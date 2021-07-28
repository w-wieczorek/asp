module Asp
  alias Atom = UInt32
  alias Rule = NamedTuple(head: Atom, positives: Set(Atom), negatives: Set(Atom))

  struct Literal
    property atom : Atom
    property negated : Bool

    def initialize(@atom, @negated)
    end

    def ~
      Literal.new(@atom, true)
    end
  end

  DUMMY = Literal.new(0_u32, false)
  
  class LiteralFactory
    @@indices = Hash({UInt64, String}, UInt32).new
    @@num_of_atoms = 1_u32  # Dummy atom (0_u32) is the first

    def initialize(range)
      u = self.object_id
      range.each do |idx|
        @@indices[{u, idx.to_s}] = @@num_of_atoms
        @@num_of_atoms += 1_u32
      end
    end

    def [](idx : Object) : Literal
      u = self.object_id
      s = idx.to_s
      i = @@indices[{u, s}]
      Literal.new(i, false)
    end

    def [](*ids) : Literal
      u = self.object_id
      s = ids.to_s
      i = @@indices[{u, s}]
      Literal.new(i, false)
    end

    def self.reset
      @@indices.clear
      @@num_of_atoms = 1_u32
    end

    def self.indices
      @@indices
    end
  end

  def self.reduct(pi : Set(Rule), x : Set(Atom)) : Set(Rule)
    result = Set(Rule).new
    pi.each do |r|
      unless x.intersects? r[:negatives] 
        result.add({head: r[:head], positives: r[:positives], negatives: Set(Atom).new})
      end
    end
    result
  end

  def self.cn(p)
    x = Set(Atom).new
    finish_loop = false
    until finish_loop
      finish_loop = true
      p.each do |r|
        if r[:positives].subset_of? x
          if x.add? r[:head]
            finish_loop = false
          end 
        end
      end
    end
    x
  end

  def self.narrow(pi, lb, ub)
    u_changed = true
    l_changed = true
    pi_u = Set(Rule).new
    pi_l = Set(Rule).new
    while u_changed || l_changed
      if u_changed
        pi_u = reduct pi, ub
      end
      if l_changed
        pi_l = reduct pi, lb
      end
      before_size = lb.size
      lb.concat(cn pi_u)
      l_changed = (lb.size != before_size)
      before_size = ub.size
      ub = ub & cn(pi_l)
      u_changed = (ub.size != before_size)
    end
    {lb, ub}
  end

  class Heap(T)
    # T is a tuple with the last element being priority
    
    def initialize
      @arr = Array(T).new(1024)
      @heap_size = 0
    end

    private def parent(i)
      i//2
    end

    private def left(i)
      2*i
    end

    private def right(i)
      2*i + 1
    end

    private def heapify(i)
      l = left(i)
      r = right(i)
      smallest = l <= @heap_size && @arr[l][-1] < @arr[i][-1] ? l : i
      smallest = r if r <= @heap_size && @arr[r][-1] < @arr[smallest][-1]
      if smallest != i
        @arr.swap(i, smallest)
        heapify(smallest)
      end
    end

    def extract : T
      m = @arr[0]
      @arr[0] = @arr[@heap_size - 1]
      @heap_size -= 1
      heapify 0
      m
    end

    def insert(el : T)
      @heap_size += 1
      if @arr.size < @heap_size
        @arr << el
      end
      i = @heap_size - 1
      while i > 0 && @arr[parent(i)][-1] > el[-1]
        @arr[i] = @arr[parent(i)]
        i = parent(i)
      end
      @arr[i] = el
    end

    def empty?
      @heap_size == 0
    end
  end

  class Program
    include Iterator(Set(Atom))

    getter atoms
    getter rules

    def initialize
      @solution_procedure_started = false
      @atoms = Set(Atom).new
      @rules = Set(Rule).new
      @heap = Heap(Tuple(Set(Atom), Set(Atom), Atom, Symbol, Int32)).new
    end

    private def _addRule(body, head)
      raise "The head cannot be negated!" if head.negated
      raise "Cannot change model during solving!" if @solution_procedure_started
      pos_set = Set(Atom).new
      neg_set = Set(Atom).new
      body.each do |literal|
        if literal.negated
          neg_set.add(literal.atom)
        else
          pos_set.add(literal.atom)
        end
      end
      @rules.add({head: head.atom, positives: pos_set, negatives: neg_set})
      @atoms.add(head.atom)
      @atoms.concat(pos_set)
      @atoms.concat(neg_set)
    end

    def addRule(*body, implies head)
      _addRule(body, head)
    end

    def addRuleFromArray(body, implies head)
      _addRule(body, head)
    end

    def addFact(head)
      raise "The head cannot be negated!" if head.negated
      raise "Cannot change model during solving!" if @solution_procedure_started
      @rules.add({head: head.atom, positives: Set(Atom).new, negatives: Set(Atom).new})
      @atoms.add(head.atom)
    end

    private def _addConstraint(body)
      raise "Cannot change model during solving!" if @solution_procedure_started
      pos_set = Set(Atom).new
      neg_set = Set(Atom).new
      body.each do |literal|
        if literal.negated
          neg_set.add(literal.atom)
        else
          pos_set.add(literal.atom)
        end
      end
      neg_set.add(DUMMY.atom)
      @rules.add({head: DUMMY.atom, positives: pos_set, negatives: neg_set})
      @atoms.concat(pos_set)
      @atoms.concat(neg_set)
    end

    def addConstraint(*body)
      _addConstraint(body)
    end

    def addConstraintFromArray(body)
      _addConstraint(body)
    end

    def next
      if @solution_procedure_started == false
        @solution_procedure_started = true
        lb, ub = Asp.narrow(@rules, Set(Atom).new, @atoms)
        if lb == ub
          return lb
        else
          if lb.subset_of?(ub)
            a = (ub - lb).sample
            @heap.insert({lb.dup, ub.dup, a, :cut_down, ub.size - lb.size})
            @heap.insert({lb, ub, a, :expand, ub.size - lb.size})
          end
        end
      end
      until @heap.empty?
        lb, ub, a, path, priority = @heap.extract
        case path
        when :expand
          lb.add a
        when :cut_down
          ub.delete a
        end 
        lb, ub = Asp.narrow(@rules, lb, ub)
        if lb == ub
          return lb
        else
          if lb.subset_of?(ub)
            a = (ub - lb).sample
            @heap.insert({lb.dup, ub.dup, a, :cut_down, ub.size - lb.size})
            @heap.insert({lb, ub, a, :expand, ub.size - lb.size})
          end
        end
      end
      @solution_procedure_started = false
      stop
    end
  end
end
