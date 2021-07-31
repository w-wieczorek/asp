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

    def clear
      @heap_size = 0
    end

    def empty?
      @heap_size == 0
    end
  end

  class Program
    include Iterator(Set(Atom))

    getter atoms, rules, level

    def initialize
      @solution_procedure_started = false
      @atoms = Set(Atom).new
      @rules = Set(Rule).new
      @heap = Heap(Tuple(Set(Atom), Set(Atom), Int64)).new
      @level = {} of Atom => Int32
      proc = ->(hash : Hash(Atom, Int64), key : Atom) { hash[key] = 0_i64 }
      @weight = Hash(Atom, Int64).new(proc)
    end

    def determineDependences
      dependences = Set({Atom, Atom}).new
      @atoms.each { |a| dependences.add({a, a}) }
      @rules.each do |r|
        r[:positives].each { |b| dependences.add({r[:head], b}) }
        r[:negatives].each { |b| dependences.add({r[:head], b}) }
      end
      finish_loop = false
      new_pairs = [] of {Atom, Atom}
      until finish_loop
        finish_loop = true
        @atoms.each do |a|
          dependences.each do |c, b|
            if dependences.includes?({a, c}) && !dependences.includes?({a, b})
              new_pairs << {a, b}
              finish_loop = false
            end 
          end
        end
        dependences.concat new_pairs unless finish_loop
        new_pairs.clear
      end
      dependences
    end

    def determineLevels
      @level.clear
      dependences = determineDependences
      partition = [] of Set(Atom)
      eq_class = {} of Atom => Set(Atom)
      @atoms.each { |a| eq_class[a] = Set{a} }
      dependences.each do |a, b|
        if a != b && dependences.includes?({b, a}) && !eq_class[a].same?(eq_class[b])
          eq_class[a].concat eq_class[b]
          eq_class[b] = eq_class[a]
        end
      end
      partition = eq_class.values.uniq
      less_than = Set({Set(Atom), Set(Atom)}).new
      n = partition.size
      (0...n).each do |i|
        (0...n).each do |j|
          if i != j
            partition[i].each do |p|
              partition[j].each do |q|
                less_than.add({partition[i], partition[j]}) if dependences.includes?({q, p})
              end
            end
          end
        end
      end
      level_of_eq_class = {} of Set(Atom) => Int32
      (0...n).each { |i| level_of_eq_class[partition[i]] = 0 }
      current_level = 0
      until (n = partition.size) == 0
        (0...n).each do |i|
          (0...n).each do |j|
            if i != j && less_than.includes?({partition[i], partition[j]})
              level_of_eq_class[partition[j]] = current_level + 1
            end
          end
        end
        partition.reject! { |eqc| level_of_eq_class[eqc] == current_level }
        current_level += 1
      end
      level_of_eq_class.each do |eqc, lev|
        eqc.each { |a| @level[a] = lev }
      end
    end

    def associateWeight(w : Int64, with atom)
      raise "Cannot change model during solving!" if @solution_procedure_started
      raise "Weight cannot be negative!" if w < 0_i64
      @weight[atom] = w
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

    private def heuristicSelection(soa : Set(Atom))
      soa.min_by { |a| @level[a] }
    end

    def next
      if @solution_procedure_started == false
        @solution_procedure_started = true
        determineLevels
        @heap.clear
        @heap.insert({Set(Atom).new, @atoms, @atoms.size.to_i64})
      end
      until @heap.empty?
        lb, ub, priority = @heap.extract
        lb, ub = Asp.narrow(@rules, lb, ub)
        if lb == ub
          return lb
        else
          if lb.subset_of?(ub)
            a = heuristicSelection(ub - lb)
            @heap.insert({lb, ub - Set{a}, (ub.size - lb.size - 1).to_i64})
            @heap.insert({lb | Set{a}, ub, (ub.size - lb.size - 1).to_i64})
          end
        end
      end
      @solution_procedure_started = false
      stop
    end

    private def eval(soa : Set(Atom)) : Int64
      soa.sum(0_i64) { |a| @weight[a] }
    end

    def minimize
      @solution_procedure_started = true
      determineLevels
      best_weight = Int64::MAX
      best_answer : Set(Atom)? = nil
      @heap.clear
      @heap.insert({Set(Atom).new, @atoms, 0_i64})
      until @heap.empty?
        lb, ub, lb_eval = @heap.extract
        next if lb_eval >= best_weight
        lb, ub = Asp.narrow(@rules, lb, ub)
        if lb == ub
          if (lb_eval = eval(lb)) < best_weight
            best_answer = lb
            best_weight = lb_eval
          end
        else
          if lb.subset_of?(ub)
            a = heuristicSelection(ub - lb)
            lb_eval = eval(lb)
            @heap.insert({lb, ub - Set{a}, lb_eval})
            @heap.insert({lb | Set{a}, ub, lb_eval + @weight[a]})
          end
        end
      end
      @solution_procedure_started = false
      {best_answer, best_weight}
    end

    def maximize
      @solution_procedure_started = true
      determineLevels
      best_weight = Int64::MIN
      best_answer : Set(Atom)? = nil
      @heap.clear
      @heap.insert({Set(Atom).new, @atoms, 0_i64})
      until @heap.empty?
        lb, ub, ub_eval = @heap.extract
        next if -ub_eval <= best_weight
        lb, ub = Asp.narrow(@rules, lb, ub)
        if lb == ub
          if (ub_eval = eval(ub)) > best_weight
            best_answer = ub
            best_weight = ub_eval
          end
        else
          if lb.subset_of?(ub)
            a = heuristicSelection(ub - lb)
            ub_eval = eval(ub)
            @heap.insert({lb, ub - Set{a}, -ub_eval})
            @heap.insert({lb | Set{a}, ub, -ub_eval - @weight[a]})
          end
        end
      end
      @solution_procedure_started = false
      {best_answer, best_weight}
    end
  end
end
