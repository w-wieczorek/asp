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

  class Program
    include Iterator(Set(Atom))

    getter atoms
    getter rules

    def initialize
      @solution_procedure_started = false
      @atoms = Set(Atom).new
      @rules = Set(Rule).new
      @stack = Array(Tuple(Set(Atom), Set(Atom), Atom, Symbol, Bool)).new
    end

    def addRule(*body, implies head)
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

    def addFact(head)
      raise "The head cannot be negated!" if head.negated
      raise "Cannot change model during solving!" if @solution_procedure_started
      @rules.add({head: head.atom, positives: Set(Atom).new, negatives: Set(Atom).new})
      @atoms.add(head.atom)
    end

    def addConstraint(*body)
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

    def next
      if @solution_procedure_started == false
        @solution_procedure_started = true
        lb, ub = Asp.narrow(@rules, Set(Atom).new, @atoms)
        if lb == ub
          return lb
        else
          if lb.subset_of?(ub)
            a = (ub - lb).sample
            @stack.push({lb, ub, a, [:expand, :cut_down].sample, false})
          end
        end
      end
      until @stack.empty?
        lb, ub, a, path, remove = @stack.pop
        unless remove
          @stack.push({lb.dup, ub.dup, a, path == :expand ? :cut_down : :expand, true})
        end
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
            @stack.push({lb, ub, a, [:expand, :cut_down].sample, false})
          end
        end
      end
      @solution_procedure_started = false
      stop
    end
  end
end
