module Asp
  alias Atom = UInt64
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

  EMPTY = Set(Atom).new
  DUMMY = Literal.new(0_u64, false)
  
  class LiteralFactory
    property indices : Array(UInt64)

    def initialize(range : Range(Int32, Int32))
      @indices = range.to_a.map &.hash
      @indices.uniq!
      if @indices.size < range.size
        raise RuntimeError.new("Inefficient hash function for class Int32.")
      end
    end

    def initialize(range : Array(T)) forall T
      @indices = range.map &.hash
      @indices.uniq!
      if @indices.size < range.size
        raise RuntimeError.new("Inefficient hash function for class #{T.name}.")
      end
    end

    def initialize(range : Set(T)) forall T
      @indices = range.to_a.map &.hash
      @indices.uniq!
      if @indices.size < range.size
        raise RuntimeError.new("Inefficient hash function for class #{T.name}.")
      end
    end

    def [](idx : Object) : Literal
      x0 = self.object_id.to_u128
      x1 = idx.hash.to_u128
      v = (x0 * 4029721224409075548 + x1 * 5440965862096952843) % 18446744073709551557
      Literal.new(v.to_u64, false)
    end
  end

  def self.reduct(pi : Set(Rule), x : Set(Atom)) : Set(Rule)
    result = Set(Rule).new
    pi.each do |r|
      unless x.intersects? r[:negatives] 
        result.add({head: r[:head], positives: r[:positives], negatives: EMPTY})
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
      @stack = Array(NamedTuple(ub: Set(Atom), lb: Set(Atom), a: Atom, path: Symbol, remove: Bool)).new
    end

    def addRule(*body, implies head)
      raise ArgumentError.new("The head cannot be negated!") if head.negated
      raise RuntimeError.new("Cannot change model during solving!") if @solution_procedure_started
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
      raise ArgumentError.new("The head cannot be negated!") if head.negated
      raise RuntimeError.new("Cannot change model during solving!") if @solution_procedure_started
      @rules.add({head: head.atom, positives: EMPTY, negatives: EMPTY})
      @atoms.add(head.atom)
    end

    def addConstraint(*body)
      raise RuntimeError.new("Cannot change model during solving!") if @solution_procedure_started
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
      end
        
      Stop
      
    end
  end
end
