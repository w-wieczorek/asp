module Asp
  alias Atom = Tuple(UInt64, UInt64)
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
  DUMMY = Literal.new({0_u64, 0_u64}, false)
  
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
      Literal.new({self.object_id, idx.hash}, false)
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
      if !@solution_procedure_started
        @solution_procedure_started = true
        Set(Atom).new
      else
        Stop
      end
    end
  end

  def reduct(pi : Set(Rule), x : Set(Atom)) : Set(Rule)
    result = Set(Rule).new
    pi.each do |r|
      unless x.intersects? r[:negatives] 
        result.add({head: r[:head], positives: r[:positives], negatives: EMPTY})
      end
    end
    result
  end
end
