module Asp
  alias AtomId = Tuple(UInt64, UInt64)
  alias Rule = NamedTuple(head: AtomId?, positives: Set(AtomId), negatives: Set(AtomId))

  struct Literal
    property atom : AtomId
    property negated : Bool

    def initialize(@atom, @negated)
    end

    def ~
      Literal.new(@atom, true)
    end
  end

  class Atom
    property indices : Array(UInt64)

    def initialize(range : Range(Int32, Int32))
      @indices = range.to_a.map &.hash
    end

    def initialize(range : Array(T)) forall T
      @indices = range.to_a.map &.hash
    end

    def initialize(range : Set(T)) forall T
      @indices = range.to_a.map &.hash
    end

    def [](idx : Object) : Literal
      Literal.new({self.object_id, idx.hash}, false)
    end
  end

  class Program
    include Iterator(Set(AtomId))

    getter atoms
    getter rules

    def initialize
      @solution_procedure_started = false
      @atoms = Set(AtomId).new
      @rules = Set(Rule).new
    end

    def addRule(*body, implies head)
      raise ArgumentError.new("The head cannot be negated!") if head.negated
      pos_set = Set(AtomId).new
      neg_set = Set(AtomId).new
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

    def next
      if !@solution_procedure_started
        @solution_procedure_started = true
        Set(AtomId).new
      else
        Stop
      end
    end
  end
end
