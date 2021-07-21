module Asp
  alias AtomId = Tuple(UInt64, UInt64)
  alias Literal = NamedTuple(atom: AtomId, negated : Bool)
  alias Rule = NamedTuple(head: Literal, body: Set(Literal))

  class Atom
    def initialize(@indices : Enumerable(U)) forall U
    end

    def []=(head, *body) : Rule
    end

    def [](idx)
      {self.object_id, idx.hash}
    end
  end

  class Rule
  end

  class Program
    include Iterator(Set(AtomId))

    def initialize
      @solution_procedure_started = false
    end

    def next
      @solution_procedure_started = true
    end
  end
end
