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
