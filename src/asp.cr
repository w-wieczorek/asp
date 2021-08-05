module Asp
  alias Atom = UInt32
  alias Rule = NamedTuple(head: Atom, positives: Set(Atom), negatives: Set(Atom))
  alias Graph = Array(Tuple(Atom, Atom))

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
    getter atoms, rules

    def initialize
      @atoms = Set(Atom).new
      @arr_of_atoms = [] of Atom
      @s_set = Array(Atom).new
      @g_set = Graph.new
      @stack = Array(Tuple(Int32, Int32, Int32, Int32)).new
      @rules = Set(Rule).new
      @num_of_rules = Hash(Atom, Int32).new(0)
      proc = ->(hash : Hash(Atom, Int64), key : Atom) { hash[key] = 0_i64 }
      @weight = Hash(Atom, Int64).new(proc)
    end

    def associateWeight(w : Int64, with atom)
      raise "Weight cannot be negative!" if w < 0_i64
      @weight[atom] = w
    end

    private def _addRule(body, head)
      raise "The head cannot be negated!" if head.negated
      pos_set = Set(Atom).new
      neg_set = Set(Atom).new
      body.each do |literal|
        if literal.negated
          neg_set.add(literal.atom)
        else
          pos_set.add(literal.atom)
        end
      end
      if @rules.add?({head: head.atom, positives: pos_set, negatives: neg_set})
        @atoms.add(head.atom)
        @atoms.concat(pos_set)
        @atoms.concat(neg_set)
        if @num_of_rules.has_key? head.atom
          @num_of_rules[head.atom] += 1
        else
          @num_of_rules[head.atom] = 1
        end
      end
    end

    def addRule(*body, implies head)
      _addRule(body, head)
    end

    def addRuleFromArray(body, implies head)
      _addRule(body, head)
    end

    def addFact(head)
      _addRule([] of Literal, head)
    end

    private def _addConstraint(body)
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

    private def put(elem : U, arr : Array(U), at idx) forall U
      if arr.size > idx
        arr[idx] = elem
      else
        arr << elem
      end
    end

    def satisfies?(context : Set(Atom), rule : Rule)
      return true if context.intersects? rule[:negatives]
      if context.superset_of? rule[:positives]
        context.includes? rule[:head]
      else
        true
      end
    end

    private def find_nth_rule(idx, atom) : Rule
      counter = 0
      @rules.each do |r|
        if r[:head] == atom
          counter += 1
          return r if counter == idx
        end
      end
      raise "Connot find #{idx}th rule!"
    end

    def answer?(context : Set(Atom))
      red = Asp.reduct(@rules, context)
      x = Asp.cn(red)
      context == x
    end

    private def dfs(g, len, s)
      dist = Hash(Atom, Float32).new(Float32::INFINITY)
      dist[s] = 0_f32
      q = Deque{s}
      until q.empty?
        u = q.shift
        (0...len).each do |i|
          w, v = g[i]
          if u == w && dist[v] == Float32::INFINITY
            q.push v
            dist[v] = dist[u] + 1_f32
          end
        end
      end
      dist
    end

    def add_to_graph?(len : Int32, head : Atom, pos : Set(Atom))
      pos.each do |a|
        dist = dfs @g_set, len, head
        if dist[a] < Float32::INFINITY
          return false
        else
          put({a, head}, @g_set, len)
          len += 1
        end
      end
      true
    end

    def solve
      s_len = 0
      @stack.clear
      @rules.each do |r|
        if r[:positives].empty? && r[:negatives].empty?
          put r[:head], @s_set, at: s_len
          s_len += 1
        end
      end
      @arr_of_atoms = @atoms.to_a
      @stack.push({0, 0, 1, s_len})
      until @stack.empty?
        a_idx, g_len, r_idx, s_len = @stack.pop
        if r_idx == 1 && a_idx + 1 < @arr_of_atoms.size
          @stack.push({a_idx + 1, g_len, 1, s_len})
        end
        context = Slice.new(@s_set.to_unsafe, s_len).to_set
        if answer?(context)
          return context
        end
        continue_loop = true
        while continue_loop && a_idx < @arr_of_atoms.size
          a = @arr_of_atoms[a_idx]
          unless context.includes?(a)
            while continue_loop && r_idx <= @num_of_rules[a]
              r = find_nth_rule(r_idx, a)
              if !r[:negatives].includes?(a) && !context.intersects?(r[:negatives]) && add_to_graph?(g_len, a, r[:positives])
                @stack.push({a_idx, g_len, r_idx + 1, s_len})
                g_len += r[:positives].size
                put a, @s_set, at: s_len
                s_len += 1
                r[:positives].each do |b|
                  put b, @s_set, at: s_len
                  s_len += 1
                end
                continue_loop = false
                @stack.push({a_idx + 1, g_len, 1, s_len})
              end
              r_idx += 1
            end
          end
          a_idx += 1
        end
      end
    end

    private def eval(soa : Set(Atom)) : Int64
      soa.sum(0_i64) { |a| @weight[a] }
    end
  end
end
