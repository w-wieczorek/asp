require "spec"
require "../src/asp.cr"

describe Asp do
  it "creates a rule and adds it to a logic program" do
    prog = Asp::Program.new
    p = Asp::LiteralFactory.new (0..3)
    prog.addRule p[1], ~p[2], ~p[3], implies: p[0]
    prog.atoms.should eq(Set{p[0].atom, p[1].atom, p[2].atom, p[3].atom})
    prog.rules.size.should eq(1)
    prog.rules.should contain({head: p[0].atom, positives: Set{p[1].atom}, 
      negatives: Set{p[2].atom, p[3].atom}})
  end

  it "adds facts and constraints to a logic program" do
    prog = Asp::Program.new
    idx_arr = (0..2).zip ["Ala", "Grażyna", "Adam"]
    Asp::LiteralFactory.reset
    person = Asp::LiteralFactory.new idx_arr
    prog.addFact person[0, "Ala"]
    prog.addConstraint person[1, "Grażyna"], ~person[2, "Adam"]
    prog.atoms.should eq(Set{person[0, "Ala"].atom, person[1, "Grażyna"].atom, 
      person[2, "Adam"].atom, Asp::DUMMY.atom})
    prog.rules.size.should eq(2)
    r1 = {head: person[0, "Ala"].atom, positives: Set(Asp::Atom).new, 
      negatives: Set(Asp::Atom).new}
    prog.rules.should contain(r1)
    r2 = {head: Asp::DUMMY.atom, positives: Set{person[1, "Grażyna"].atom}, 
      negatives: Set{person[2, "Adam"].atom, Asp::DUMMY.atom}}
    prog.rules.should contain(r2)
  end

  it "computes reduct" do
    prog = Asp::Program.new
    idx_arr = [:a, :b]
    idx_arr2 = [] of {Symbol, Symbol}
    idx_arr.each_repeated_permutation { |pair| idx_arr2 << Tuple(Symbol, Symbol).from pair }
    Asp::LiteralFactory.reset
    el = Asp::LiteralFactory.new idx_arr
    equal = Asp::LiteralFactory.new idx_arr2
    neq = Asp::LiteralFactory.new idx_arr2
    idx_arr.each do |i|
      prog.addFact el[i]
      prog.addRule el[i], implies: equal[i, i]
      idx_arr.each do |j|
        prog.addRule el[i], el[j], ~equal[i, j], implies: neq[i, j]
      end
    end
    expected = Set(Asp::Rule).new
    expected.add({head: el[:a].atom, positives: Set(Asp::Atom).new, negatives: Set(Asp::Atom).new})
    expected.add({head: el[:b].atom, positives: Set(Asp::Atom).new, negatives: Set(Asp::Atom).new})
    expected.add({head: equal[:a, :a].atom, positives: Set{el[:a].atom}, negatives: Set(Asp::Atom).new})
    expected.add({head: equal[:b, :b].atom, positives: Set{el[:b].atom}, negatives: Set(Asp::Atom).new})
    expected.add({head: neq[:a, :b].atom, positives: Set{el[:a].atom, el[:b].atom}, negatives: Set(Asp::Atom).new})
    expected.add({head: neq[:b, :a].atom, positives: Set{el[:a].atom, el[:b].atom}, negatives: Set(Asp::Atom).new})
    x = Set{equal[:a, :a].atom, equal[:b, :b].atom, el[:a].atom, el[:b].atom, neq[:a, :b].atom, neq[:b, :a].atom}
    computed = Asp.reduct(prog.rules, x)
    computed.should eq(expected)
  end

  it "determines the smallest model of a positive program" do
    prog = Asp::Program.new
    Asp::LiteralFactory.reset
    q = Asp::LiteralFactory.new (1..6)
    prog.addFact q[1]
    prog.addRule q[1], implies: q[2]
    prog.addRule q[1], q[2], implies: q[3]
    prog.addRule q[6], implies: q[5]
    expected = Set{q[1].atom, q[2].atom, q[3].atom}
    computed = Asp.cn(prog.rules)
    computed.should eq(expected)
  end

  it "computes reduct and cn on it" do
    prog = Asp::Program.new
    Asp::LiteralFactory.reset
    q = Asp::LiteralFactory.new (1..6)
    prog.addFact q[1]
    prog.addRule ~q[1], implies: q[2]
    prog.addRule q[1], ~q[4], implies: q[3]
    prog.addRule ~q[3], ~q[5], implies: q[4]
    prog.addRule q[2], ~q[6], implies: q[5]
    prog.addRule q[5], implies: q[5]
    p0 = Asp.reduct prog.rules, Set(Asp::Atom).new
    p6 = Asp.reduct prog.rules, Set{q[1].atom, q[2].atom, q[3].atom, q[4].atom, q[5].atom, q[6].atom}
    expected0 = Set{q[1].atom, q[2].atom, q[3].atom, q[4].atom, q[5].atom}
    expected6 = Set{q[1].atom}
    computed0 = Asp.cn p0
    computed6 = Asp.cn p6
    computed0.should eq(expected0)
    computed6.should eq(expected6)
  end

  it "computes answer sets for a simple program 1" do
    prog = Asp::Program.new
    Asp::LiteralFactory.reset
    a = Asp::LiteralFactory.new [0]
    prog.addRule a[0], implies: a[0]
    prog.solve.should eq(Set(Asp::Atom).new)
  end

  it "computes answer sets for a simple program 2" do
    prog = Asp::Program.new
    Asp::LiteralFactory.reset
    a = Asp::LiteralFactory.new [0, 1]
    prog.addRule ~a[1], implies: a[0]
    prog.solve.should eq(Set{a[0].atom})
  end

  it "computes answer sets for a simple program 3" do
    prog = Asp::Program.new
    Asp::LiteralFactory.reset
    a = Asp::LiteralFactory.new [0]
    prog.addRule ~a[0], implies: a[0]
    prog.solve.should be_nil
  end

  it "computes answer sets for a simple program 4" do
    prog = Asp::Program.new
    Asp::LiteralFactory.reset
    a = Asp::LiteralFactory.new [0, 1]
    prog.addRule ~a[1], implies: a[0]
    prog.addRule ~a[0], implies: a[1]
    prog.addConstraint a[1]
    result = prog.solve
    result.should eq(Set{a[0].atom})
  end

  it "computes answer sets for a simple program 5" do
    prog = Asp::Program.new
    Asp::LiteralFactory.reset
    a = Asp::LiteralFactory.new (1..5)
    prog.addRule a[2], a[3], ~a[4], ~a[5], implies: a[1]
    prog.addRule ~a[3], implies: a[2]
    prog.addRule a[1], a[4], implies: a[3]
    prog.addConstraint a[4], ~a[5]
    prog.addFact a[5]
    result = prog.solve
    result.should eq(Set{a[2].atom, a[5].atom})
  end

  it "solves a combinatorial problem (Hamiltonian Cycle)" do
    prog = Asp::Program.new
    Asp::LiteralFactory.reset
    graph = { vertices: Set{0, 1, 2}, edges: Set{ {0, 1}, {1, 2}, {2, 0} } }
    taken = Asp::LiteralFactory.new graph[:edges]
    not_taken = Asp::LiteralFactory.new graph[:edges]
    reachable = Asp::LiteralFactory.new graph[:vertices]
    graph[:edges].each do |u, v|
      prog.addRule ~not_taken[u, v], implies: taken[u, v]
      prog.addRule ~taken[u, v], implies: not_taken[u, v]
    end
    graph[:vertices].each do |v|
      prog.addRule taken[0, v], implies: reachable[v] if graph[:edges].includes?({0, v})
      graph[:vertices].each do |u| 
        prog.addRule reachable[u], taken[u, v], implies: reachable[v] if graph[:edges].includes?({u, v})
      end
      prog.addConstraint ~reachable[v]
    end
    graph[:edges].each do |u1, v1|
      graph[:edges].each do |u2, v2|
        if (v1 == v2 && u1 != u2) || (u1 == u2 && v1 != v2)
          prog.addConstraint taken[u1, v1], taken[u2, v2]
        end
      end
    end
    result = prog.solve
    result.should be_truthy
    result.as(Set(Asp::Atom)).should contain(taken[0, 1].atom)
    result.as(Set(Asp::Atom)).should contain(taken[1, 2].atom)
    result.as(Set(Asp::Atom)).should contain(taken[2, 0].atom)
  end

  it "solves a combinatorial problem (Graph Coloring)" do
    prog = Asp::Program.new
    Asp::LiteralFactory.reset
    graph = { vertices: Set{0, 1, 2, 3, 4}, 
      edges: Set{ {0, 1}, {0, 3}, {0, 4}, {1, 2}, {2, 3}, {3, 4} } }
    cs = [:red, :green, :blue]
    pairs = [] of {Int32, Symbol}
    graph[:vertices].each { |v| cs.each { |c| pairs << {v, c} } }
    color = Asp::LiteralFactory.new pairs
    other_color = Asp::LiteralFactory.new pairs
    has_color = Asp::LiteralFactory.new graph[:vertices]
    graph[:vertices].each do |v|
      cs.each do |c| 
        prog.addRule ~other_color[v, c], implies: color[v, c] 
        prog.addRule ~color[v, c], implies: other_color[v, c] 
        prog.addRule color[v, c], implies: has_color[v]
        cs.each { |c2| prog.addConstraint color[v, c], color[v, c2] unless c == c2 }
      end
      prog.addConstraint ~has_color[v]
    end
    graph[:edges].each do |v, u|
      cs.each { |c| prog.addConstraint color[v, c], color[u, c] }
    end
    prog.addFact color[0, :red]
    prog.addFact color[1, :blue]
    prog.addFact color[3, :green]
    result = prog.solve
    result.should be_truthy
    result.as(Set(Asp::Atom)).should contain(color[2, :red].atom)
    result.as(Set(Asp::Atom)).should contain(color[4, :blue].atom)
  end

  pending "solves a combinatorial problem (Kernel)" do
    prog = Asp::Program.new
    Asp::LiteralFactory.reset
    graph = { vertices: Set{0, 1, 2, 3, 4, 5, 6, 7}, 
      edges: Set{ {0, 1}, {0, 2}, {1, 2}, {2, 6}, {3, 1}, {3, 2}, {4, 0}, {4, 5} } }
    taken = Asp::LiteralFactory.new graph[:vertices]
    not_taken = Asp::LiteralFactory.new graph[:vertices]
    outdegree = {} of Int32 => Int32
    graph[:vertices].each do |v|
      prog.addRule ~not_taken[v], implies: taken[v]
      prog.addRule ~taken[v], implies: not_taken[v]
      outdegree[v] = 0
      graph[:edges].each { |u, w| outdegree[v] += 1 if v == u }
      prog.addFact taken[v] if outdegree[v] == 0
      if outdegree[v] > 0
        arr = [~taken[v]]
        graph[:edges].each { |u, w| arr << ~taken[w] if v == u }
        prog.addConstraintFromArray arr
      end
    end
    graph[:edges].each do |u, v|
      prog.addConstraint taken[u], taken[v]
    end
    result = prog.solve
    result.should be_truthy
    result.as(Set(Asp::Atom)).should contain(taken[1].atom)
    result.as(Set(Asp::Atom)).should contain(taken[5].atom)
    result.as(Set(Asp::Atom)).should contain(taken[6].atom)
    result.as(Set(Asp::Atom)).should contain(taken[7].atom)
    result.as(Set(Asp::Atom)).should contain(not_taken[0].atom)
    result.as(Set(Asp::Atom)).should contain(not_taken[2].atom)
    result.as(Set(Asp::Atom)).should contain(not_taken[3].atom)
    result.as(Set(Asp::Atom)).should contain(not_taken[4].atom)
  end

  pending "solves a combinatorial optimization problem (Maximum Clique)" do
    prog = Asp::Program.new
    Asp::LiteralFactory.reset
    graph = { vertices: (0..7).to_set, 
      edges: Set{ {0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 5}, 
        {1, 7}, {2, 5}, {2, 7}, {3, 4}, {3, 6}, {4, 6}, {5, 7} } }
    taken = Asp::LiteralFactory.new graph[:vertices]
    not_taken = Asp::LiteralFactory.new graph[:vertices]
    graph[:vertices].each do |u|
      prog.addRule ~not_taken[u], implies: taken[u]
      prog.addRule ~taken[u], implies: not_taken[u]
      prog.associateWeight 1_i64, with: taken[u].atom
      graph[:vertices].each do |v|
        if u < v && !graph[:edges].includes?({u, v})
          prog.addConstraint taken[u], taken[v]
        end
      end
    end
    answer, clique_size = prog.maximize
    answer.should be_truthy
    clique_size.should eq(4_i64)
    answer.as(Set(Asp::Atom)).should contain(taken[1].atom)
    answer.as(Set(Asp::Atom)).should contain(taken[2].atom)
    answer.as(Set(Asp::Atom)).should contain(taken[5].atom)
    answer.as(Set(Asp::Atom)).should contain(taken[7].atom)
    answer.as(Set(Asp::Atom)).should contain(not_taken[0].atom)
    answer.as(Set(Asp::Atom)).should contain(not_taken[3].atom)
    answer.as(Set(Asp::Atom)).should contain(not_taken[4].atom)
    answer.as(Set(Asp::Atom)).should contain(not_taken[6].atom)
  end

  pending "solves a combinatorial optimization problem (Minimum Vertex Cover)" do
    prog = Asp::Program.new
    Asp::LiteralFactory.reset
    graph = { vertices: (0..7).to_set, 
      edges: Set{ {0, 1}, {0, 2}, {0, 3}, {0, 6}, {1, 2}, 
        {1, 3}, {1, 5}, {1, 7}, {2, 7}, {3, 6}, {4, 6}, {5, 7} } }
    taken = Asp::LiteralFactory.new graph[:vertices]
    not_taken = Asp::LiteralFactory.new graph[:vertices]
    graph[:vertices].each do |u|
      prog.addRule ~not_taken[u], implies: taken[u]
      prog.addRule ~taken[u], implies: not_taken[u]
      prog.associateWeight 1_i64, with: taken[u].atom
    end
    graph[:edges].each do |u, v|
      prog.addConstraint ~taken[u], ~taken[v]
    end
    answer, cover_size = prog.minimize
    answer.should be_truthy
    cover_size.should eq(4_i64)
    answer.as(Set(Asp::Atom)).should contain(taken[0].atom)
    answer.as(Set(Asp::Atom)).should contain(taken[1].atom)
    answer.as(Set(Asp::Atom)).should contain(taken[6].atom)
    answer.as(Set(Asp::Atom)).should contain(taken[7].atom)
    answer.as(Set(Asp::Atom)).should contain(not_taken[2].atom)
    answer.as(Set(Asp::Atom)).should contain(not_taken[3].atom)
    answer.as(Set(Asp::Atom)).should contain(not_taken[4].atom)
    answer.as(Set(Asp::Atom)).should contain(not_taken[5].atom)
  end
end
