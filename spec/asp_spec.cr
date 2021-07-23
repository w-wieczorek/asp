require "spec"
require "../src/asp.cr"

describe Asp do
  it "creates a rule and adds it to a logic program" do
    model = Asp::Program.new
    p = Asp::LiteralFactory.new (0..3)
    model.addRule p[1], ~p[2], ~p[3], implies: p[0]
    model.atoms.should eq(Set{p[0].atom, p[1].atom, p[2].atom, p[3].atom})
    model.rules.size.should eq(1)
    model.rules.should contain({head: p[0].atom, positives: Set{p[1].atom}, 
      negatives: Set{p[2].atom, p[3].atom}})
  end

  it "adds facts and constraints to a logic program" do
    model = Asp::Program.new
    idx_arr = (0..2).zip ["Ala", "Ewa", "Adam"]
    person = Asp::LiteralFactory.new idx_arr
    model.addFact person[{0, "Ala"}]
    model.addConstraint person[{1, "Ewa"}], ~person[{2, "Adam"}]
    model.atoms.should eq(Set{person[{0, "Ala"}].atom, person[{1, "Ewa"}].atom, 
      person[{2, "Adam"}].atom, Asp::DUMMY.atom})
    model.rules.size.should eq(2)
    r1 = {head: person[{0, "Ala"}].atom, positives: Asp::EMPTY, 
      negatives: Asp::EMPTY}
    model.rules.should contain(r1)
    r2 = {head: Asp::DUMMY.atom, positives: Set{person[{1, "Ewa"}].atom}, 
      negatives: Set{person[{2, "Adam"}].atom, Asp::DUMMY.atom}}
    model.rules.should contain(r2)
  end

  it "computes reduct" do
    model = Asp::Program.new
    idx_arr = [:a, :b]
    idx_arr2 = idx_arr.each_repeated_combination.to_a.map{ |pair| Tuple(Symbol, Symbol).from pair }
    el = Asp::LiteralFactory.new idx_arr
    equal = Asp::LiteralFactory.new idx_arr2
    neq = Asp::LiteralFactory.new idx_arr2
    idx_arr.each do |i|
      model.addFact el[i]
      model.addRule el[i], implies: equal[{i, i}]
      idx_arr.each do |j|
        model.addRule el[i], el[j], ~equal[{i, j}], implies: neq[{i, j}]
      end
    end
    expected = Set(Asp::Rule).new
    expected.add({head: el[:a].atom, positives: Asp::EMPTY, negatives: Asp::EMPTY})
    expected.add({head: el[:b].atom, positives: Asp::EMPTY, negatives: Asp::EMPTY})
    expected.add({head: equal[{:a, :a}].atom, positives: Set{el[:a].atom}, negatives: Asp::EMPTY})
    expected.add({head: equal[{:b, :b}].atom, positives: Set{el[:b].atom}, negatives: Asp::EMPTY})
    expected.add({head: neq[{:a, :b}].atom, positives: Set{el[:a].atom, el[:b].atom}, negatives: Asp::EMPTY})
    expected.add({head: neq[{:b, :a}].atom, positives: Set{el[:a].atom, el[:b].atom}, negatives: Asp::EMPTY})
    x = Set{equal[{:a, :a}].atom, equal[{:b, :b}].atom, el[:a].atom, el[:b].atom, neq[{:a, :b}].atom, neq[{:b, :a}].atom}
    computed = Asp.reduct(model.rules, x)
    computed.should eq(expected)
  end

  it "determines the smallest model of a positive program" do
    prog = Asp::Program.new
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
    q = Asp::LiteralFactory.new (1..6)
    prog.addFact q[1]
    prog.addRule ~q[1], implies: q[2]
    prog.addRule q[1], ~q[4], implies: q[3]
    prog.addRule ~q[3], ~q[5], implies: q[4]
    prog.addRule q[2], ~q[6], implies: q[5]
    prog.addRule q[5], implies: q[5]
    p0 = Asp.reduct prog.rules, Asp::EMPTY
    p6 = Asp.reduct prog.rules, Set{q[1].atom, q[2].atom, q[3].atom, q[4].atom, q[5].atom, q[6].atom}
    expected0 = Set{q[1].atom, q[2].atom, q[3].atom, q[4].atom, q[5].atom}
    expected6 = Set{q[1].atom}
    computed0 = Asp.cn p0
    computed6 = Asp.cn p6
    computed0.should eq(expected0)
    computed6.should eq(expected6)
  end
end
