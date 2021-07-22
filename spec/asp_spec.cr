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
    names = ["Ala", "Ewa", "Adam"]
    idx_arr = Array({Int32, String}).new(3) { |i| {i, names[i]} }
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
    idx_arr2 = Array(Symbol).new(4)
    idx.arr.each do |i|
      idx_arr.each { |j| idx_arr2 << {i, j} }
    end
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
    expected = Set(Rule).new
    expected.add({head: el[:a].atom, positives: Asp::EMPTY, negatives: Asp::EMPTY})
    expected.add({head: el[:b].atom, positives: Asp::EMPTY, negatives: Asp::EMPTY})
    expected.add({head: equal[{:a, :a}].atom, positives: Set{el[:a].atom}, negatives: Asp::EMPTY})
    expected.add({head: equal[{:b, :b}].atom, positives: Set{el[:b].atom}, negatives: Asp::EMPTY})
  end
end
