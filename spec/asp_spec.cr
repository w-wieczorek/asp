require "spec"
require "../src/asp.cr"

describe Asp do
  it "creates a rule and adds it to a logic program" do
    model = Asp::Program.new
    p = Asp::Atom.new (0..3)
    model.addRule p[1], ~p[2], ~p[3], implies: p[0]
    model.atoms.should eq(Set{p[0].atom, p[1].atom, p[2].atom, p[3].atom})
    model.rules.size.should eq(1)
    model.rules.should contain({head: p[0].atom, positives: Set{p[1].atom}, negatives: Set{p[2].atom, p[3].atom}})
  end
end
