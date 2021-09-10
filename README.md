# asp

This [Crystal](https://crystal-lang.org/) module consists of the set of classes to modeling optimization problems 
by means of [Answer Set Programming](https://en.wikipedia.org/wiki/Answer_set_programming). We use only grounded 
rules. For definitions and basic algorithms please refer to 
an [article](https://www.mdpi.com/2076-3417/10/21/7700) and 
a [textbook](https://www.amazon.com/gp/product/0521147751/ref=dbs_a_def_rwt_hsch_vapi_tpbk_p1_i0).

## Installation

1. Add the dependency to your `shard.yml`:

   ```yaml
   dependencies:
     asp:
       github: w-wieczorek/asp
       branch: old-state
   ```

2. Run `shards install`

## Usage

```crystal
require "asp"
```

Let us solve as an example the graph kernel problem. For a given directed graph
G = (V, E), find an [independent set](https://en.wikipedia.org/wiki/Independent_set_(graph_theory))
of vertices, U, such that if v is in V - U then there is at least one u in U for which (v, u) is
in E.

```crystal
require "asp"
include Asp

prog = Program.new
graph = { vertices: (0..7).to_set,
  edges: Set{ {0, 1}, {0, 2}, {1, 2}, {2, 6}, {3, 1}, {3, 2}, {4, 0}, {4, 5} } }
taken = LiteralFactory.new graph[:vertices]
not_taken = LiteralFactory.new graph[:vertices]
graph[:vertices].each do |v|
  prog.addRule ~not_taken[v], implies: taken[v]
  prog.addRule ~taken[v], implies: not_taken[v]
  outdegree = 0
  graph[:edges].each { |u, w| outdegree += 1 if v == u }
  prog.addFact taken[v] if outdegree == 0
  if outdegree > 0
    arr = [~taken[v]]
    graph[:edges].each { |u, w| arr << ~taken[w] if v == u }
    prog.addConstraintFromArray arr
  end
end
graph[:edges].each do |u, v|
  prog.addConstraint taken[u], taken[v]
end
answer = prog.first?
if answer
  print "Kernel:"
  graph[:vertices].each { |v| print " #{v}" if answer.includes? taken[v].atom }
  puts
else
  puts "There is no kernel."
end
```

Optimization problems can be solved by associating non-negative weights with atoms. Then,
we can find an answer set that minimizes or maximizes the sum of weights.
Take the following two examples ([Maximum Clique](https://en.wikipedia.org/wiki/Clique_(graph_theory))  
and [Minimum Vertex Cover](https://en.wikipedia.org/wiki/Vertex_cover)) as illustrations.

```crystal
require "asp"
include Asp

prog = Program.new
graph = { vertices: (0..7).to_set, 
  edges: Set{ {0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 5}, 
    {1, 7}, {2, 5}, {2, 7}, {3, 4}, {3, 6}, {4, 6}, {5, 7} } }
taken = LiteralFactory.new graph[:vertices]
not_taken = LiteralFactory.new graph[:vertices]
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
if answer
  print "The clique of size #{clique_size} is:"
  graph[:vertices].each { |v| print " #{v}" if answer.includes? taken[v].atom }
  puts
end
```

```crystal
require "asp"
include Asp

prog = Program.new
graph = { vertices: (0..7).to_set, 
  edges: Set{ {0, 1}, {0, 2}, {0, 3}, {0, 6}, {1, 2}, 
    {1, 3}, {1, 5}, {1, 7}, {2, 7}, {3, 6}, {4, 6}, {5, 7} } }
taken = LiteralFactory.new graph[:vertices]
not_taken = LiteralFactory.new graph[:vertices]
graph[:vertices].each do |u|
  prog.addRule ~not_taken[u], implies: taken[u]
  prog.addRule ~taken[u], implies: not_taken[u]
  prog.associateWeight 1_i64, with: taken[u].atom
end
graph[:edges].each do |u, v|
  prog.addConstraint ~taken[u], ~taken[v]
end
answer, cover_size = prog.minimize
if answer
  print "The cover of size #{cover_size} is:"
  graph[:vertices].each { |v| print " #{v}" if answer.includes? taken[v].atom }
  puts
end
```

For more examples please see `spec` directory.

## Contributing

1. Fork it (<https://github.com/your-github-user/asp/fork>)
2. Create your feature branch (`git checkout -b my-new-feature`)
3. Commit your changes (`git commit -am 'Add some feature'`)
4. Push to the branch (`git push origin my-new-feature`)
5. Create a new Pull Request

## Contributors

- [Wojciech Wieczorek](https://github.com/w-wieczorek) - creator and maintainer
