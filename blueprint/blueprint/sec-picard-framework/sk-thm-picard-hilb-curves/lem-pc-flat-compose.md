+++
id = "lem-pc-flat-compose"
kind = "lemma"
title = "Flatness is transitive"
order = 793
uses = ["def-pc-morphism-conventions"]
+++
Let $g:X\to Y$ and $f:Y\to Z$ be flat morphisms of schemes. Then
$f\circ g$ is flat.

## Proof

Flatness is Zariski-local; on affine patches the assertion is: if
$A\to B$ and $B\to C$ are flat ring maps, then $A\to C$ is flat. For
an exact sequence $0\to M'\to M\to M''\to0$ of $A$-modules, its
base change to $B$ is exact (flatness of $B/A$) and the base change
of that to $C$ is exact (flatness of $C/B$); since
$(M\otimes_AB)\otimes_BC=M\otimes_AC$ (associativity of the tensor
product), the sequence $0\to M'\otimes_AC\to M\otimes_AC\to M''\otimes_AC\to0$ is exact: $C$ is flat over $A$.
