+++
id = "def-kun-separably-closed"
kind = "definition"
title = "Separably closed fields"
order = 989
lean = ["IsSepClosed"]
uses = ["def-weil-pbc-scheme-conventions"]
+++
A field $K$ is *separably closed* if it admits no nontrivial
finite separable extension. A *separable closure* of a field
$K$ is a separable algebraic extension $K^{\mathrm{sep}}/K$ whose
top field is separably closed.

*Implementation note.* Mathlib's `IsSepClosed K` is stated as "every separable
polynomial over $K$ splits", which is equivalent to the formulation above. The
picard-schemes chapter defines the same notion again in that polynomial form, as
[def-pc-separably-closed].
