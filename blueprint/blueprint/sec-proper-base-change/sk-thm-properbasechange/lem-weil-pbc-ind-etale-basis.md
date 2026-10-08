+++
id = "lem-weil-pbc-ind-etale-basis"
kind = "lemma"
title = "The ind-etale subsite is a basis"
order = 1279
uses = ["def-weil-pbc-ind-etale-basis", "def-weil-pbc-proetale-site", "lem-weil-pbc-ind-etale-stability", "thm-weil-pbc-weak-etale-refinement"]
+++
Every pro-etale object over an affine $X$ has a cover by objects of $\mathcal
B_X$. Every covering of a basis object has a refinement by a finite covering
of basis objects. Fibre products of basis objects over a basis object remain
in the basis. Restriction to this basis determines a sheaf and its morphisms
uniquely and detects isomorphisms of sheaves.

## Proof

Cover an object by affine opens. On each of them apply the ind-etale
refinement theorem over the affine base $X$. Its faithfully flat affine
refinement is a covering in the small pro-etale site and belongs to
[def-weil-pbc-ind-etale-basis]. For a covering of an affine basis object, the
definition of a pro-etale covering first selects finitely many affine pieces
of its members. Apply the same refinement theorem over that basis object to
these pieces. Their composites with $X$ are ind-etale by the stability lemma
for ind-etale algebras. The relative-map and base-change assertions of that
lemma prove stability under the required fibre products.

For completeness, the extension of a sheaf on this basis is explicit: a
section on an arbitrary object is a compatible family of sections on a basis
covering, with equality imposed on basis coverings of the pairwise
intersections. Two choices are compared on a common refinement, which exists
by the preceding covering and fibre-product assertions. The basis sheaf axiom
makes this comparison independent of refinements and permits gluing. This
constructs a sheaf on the full site inverse to restriction, on objects and
morphisms. It also proves the asserted detection of isomorphisms.
