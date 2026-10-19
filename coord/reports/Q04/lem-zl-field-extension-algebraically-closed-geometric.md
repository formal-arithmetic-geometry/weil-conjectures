## Worker report

The module `lean/Sheaf/FieldTheory/FieldExtensionGeometricallyIrreducible.lean` states the
Tag 037P criterion. It introduces fields `k` and `K` in one universe and the Mathlib algebra
structure `[Algebra k K]`, which is the recorded field-extension convention. Its theorem
`AlgebraicGeometry.geometricallyIrreducible_of_isAlgebraic_mem` has a sorry-only proof.

The hypothesis

`h : ∀ x : K, IsAlgebraic k x → ∃ y : k, algebraMap k K y = x`

renders “every element of `K` algebraic over `k` belongs to `k`”: `IsAlgebraic k x` is the
recorded Mathlib definition of an algebraic element, and equality with `algebraMap k K y`
expresses membership in the embedded copy of `k`. Since both terms are fields, the algebra map
is injective, so this is equivalent to the node's “algebraically closed in” wording.

The conclusion

`GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k K)))`

renders that the field extension `K/k` is geometrically irreducible. The structure morphism is
exactly the affine-spectrum map induced by the field-extension algebra map, and
`GeometricallyIrreducible` is Mathlib's geometric irreducibility property for this morphism.
No finite-generation, separability, characteristic, or algebraic-closedness assumption was
added.

Dependencies used are all Mathlib leaves recorded by the node: `Algebra` from
`Mathlib.Algebra.Algebra.Defs` (the field-extension structure), `IsAlgebraic` from
`Mathlib.RingTheory.Algebraic.Defs` (the algebraicity predicate), and
`AlgebraicGeometry.GeometricallyIrreducible` from
`Mathlib.AlgebraicGeometry.Geometrically.Irreducible` (the conclusion). Their full signatures
and docstrings were read in the pinned Mathlib source. The node's project definitions
`def-pc-field-extension`, `def-weil-algebraic-element`, and
`def-pc-geometrically-irreducible` therefore need no project-side duplicate modules.

Edge cases checked before writing: `K = k` satisfies the hypothesis via `y = x`; a purely
transcendental extension has no nontrivial algebraic elements and is covered; positive and zero
characteristic are both allowed; no finite-type or separability condition is implicit; and the
single universe `u` keeps the scheme spectra and the algebra map in the same universe as the
Mathlib geometric-irreducibility class. The existential membership formulation also covers the
identity algebra map without choosing a noncanonical inverse.

Searches for an existing declaration or duplicate notion:

- `msearch.py ... leanfinder "field extension algebraically closed in extension geometrically irreducible"` returned algebraic-closure and geometric-reducedness declarations, but no theorem with this hypothesis and conclusion.
- `msearch.py ... loogle "GeometricallyIrreducible, IsAlgebraic, algebraMap"` returned no hits (the remote index reported `GeometricallyIrreducible` as unknown).
- `msearch.py ... grep "GeometricallyIrreducible|IsAlgebraic|field extension" AlgebraicGeometry/Geometrically` returned only generic geometric-property declarations, with no field-extension criterion.
- `rg` over `WeilConjectures/` and project `lean/Sheaf` found no declaration of the Tag 037P criterion; the nearby geometric-irreducibility results use different hypotheses.
- The dependency-node search found the exact Mathlib matches above, so no new definition or dependency repair was needed.

No statement correction, `STATEMENT-DISPUTED`, new node, or dependency module is needed.

## Second reading by Q04

I reread the node, the module, and all three recorded dependency declarations. The two field
instances and the algebra map render exactly the field-extension object; the hypothesis has one
conjunctive implication for every `x : K` and uses `IsAlgebraic k x` exactly; and the conclusion
is the geometric-irreducibility class on the canonical `Spec.map` morphism. The identity case,
transcendental case, and characteristic cases remain included. No mismatch was found.
