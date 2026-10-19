## Worker report

Recorded the existing, proved declaration
`Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`
in `WeilConjectures.Mathlib.RingTheory.Finiteness.Descent`, branch `slopmaster2`.
No module is added. The source was read locally at lines 33–54 and independently
retrieved with `scompile.py --source` from the published source. Both agree.
The item already has a closed upstream audit for this exact theorem, with
`sorry: false`; this delivery completes its partial attachment with the full
stage-2 Lean record. No field other than `lean` changes.

Source checked: `literature/stacks-project/algebra.tex`, label
`lemma-descend-properties-modules`, part (2), lines 20307–20344;
`tags/tags` confirms Tag 03C4. The source's `M ⊗_R S` is canonically
isomorphic to the node's `T ⊗_R M` by tensor symmetry. The upstream statement
uses exactly the node's order.

Hypothesis and conclusion correspondence:

- Commutative rings R and T: upstream section variables `{A B : Type*}`,
  `[CommRing A] [CommRing B]`, with A = R and B = T.
- Ring homomorphism R → T: `[Algebra A B]` encodes this homomorphism as
  `algebraMap A B`. Every commutative-ring homomorphism supplies this structure
  using `RingHom.toAlgebra`; this adds no restriction on the map.
- Faithful flatness: `[Module.FaithfullyFlat A B]`, exactly the ring-map
  definition through its induced algebra/module structure.
- R-module M: `{M : Type*} [AddCommGroup M] [Module A M]`.
- Finite presentation of T ⊗_R M as a T-module:
  `[Module.FinitePresentation B (B ⊗[A] M)]`. Its B-action is the standard
  action on the left tensor factor, not restriction of scalars to A.
- Conclusion: `Module.FinitePresentation A M`, precisely finite presentation
  over the original ring. There are no additional locality, Noetherian,
  finite-generation, or finiteness conditions on the algebra.

Dependency declarations read:

- `def-weil-pbc-faithfully-flat-ring-map`: `Module.FaithfullyFlat` in
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` (class at line 63), and
  `RingHom.FaithfullyFlat` / `RingHom.faithfullyFlat_algebraMap_iff` in
  `Mathlib.RingTheory.RingHom.FaithfullyFlat` (lines 25–34). These give the
  exact interpretation of the faithful-flatness hypothesis.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs` (line 81), with its actual
  quotient construction and `TensorProduct.tmul` (line 107).
- `def-sc-finitely-presented-module`: this is the existing DAG definition
  for ordinary finitely presented ring modules. Its Mathlib match is the
  class `Module.FinitePresentation` in
  `Mathlib.Algebra.Module.FinitePresentation` (lines 67–69), characterized
  by finite generators and a finitely generated relation kernel, equivalently
  an exact sequence `A^m → A^n → M → 0`. This is exactly the module notion
  used by Tag 03C4 and by the upstream declaration. The previous citation
  `def-weil-pbc-module-finite-type-presentation` was removed because its
  recorded declaration is `SheafOfModules.IsFinitePresentation`, a sheaf
  notion on a ringed space and not the ordinary module notion required here.

The upstream proof was read: descend finite generation of M, choose a finite
free surjection to M, use flatness to identify its base-changed kernel with
the kernel of the base-changed surjection, use finite presentation upstairs
to obtain finite generation of that kernel, then descend finite generation
of the original kernel. This is exactly the argument of 03C4(2).

Edge cases checked: the statement admits the zero module, the zero ring,
and the identity faithfully flat homomorphism, without a `Nontrivial`
assumption. A zero target over a nonzero source is excluded by faithful
flatness itself. The section variables use separate `Type*` universes for
A, B, and M, with no equality restriction. There is no local-ring hypothesis
(despite the historical item-id suffix). No statement correction is needed.

Searches performed in this session:

- `msearch.py ... leanfinder "finite presentation descends faithfully flat tensor product module"`:
  eight hits, including ascent of module finite presentation and descent of
  flatness, but no module-finite-presentation descent theorem.
- `msearch.py ... loogle "Module.FinitePresentation, Module.FaithfullyFlat"`:
  zero hits.
- `msearch.py ... grep "FinitePresentation.*faithfullyFlat" RingTheory`:
  six hits; direct reading shows the similarly named Mathlib result in
  `RingTheory/Finiteness/Descent.lean` concerns algebras, not modules.
- `msearch.py ... leansearch "finite presentation of modules descends along faithfully flat ring maps"`:
  eight hits, including ascent, module presentation characterizations, and
  descent of flatness; none is the exact module-descent statement.
- `rg` of the upstream finiteness-descent source found the exact declaration
  at lines 38–40. Direct reading of its full signature, section variables,
  docstring, and proof confirms the match. The existing node audit identifies
  the same theorem and module.
- `rg` for the item id in upstream `WeilConjectures/`: no textual blueprint
  tag. `rg` for the declaration in `dag/lean_names_upstream.json`: no hit.
- `rg` for faithful-flatness/finite-presentation wording and the exact theorem
  name in `lean/Sheaf`: no duplicate of this statement found.


## Statement corrected

The statement citation was corrected because `def-weil-pbc-module-finite-type-presentation`
denotes sheaf finite presentation on a ringed space, whereas Tag 03C4 and the
Lean theorem concern ordinary ring modules. The corrected citation is the
existing `def-sc-finitely-presented-module`; no hypothesis, object, or
conclusion changed. The complete `statement_change` record preserves the old
statement and old dependency list.

The complete citer audit found `lem-trf-flat-finite-type-flat-point-local`,
which still holds: its Step 3 applies this theorem to an ordinary stalk module
and a faithfully flat local-ring map. The citer is named in the record and was
not edited.

## Dependency citation repair and citer audit

The item statement and `stmt_deps` now cite `def-sc-finitely-presented-module`
for both ordinary finite-presentation clauses. The item’s theorem and its
existing Lean declaration are unchanged mathematically. The removed
`def-weil-pbc-module-finite-type-presentation` citation was a sheaf-level
notion and did not support the ordinary rings-and-modules statement.

A repository-wide `rg -rl
"lem-trf-finite-presentation-module-descent-flat-local" dag/nodes` audit found
one citer: `lem-trf-flat-finite-type-flat-point-local`. Its proof Step 3 uses
this item only as the ordinary faithfully-flat descent theorem for the stalk
module, so that use still holds exactly. The citer itself is not edited: its
separate sheaf finite-presentation citation remains outside this repair’s
scope, and no statement or proof dependency of the citer is broken by the
item’s corrected citation.

Validation: `deliver2.py --no-push` checks this existing declaration through
its generated import-and-`#check` probe using the required scompile wrapper,
and runs server preflight. The final delivery repeats these checks.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
