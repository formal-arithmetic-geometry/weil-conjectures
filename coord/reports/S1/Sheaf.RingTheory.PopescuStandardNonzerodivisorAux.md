## What changed

The statement and existing docstring of `exists_localized_smooth_factorization` are unchanged.
Its proof now applies the first proof step, stated separately as
`localized_target_is_ind_smooth` in the new module
`Sheaf.RingTheory.PopescuLocalizedIndSmooth`, and proves the finite-presentation extraction
step directly in Lean.

The extraction proof transports finite presentation along
`Localization.tensorRightAlgEquiv`, constructs the localized algebra map and proves its
coefficient compatibility, and forgets the algebra colimit to commutative rings using a
proved private universal-property construction. It lifts the base ring to universe
`max u v`, applies Mathlib's
`RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`, and turns the resulting ring map
into an algebra map using the coefficient identity. The final equality is obtained from
the factorization equality. The helper for forgetting the colimit is adapted from the
proved helper in `FilteredColimitSmoothProduct`; it has no `sorry`.

No public definition or existing signature changes. All writes are in the sandbox.
Both modules compile without warnings through `lcompile.py --all`.

## Proved and sorry left

Closed original hole: `exists_localized_smooth_factorization`
(node `lem-weil-pbc-popescu-standard-nonzerodivisor-aux`). Its proof has no `sorry`.

Added hole: `localized_target_is_ind_smooth`
(node `lem-weil-pbc-popescu-standard-nonzerodivisor-aux-localized-ind`), in
`Sheaf.RingTheory.PopescuLocalizedIndSmooth`. It isolates the total-fraction field/product
argument, without any finitely presented source algebra or factorization map.

This is a decomposition: one original hole closed, one strictly earlier intermediate
hole added, net zero holes. The finite-presentation extraction is completely proved,
not deferred. There are no other holes in the delivery.

The remaining lemma was checked conceptually for a field base (one minimal-prime factor),
a reduced base with multiple components, and the zero target algebra. The nontriviality
of the base excludes an empty family of minimal primes. The universes match the field
hypothesis: residue fields are in `u`, fibre algebras and diagrams in `max u v`.

## No longer needed

Removed direct proof imports from the original module:
`Sheaf.RingTheory.ReducedNoetherianTotalRingFractions` and
`Sheaf.RingTheory.FilteredColimitSmoothProduct`. These are now proof-plan imports of the
new intermediate module, so their nodes and modules remain needed transitively and are
not globally pruned.

Removed unused imports:
`Mathlib.CategoryTheory.Limits.Constructions.Over.Connected` and
`Mathlib.CategoryTheory.Filtered.Connected`. The direct universal-property construction
supplies the required ring colimit without the under-category equivalence argument.
No project nodes or Sheaf modules become globally unnecessary. All original unit steps
remain realized.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The node's second step is already supported
by the recorded Mathlib factorization theorem, with explicit universe lifting of the
coefficient ring needed to apply it. Automatic scalar-tower inference for localization
was expensive; supplying `isScalarTower_localizationAlgebra` explicitly makes the final
file compile in approximately six seconds with the default heartbeat bound.

The local copy does not contain `literature/stacks-project/smoothing.tex`; the remaining
lemma's source and complete proof are retained from the existing node and docstring,
with the new node containing the same first argument. The next worker can also use the
already-proved `Algebra.ind_smooth_of_ringEquiv` in
`Sheaf.Algebra.IndSmoothRingEquiv` for the final transport.

## New nodes

`lem-weil-pbc-popescu-standard-nonzerodivisor-aux-localized-ind` states exactly the first
argument of the original node: the field-case assumption implies ind-smoothness of the
total-fraction localization. Its own module makes it a separate work item. Its statement,
full proof plan, source, search receipts, and verbatim Lean signature are included.
The original node's proof dependencies now use this intermediate node and the existing
Mathlib-backed finite-presentation/filtered-colimit nodes.

## Second reading by S1

1. Compared the delivered `PopescuStandardNonzerodivisorAux.lean` with the repository version. The existing theorem statement and docstring are byte-for-byte unchanged; only imports, proof code, and the recorded proof route changed. The new `PopescuLocalizedIndSmooth` module and its node are included as the stated decomposition.

2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds without warnings. The only remaining `sorry` is the named theorem `localized_target_is_ind_smooth`, and it has a public docstring, source, blueprint id, and matching DAG node. No forbidden declarations or hollow definitions were added.

3. Checked the split statement against the original first proof step. It has exactly the field-case hypothesis, the reduced Noetherian nonzero base, regularity, localization target, universe bounds, and ind-smooth conclusion. It is strictly simpler than the original factorization theorem and is required by the proof.

4. Checked the proof route and pruning. The original unit's two steps remain represented: the first is delegated to the new intermediate node, and the second is proved by finite-presentation transport and filtered-colimit factorization. Removed imports are proof-only or unused, and the node's `proof_deps` and `proof_origin` match the Lean proof.

5. Checked edge cases recorded by the worker (field base, multiple minimal-prime components, and zero target algebra). No statement or definition change was found, and no existing declaration was duplicated.

Changed during second reading: appended this review record only; no Lean proof or statement edits were necessary.
