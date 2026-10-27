## What changed

The signature of `WeilConjectures.residue_lisse_projective_models` is unchanged.
Its proof now performs strong induction on the natural interval length `(b-a).toNat`
on each member of a finite clopen partition. The existing
`complete_top_residue_cell_cone` supplies the lifted top free cell, complete cone,
shortened residue interval and singleton-interval isomorphism. The induction is
written in Lean, including the zero-rank case.

A proved private helper represents the connecting map from the bounded projective
complex by a chain map, compares two rotated distinguished triangles, and shifts
its mapping cone back. Explicit cone projections identify the terms below the top
and in the top degree. This argument uses Mathlib's K-projective and triangulated
APIs directly and works with independent object and morphism universe sizes.

The resulting finite free terms are identified with finite products by reindexing
`ULift (Fin N)` and the canonical finite biproduct comparisons. Their isomorphisms
provide exactly the inclusion and retraction required by the original statement.
The differentials remain arbitrary sheaf-linear maps.

The new module `Sheaf.Paper.ResidueLisseClopenBases` isolates the remaining
preparation: simultaneous residue bases, complete restriction in the precise
`integralDerivedPullback` presentation, and the local Tor tests. It asserts no
integral complex model. Its one proof obligation has a source, a complete proof
in words, and a new node. No existing shared definition, public import, theorem
signature, or module other than the item is changed. The parent's proof route is
updated to the code.

Validation: `lcompile.py --all` compiled the new preparation module in 42.9 seconds
and the item in 43.7 seconds, with no errors or warnings. The original theorem
statement and public-import list were also compared textually and are unchanged.

## Proved and sorry left

The original hole in `WeilConjectures.residue_lisse_projective_models`
(`lem-fix-residue-lisse-projective-models`) is replaced by a complete Lean proof
from the existing cone theorem and the new preparation lemma. The private
`attachCell`, `finiteFreeProductIso`, `freeZero`, `singleFree`, and `localFreeModel`
helpers are all proved.

One hole is added: `WeilConjectures.residue_lisse_clopen_bases`, node
`lem-sf-residue-lisse-clopen-bases`, in its own new module. This is the only
`sorry` left in the delivery. The existing imported
`WeilConjectures.complete_top_residue_cell_cone` remains an external proof
dependency; its hole is unchanged.

Counts: one original hole closed, one new hole added, net zero. This is a
**decomposition**, not a net proof closure. The interval induction, singleton
case, projective chain-map representation, cone attachment and finite-product
retraction construction are completely proved in the item.

## No longer needed

The following original private proof imports are removed from the item:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.Paper.ConstantModuleSectionProperties`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit`
- `Sheaf.AlgebraicGeometry.WeaklyEtaleStability`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.AlgebraicGeometry.EtaleComparison`
- `Sheaf.AlgebraicGeometry.IntegralConstantCompletion`
- `Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties`
- `Sheaf.Paper.CompleteResidueCohomologyBounds`
- `Sheaf.Paper.DerivedNakayamaFirstReduction`
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`

The parent no longer directly invokes
`lem-sf-completed-coefficient-free-resolution`,
`det-prop-integral-criterion-constant-coefficients`,
`det-pe-derived-nakayama-first-reduction`,
`lem-sf-complete-residue-cohomology-bounds`, or
`lem-sf-projective-cohomology-split-model`: their required content is already
packaged in the top-cell cone theorem. The clopen localization theorem is used
by the new preparation node rather than directly by the parent.
`lem-sf-projective-top-cell-attachment` and its module are unnecessary for the
parent: its small-site signature does not apply to the original site, and the
needed cone construction is proved privately over any abelian category.
No whole-library module withdrawal or global pruning is claimed; several of
these nodes are still needed transitively by the cone and localization results.

The obsolete direct `tool_uses` approvals removed from the parent node are:

- `det-prop-integral-criterion-constant-coefficients`
- `lem-weil-l-adic-extension-integers-dvr`
- `lem-weil-pbc-completed-constant-sheaf-reduction`
- `lem-weil-pbc-constant-module-section-properties`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-weil-proetale-surjective-tower-derived-limit`
- `det-pe-derived-nakayama-first-reduction`
- `det-pe-topos-functoriality-site`
- `sk-lem-pe-weakly-etale-stability`
- `det-pe-morphisms-etale-comparison`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-pc-kflat-resolution`
- `lem-pur-derived-change-of-rings`

These removals describe the parent's direct proof route; they do not withdraw
any upstream declaration or any dependency of the remaining imported theorems.

## Where the brief, the DAG or earlier work was wrong

The existing `CochainComplex.projective_top_cell_attachment` quantifies over
`C : Type u` with `[SmallCategory C]` and coefficient rings in the same universe.
The original small pro-etale site has object universe `u+1` and morphism universe
`u`, so this theorem cannot be instantiated directly there. Its mathematical
argument is size-independent. The private `attachCell` proof removes that
interface obstacle without changing the shared theorem or site.

The clopen localization theorem returns ordinary restriction and free models on
localized sites. The target instead uses the completed derived pullback and the
full-site residue cohomology/Tor interfaces. The new preparation lemma records
that actual compatibility work explicitly; it is not treated as definitional
equality. It has no integral projective-model conclusion and therefore does not
rename the original goal. Edge cases checked in the statement and argument are
the empty base/cover, zero ranks, a singleton interval, and successive intervals.
The unit and chapter route remain unchanged.

## New nodes

`lem-sf-residue-lisse-clopen-bases` corresponds to
`WeilConjectures.residue_lisse_clopen_bases` in
`Sheaf.Paper.ResidueLisseClopenBases`. It extracts the restriction/cohomology
preparation from the parent's first step, with the existing clopen localization
result as its principal dependency. It does not assert the existence of a
bounded integral representative. Its source is Stacks 09C3/098F with exact
restriction and Tor locality from 0946/08FZ. The searches and the blueprint
ancestor are recorded in the node. No change record is required for a shared
interface: none is changed.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
