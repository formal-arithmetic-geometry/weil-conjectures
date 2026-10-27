## What changed

Proved `SheafOfModules.ExactPullbackSigned.exact_pullback_signed_comparison`
in its existing module, preserving its full statement, universes and public imports.
Added proof imports of `ResolvingTensorSignedCoherence`,
`TensorColimitsIndependentCoefficients` and Mathlib's `PointwiseLeftDerived`. Proved private helpers compare curried and uncurried tensor maps, extract the
two normalized model equations, and package the natural constraints into
`TensorConstraints`.

Exact localization is itself a left-derived functor by Mathlib's
`isLeftDerivedFunctor_of_inverts`. Left-derived uniqueness produces eta and its
all-complex factorization equation. Transporting shifts along eta gives the
required shift structures; naturality along flat-term K-flat resolutions proves
uniqueness from the stipulated resolving normalization. Existing tensor
model-closure supplies resolving single complexes, so the K-flat pullback
preservation theorem also yields flat-module preservation. The module adjunction
supplies coproduct preservation, and additivity supplies integer signs.
The canonical shift-unit comparison and normalized tensor constraints satisfy
the hypotheses of the existing resolving signed-coherence theorem. Its
conclusions give all three final equations and the comparison transport formula.
The DAG proof and proof dependencies now record this route.

Local high-priority sheaf-composition instances avoid repeated searches; local
folding attributes keep the existing tensor and localization constructions shared.
The complete module compiled through `lcompile.py`; the final delivery checks
recompile it. Its theorem
statement was checked textually against the current repository and is unchanged.

## Proved and sorry left

Closed 1 hole: `SheafOfModules.ExactPullbackSigned.exact_pullback_signed_comparison`
(node `lem-pur-exact-pullback-signed-comparison`). Added 0 holes; split off 0.
No sorry remains in the delivered module. Existing lower dependency theorems
remain outside this delivery; proving this item from those declared dependencies
is the stage-3 proof, not a claim that the target closure is axiom-free.

## No longer needed

Removed direct proof imports of
`Sheaf.Algebra.Homology.KFlatTotalTensorModel`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`,
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction` and
`Mathlib.CategoryTheory.Localization.Predicate`.
Their needed definitions or generic APIs are available through retained imports.

The direct dependency `lem-pur-exact-derived-resolving-identification` and its
module `Sheaf.Paper.ExactDerivedResolvingIdentification` are bypassed: Mathlib
already proves exact-factorization left-derived uniqueness for the comparison on
complexes and supports independently sized source and target derived categories.
The direct dependency `lem-pur-cochain-pullback-tensor-coherence` and its module
`Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence` are used through the existing
resolving signed-coherence declaration, rather than a separate application here.
Neither is withdrawn: this delivery makes no assertion that other consumers no
longer need them. No module is withdrawn or globally pruned.

## Where the brief, the DAG or earlier work was wrong

The item docstring describes an earlier ten-step plan, while its current DAG
already factors signed coherence into declared dependencies. The exact resolving
identification dependency currently takes a homotopy-category comparison, extra
resolving shift hypotheses, and a shared derived-category universe; it cannot be
applied directly to this item's complex comparison with independent universes.
The replacement is Mathlib's exact-localization left-derived uniqueness, with a
real resolving-representative naturality argument for the weaker uniqueness
hypothesis of this item's statement. `tensorMap` becomes a definition with its original body and an explicit result
type, so it can stay folded locally. The `TensorConstraints` model equations are
factored verbatim into named public
predicates to avoid repeated expansion in generated eliminators. This preserves
the field types definitionally and needs no consumer adaptation. The change
record is `coord/changes/K4-exact-pullback-tensor-constraints.md`.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
