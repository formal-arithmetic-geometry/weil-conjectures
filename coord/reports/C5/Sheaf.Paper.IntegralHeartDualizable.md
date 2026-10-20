## What changed

Proved `AlgebraicGeometry.ProEtale.integralHeartDualizable` with its original signature.
The proof constructs a finite free presentation over the coefficient DVR, realizes its
short exact sequence, and applies the generic derived short-exact dualizability and
bounded flat mapping-cone criteria. Cover descent gives the canonical global pairing
and Tor bound; duality reverses the interval. The residue calculation dualizes the
uniformizer triangle. The unit's two-term-resolution route is retained.

Added and proved three intermediate results in their own modules: exact scalar realization
and finite free dualizability, local duality and Tor descent, and the residue dual. In the
scalar realization proof, continuous functions into the DVR are torsion-free and therefore
flat. An explicit sectionwise tensor functor and its adjunction identify this exact functor
with the canonical realization. Sheafification is kept abstract during that comparison to
avoid repeated unfolding. The local algebra instance in the sectionwise flatness proof is
inlined to keep elaboration small. No existing public signature, definition or public import
changes.

Validation: all four modules compiled in import order; the final scalar helper also compiled
without warnings after the linter cleanup. The parent interface comparison is empty.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.ProEtale.integralHeartDualizable`.
Added zero holes. All three new public theorems are proved:

- `AlgebraicGeometry.ProEtale.integralHeartRealization_exact_free`;
- `AlgebraicGeometry.ProEtale.integralHeart_local_duality_descent`;
- `AlgebraicGeometry.ProEtale.integralHeart_residue_dual`.

There is no `sorry` in any of the four delivered Lean modules. Existing imported theorems
remain separate stage-3 items; this delivery does not claim to prove those dependencies.

## No longer needed

Removed these proof-only imports from the parent:

- `Mathlib.RingTheory.Noetherian.Basic`;
- `Sheaf.Paper.CompletedConstantSheafReduction`;
- `Sheaf.Paper.ConstantModuleSectionProperties`;
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`;
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`;
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`;
- `Mathlib.CategoryTheory.Sites.LocalProperties`;
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`;
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`;
- `Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel`;
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`;
- `Sheaf.Paper.DerivedNakayamaResolution`;

The direct proof no longer needs the following former DAG proof dependencies and
corresponding top-level `tool_uses` entries:

- `det-prop-sfb-qlbar-colimit-x-integral-limit`;
- `lem-weil-pbc-completed-constant-sheaf-reduction`;
- `lem-weil-pbc-constant-module-section-properties`;
- `def-weil-size-convention`;
- `lem-pur-site-restriction-module-adjunction-exact`;
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`;
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`;
- `lem-sfb-sheaf-cover-local-isomorphism`;
- `lem-weil-pbc-unbounded-derived-iso-cohomology`;
- `lem-pur-rhom-global-sections`;
- `lem-weil-pbc-ringed-site-bounded-free-rhom-model`;
- `lem-pc-bounded-above-flat-kflat-site`;
- `sk-def-sfb-constructible`;
- `det-pe-derived-nakayama-resolution`;

The explicit flat sectionwise tensor realization replaces completed-constant reduction and
constant-module-section infrastructure. Generic derived short-exact and flat-model results
replace the bounded-free RHom, K-flat, and Nakayama route. The existing condensed cover
locality and conservativity declarations supply the local descent API, so the parent does
not import the lower generic ringed-site restriction and global-sections lemmas directly.
The coefficient-limit and constructibility modules remain public statement dependencies;
their removed proof-tool entries do not remove those statement dependencies. These are
pruned dependencies of this proof; no claim is made that every such module becomes
unreachable from all five targets.

## Where the brief, the DAG or earlier work was wrong

The interrupted attempt's report was stale: it listed the scalar-realization theorem as an
unfinished split. Its complete proof now compiles. The original DAG's completed-flatness
route was unnecessary: sectionwise torsion-freeness over the DVR proves exactly the flatness
needed here. Locality is used to detect isomorphisms and vanishing, never equality of derived
morphisms. No target statement or coefficient definition was changed.

## New nodes

`lem-integral-heart-realization-exact` records exactness of completed scalar realization and
dualizability of finite free terms, proved in
`lean/Sheaf/Paper/IntegralHeartRealizationExact.lean`.

`lem-integral-heart-local-duality-descent` records cover descent of the canonical tensor--Hom
comparison and Tor bounds, proved in
`lean/Sheaf/Paper/IntegralHeartLocalDualityDescent.lean`.

`lem-integral-heart-residue-dual` records the residue derived-dual calculation, proved in
`lean/Sheaf/Paper/IntegralHeartResidueDual.lean`.

No change record is needed: all existing public signatures, definitions and public imports
are preserved; new proof helpers in the parent are private and use explicit binders.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
