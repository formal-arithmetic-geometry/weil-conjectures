## What changed

Proved `AlgebraicGeometry.Scheme.adic_finite_stratification_pullback` using three proved,
separate results: actual finite fibre-product refinement, normalized transport of local
module isomorphisms, and preservation of finite type local constancy. The three helper
modules have matching new DAG nodes; the item's node records the resulting proof route.
All existing elaborated declaration types are unchanged. The saved work changes
`adicStratificationModelTopology` from `abbrev` to `def` with exactly the same body;
its reduction behavior is the only topology change. The compatibility definition now specializes the
shared `SheafOfModules.NormalizedLocalModuleTrivialization` definition; unfolding gives
exactly its original quantified unit equation. This requires a public import of the new
normalization helper. The change record is
`coord/changes/adic-stratification-normalization-predicate.md`. A named public
ring-sheafification instance reuses the existing generic Mathlib instance and avoids
repeating expensive inference on the concrete scheme-site constructions. Private instances
supply finite limits on the equivalent small sites and preservation by base change.
No existing consumer requires adaptation.

The normalization helper computes its composite adjunction on sections and proves the
unique unit equation. Its Hom equivalence is irreducible, with computation and naturality
lemmas, to avoid expensive repeated expansion of the adjunction construction. All four modules compiled cleanly in import order; the main item took 12.4 seconds.
The required delivery dry run passed (commit `5af1952a15`, no push). Its optional
source-appended axiom probes timed out. A separate import-only probe of the compiled
main theorem and all three helper theorems succeeded in 1.9 seconds: each uses only
`propext`, `Classical.choice`, and `Quot.sound`. The main file also compiled independently
without warnings in 24.4 seconds. Zero `sorry`s occur in the four delivered modules.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.adic_finite_stratification_pullback`
(node `lem-sfb-adic-finite-stratification-pullback`).

Also proved all three new results:

- `AlgebraicGeometry.Scheme.finite_stratification_wide_pullback`
  (`lem-sfb-finite-stratification-wide-pullback`).
- `SheafOfModules.normalized_local_module_pullback`
  (`lem-sfb-normalized-local-module-pullback`).
- `SheafOfModules.finite_type_constant_module_pullback`
  (`lem-sfb-finite-type-constant-module-pullback`).

Holes closed: 1 of 1 original holes. Holes added: 0. Sorries left: none, including in
private helpers and definitions. This is a proof, not a decomposition into unproved results.

## No longer needed

No existing import was removed. The new normalization helper is publicly imported because
the compatibility definition specializes its predicate; the original declaration types
remain definitionally identical.
The normalization helper does not import
`Sheaf.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf`; it needs only Mathlib's
module pullback, site pullback, slice-limit and filtered-colimit interfaces.

The following former direct proof dependencies are replaced by the three proved helpers
or by existing constructions; the item's updated node removes them from `proof_deps`:

- `lem-sfb-geometric-inverse-image-constant-module`
  (`Sheaf.SixFunctors.GeometricInverseImageConstantModule`) and
  `lem-weil-pbc-localize-ringed-site-morphism`
  (`Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`): constant-module comparisons already
  have completed proofs in the item; normalized local transport is proved directly for
  RingCat sheaves, without a CommRingCat coefficient-transport interface.
- `lem-weil-pbc-etale-covering-base-change`,
  `lem-weil-pbc-weakly-etale-composition-base-change`, and
  `lem-galois-fpqc-covering-base-change`: existing base-change continuity and
  `CoverPreserving.of_isContinuous` give the required sieve statement directly.
- `lem-pur-scheme-constructible-preimage`, `lem-weil-pbc-proper-fp-permanence`,
  `def-weil-closed-immersion`, and `def-weil-open-immersion`: existing
  `Stratification.pullback` and `Stratification.inter` supply the geometric constructions.
- `lemma-constructible-pullback-stratification` and `def-pc-fibre-product` are now used
  by the geometric helper rather than directly by the item.
- `def-constructible-stratification`, `def-weil-constructible-subset`,
  `def-weil-pbc-proetale-site`, and
  `def-weil-pbc-finite-type-locally-constant-module-sheaf` remain statement dependencies;
  their redundant direct proof-dependency entries are removed.

All seven old top-level `tool_uses` entries are withdrawn from the item's updated node:
`lemma-constructible-pullback-stratification`, `lem-pur-scheme-constructible-preimage`,
`lem-weil-pbc-proper-fp-permanence`, `lem-weil-pbc-etale-covering-base-change`,
`lem-weil-pbc-weakly-etale-composition-base-change`, `lem-galois-fpqc-covering-base-change`,
and `lem-weil-pbc-localize-ringed-site-morphism`. No approval entry is added or reordered.
No claim is made that these modules are globally unreachable from other targets.

## Where the brief, the DAG or earlier work was wrong

The existing general localization theorem uses CommRingCat sheaves followed by forgetting
to RingCat; the item uses constant sheaves directly in RingCat. The new proved helper
handles arbitrary ring sheaves and continuous finite-limit-preserving functors directly.
The existing `Stratification.inter` constructs actual pullback schemes, so the geometric
argument reuses it while retaining all wide-cone projections and universality.

The preserved report's temporary private hole is now proved. The final kernel timeout
was resolved by sharing the exact normalization predicate between the generic theorem and
the scheme-site definition. No file or proof was split to evade the compile limit. The resumed compile diagnostics
also exposed repeated expensive ring-sheafification inference; elaborating its proof first
on an abstract small category and then specializing it avoids unfolding scheme sites. Its remaining rewrites needed
explicit product objects, correct composition parentheses, and reduction through the
module restriction interfaces. Removing a broad unused import also required explicitly
importing Mathlib's finite-limit construction for slice categories.

Empty schemes, empty families, empty input strata, arbitrary coefficient rings and finitely
generated modules without finite presentation are retained. No unit route is bypassed:
these are auxiliary results within the common-strata step of integral models.

## New nodes

`lem-sfb-finite-stratification-wide-pullback`: the proved geometric finite fibre-product
refinement, extending existing binary intersection with limiting-cone data and deletion
of empty strata. Module: `Sheaf.AlgebraicGeometry.FiniteStratificationWidePullback`.

`lem-sfb-normalized-local-module-pullback`: proved transport of a chosen module isomorphism
with its exact adjunction-unit equation and uniqueness, for arbitrary ring sheaves.
Module: `Sheaf.AlgebraicGeometry.NormalizedLocalModulePullback`.

`lem-sfb-finite-type-constant-module-pullback`: proved preservation of fixed-ring finite
type local constancy by a constant-preserving pullback, using normalized local transport.
Module: `Sheaf.AlgebraicGeometry.FiniteTypeConstantModulePullback`.

Change record: `coord/changes/adic-stratification-normalization-predicate.md`.
It records the shared definition, its public import, and the complete direct-user audit.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
