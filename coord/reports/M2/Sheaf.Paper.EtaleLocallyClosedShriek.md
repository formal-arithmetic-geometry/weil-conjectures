## What changed

Completed the proof of `AlgebraicGeometry.Etale.etaleLocallyClosedShriekComparisons` in
`lean/Sheaf/Paper/EtaleLocallyClosedShriek.lean`. The proof establishes finite-Tor
preservation, the closed and locally closed coefficient isomorphisms, their naturality,
the compact-support comparison, and the pasted counit identity. It uses the ordinary
finite-Tor exceptional stability theorem from the source library, the finite direct-image
comparison, the open scalar tensor comparison, the ambient closed adjunction, and the
ordinary closed-support triangle. The module's proof-only imports were reduced to the
ones used by this route.

## Proved and sorry left

The module's sole theorem, `AlgebraicGeometry.Etale.etaleLocallyClosedShriekComparisons`,
is proved: one original hole closed, zero holes added, zero holes split off.
No `sorry` remains in the delivered module. The proof uses existing library theorems;
this does not certify that their transitive dependencies are sorry-free.

## No longer needed

The proof no longer needs the former amplitude/flat-model route and its imports:
`Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude`,
`Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`,
`Sheaf.AlgebraicGeometry.FiniteTypeSheafFiniteness`,
`Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`,
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.Paper.FiniteCoefficientFlatModel`,
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`,
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension`,
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`,
`WeilConjectures.ConstructibleSheaf.Pullback`,
`WeilConjectures.SixFunctors.OpenClosed.Stalk`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`,
`WeilConjectures.ConstructibleSheaf.OpenClosed`.
The following old direct DAG proof dependencies are removed (their elementary
geometry or categorical API is used directly where needed; this is not a claim
that every corresponding module leaves the global target closure):

- `lem-weil-pbc-finite-type-over-noetherian`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-qc-open-immersion-finite-type`
- `lem-etale-finite-type-sep-closed-derived-dimension`
- `sbc-thm-finiteness-finite-type`
- `prop-exc-closed-tor`
- `prop-weil-pbc-inverse-image-modules-exact`
- `prop-constructible-pullback`
- `lem-sf-flat-model`
- `lem-weil-pbc-independent-bounded-flat-kflat`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-kun-04ca`
- `lemma-openclosed-stalk-lowerstar`
- `prop-weil-pbc-geometric-stalks-exact`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `lem-pur-derived-change-of-rings`
- `def-weil-triangulated-category`
- `lem-sf-triangle-morphism-iso`
- `lem-weil-pbc-extension-by-zero-exact`

The retained source-library ordinary exceptional stability declaration belongs to
the old ordinary-etale audit of `sk-prop-sf-rf-shriek-preservation`; its current
pro-etale localizing declaration is not imported or applied. The source open
stability API supplies restriction and extension preservation.

Removed obsolete `tool_uses` approvals: `lem-etale-finite-type-sep-closed-derived-dimension`, `sbc-thm-finiteness-finite-type`, `prop-exc-closed-tor`, `lem-sf-flat-model`, `lem-weil-pbc-independent-bounded-flat-kflat`, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, `lem-kun-04ca`, `lem-pur-derived-change-of-rings`. The remaining approvals retain their original order.

## Where the brief, the DAG or earlier work was wrong

The retained earlier attempt had the right categorical route but was blocked by compiler
transport failures and had not recorded its completed proof. The source blueprint's
expanded twelve-step route is longer than necessary in this library: the source ordinary
finite-Tor exceptional stability theorem supplies the closed preservation result directly,
so the separate generic cohomological-dimension, flat-model, K-flat, and stalk route is
pruned. The target statement and all public definitions are unchanged.
The unit record has no realized statement or step entries to bypass. The
pre-existing theorem docstring still describes the longer original plan; the
updated node records the implemented shorter route.

Validation: the continuation dry run compiled the complete module and probed its
12 added private lemmas. It reported only two line-length warnings; both lines
have been wrapped. All public signatures, definitions, public imports and section
commands are unchanged. No change record is needed for these private proof helpers
and proof-only import changes. The coefficient-finiteness import is retained for
the unit route. The delivery dry run supplies the final validation result.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
