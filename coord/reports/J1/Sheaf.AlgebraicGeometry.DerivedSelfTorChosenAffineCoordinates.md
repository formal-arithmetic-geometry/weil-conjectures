## What changed

Proved the body of `AlgebraicGeometry.exists_derived_selfTor_chosen_affine_coordinates`
in `Sheaf.AlgebraicGeometry.DerivedSelfTorChosenAffineCoordinates`, preserving its complete
signature and all existing public imports. Added a proved private helper
`quotient_section_coordinates`: `i.app` is surjective on affine sections and its kernel
is `i.ker.ideal`, so the induced quotient section map is a linear equivalence. Its
normalization on quotient representatives is proved by reflexivity.

The main proof constructs a global K-flat resolution of B[0], computes its derived tensor
using `kFlat_derivedTensor_comparison_natIso`, applies the exact derived homology
factorization, and obtains a global sheaf isomorphism from ordinary tensor homology to
intrinsic self-Tor. It composes ordinary affine coordinates with this isomorphism on sections.
It constructs augmented quotient lifts using the already proved
`exists_quotient_resolution_tensor_comparison`, identifies its quotient homomorphism with
the required `Ideal.quotientMap`, proves the coefficient restriction equation on quotient
representatives using `i.naturality`, and transports the ordinary restriction equation
using `PresheafOfModules.naturality_apply`.

Added the proof-only imports `Sheaf.Algebra.Homology.KFlatResolution`,
`Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison`,
`WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion`, and
`Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionCoordinates`.

The one new theorem separates the ordinary geometric comparison from the derived tensor
transport, the canonical quotient normalization, and construction of augmented algebraic
lifts. It takes two arbitrary quasi-coherent coefficients, their specified affine section
models, and a supplied global K-flat resolution. It concludes natural coordinates for
ordinary tensor homology, for supplied comparison maps, and has no derived tensor,
closed immersion, quotient map, or existence of lifts in its statement. This is a
strict subargument, not the assigned theorem with renamed coefficients. Both files compile
with `lcompile.py`; the assigned proof takes approximately 18 seconds and the new statement
approximately 5 seconds, within the unchanged 60-second limit.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.exists_derived_selfTor_chosen_affine_coordinates`
(node `new-b3-derived-self-tor-chosen-affine-coordinates`). Its body has no sorry.
The private helper `quotient_section_coordinates` is proved entirely from existing APIs.

Added one hole:
`AlgebraicGeometry.exists_qcoh_ordinary_tensor_resolution_coordinates`
in `Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionCoordinates`
(node `new-j1-qcoh-ordinary-tensor-resolution-coordinates`). Its whole proof is `:= by sorry`;
its docstring and node give the ordinary K-flat zigzag, affine homology calculation,
and augmented-map naturality proof. This delivery is a decomposition: one hole closed,
one hole added, net zero new hole reduction. No claim of a completely sorry-free proof
of the intrinsic coordinate theorem is made.

Edge cases checked mathematically: zero coefficients have zero tensor homology and zero
section modules; empty affine charts have the zero coordinate ring; n=0 uses the ordinary
augmentation homology comparison; no flatness of the basic ring map or projectivity of
restricted target terms is assumed. The canonical quotient section equivalence and the
quotient tensor lifting theorem include I=top and I=bot without extra hypotheses. The
new theorem introduces no definition choosing arbitrary data from an unproved existence
statement. All choices of coordinates and K-flat resolutions occur within theorem proofs.

## No longer needed

Removed these proof-only imports from the assigned module:

- `Sheaf.AlgebraicGeometry.AffineQuotientRestrictedIso`
- `Sheaf.AlgebraicGeometry.AffineDerivedTensorChartComparison`
- `Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionNatural`
- `Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison`
- `Sheaf.Algebra.Homology.BoundedFlatKFlat`
- `Mathlib.Algebra.Homology.Embedding.ExtendHomology`
- `Mathlib.Algebra.Homology.Embedding.CochainComplex`

The new ordinary comparison still needs exact tilde homology, bounded flat K-flatness,
extension homology, and the affine chart total tensor calculation. Accordingly its
proof plan retains `new-affine-derived-tilde-homology-comparison`,
`lem-pc-module-bounded-flat-kflat`, `lem-pc-affine-chart-total-tensor`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`, and
`lem-weil-pbc-spec-module-tilde-sections`, with the corresponding imports in the new module.
These are moved into the remaining ordinary subargument, not claimed as pruned globally.

The route no longer needs `lem-sc-affine-quotient-restricted-iso` /
`Sheaf.AlgebraicGeometry.AffineQuotientRestrictedIso`: the closed coefficient normalization
is constructed directly on sections and quasi-coherence supplies its affine sheaf model.
It no longer directly needs `lem-pc-affine-derived-tensor-chart-comparison` /
`Sheaf.AlgebraicGeometry.AffineDerivedTensorChartComparison` or
`lem-pc-derived-tensor-open-restriction-natural` /
`Sheaf.AlgebraicGeometry.DerivedTensorOpenRestrictionNatural`: the global K-flat tensor
comparison supplies derived transport, and the lower theorem concerns ordinary tensor
homology. No claim is made that other target branches cease to import those modules.
The assigned node's proof dependencies have been updated to this actual assembly.
No unit-level realization is bypassed; the unit's recorded realized lists are empty.

## Where the brief, the DAG or earlier work was wrong

The superficially similar `SelfTorAmbientLocalizedComparisons`,
`SelfTorOrdinaryResolutionSections`, `SelfTorOrdinaryLocalizedComparisons`, and
`SelfTorNonpositiveFlatSections` cannot be imported here: their imports reach the assigned
module through `SelfTorNonpositiveChosenComparisons` and `DerivedSelfTorAffineCoordinates`.
`import_direction.py may` explicitly rejects the ambient route. Reusing those theorems
would close an import cycle. The new theorem is about arbitrary quasi-coherent coefficients
and supplied ordinary resolutions, and has no imports of any of those downstream modules.

The DAG originally described the normalized chart calculation but the available chart
comparison gives only an objectwise nonempty isomorphism, not the joint augmented restriction
square. The remaining ordinary comparison states that geometric naturality obligation
explicitly. LeanSearch returned an HTTP internal server error; this is recorded as
unavailable rather than as a negative search result. Loogle, LeanFinder, and Mathlib grep
were run through msearch.py and are recorded in searches.jsonl.

The local literature checkout contains citation inventories but not Stacks TeX source.
The cited Stacks pages 08DX, 08DV, 06YB, 06YT, 01I9, and 00LS were read online. The official
tag index was checked for the TeX labels recorded in the new node. The node marks the
expanded zigzag/naturality proof as agent-written from those sources.

## New nodes

`new-j1-qcoh-ordinary-tensor-resolution-coordinates`, in
`dag/nodes/sec-picard-framework/new-j1-qcoh-ordinary-tensor-resolution-coordinates.json`:
the ordinary tensor homology comparison described above, with supplied semilinear coefficient
and augmented resolution maps. Its module is
`lean/Sheaf/AlgebraicGeometry/QCohOrdinaryTensorResolutionCoordinates.lean`.
This is the only new node and the only new hole. The second reading narrows the new module's public imports; see its section below.
No change record is required: existing
signatures, definitions, visibility, and public imports stay identical; no other existing
module is adapted.

## Second reading by J1

1. Compared the delivered original module against the repository using diff, and
programmatically compared its complete theorem signature byte for byte: identical.
Its existing public imports, existing docstring and visibility are unchanged. The
only added declaration there is a private proved quotient-section helper. No
existing definition is changed and no change record is needed. Verdict: pass.

2. Compiled both modules in import order with lcompile.py, without errors or warnings.
The sole new sorry is the named public ordinary-coordinate theorem listed above.
Scanned both files for forbidden declarations and proof escapes: none. Explicit
axiom printing and the delivery probe check the original theorem and private helper;
upstream open statements and the reported split account for sorryAx. No data definition
is introduced or chosen from an unproved existence theorem. Verdict: pass.

3. Read the new statement, its complete verbal proof and matching new node. Checked
n=0 (augmentation gives ordinary tensor product), zero coefficients, empty charts,
and identity basic inclusions. For arbitrary augmented lifts, scalar extension to
the smaller affine ring is exact because a basic inclusion is localization; the
extended projective resolution stays a resolution. Its sheafified augmentation
square therefore represents coefficient restriction. The tensor formula determines
k on all pure tensors, so the homology square follows from the common K-flat
resolution zigzag. This is a true ordinary-complex comparison subargument; derived
transport, closed-immersion normalization and existence of quotient lifts remain
proved in the original module. Independently searched with LeanFinder for K-flat
replacement/localization, Loogle for projective-resolution lifts and grep for
homology naturality, and read the nearby upstream/self-Tor modules. The nearby
self-Tor coordinate statements have an import path back through
SelfTorNonpositiveChosenComparisons to DerivedSelfTorAffineCoordinates and this
item, so they cannot be reused here. No applicable duplicate found. Read Stacks
08DX and 06YT directly; they support the affine calculation and K-flat square
argument. Verdict: pass as a decomposition, net zero holes; the remaining geometric
assembly cannot be closed in a few minutes from these objectwise APIs.

4. Reviewed the top-down assembly: quotient section normalization is proved from
surjectivity and the kernel equality; global K-flat derived transport and naturality
of its sheaf isomorphism are explicit. The ordinary comparison is the only new
obligation. Checked every old proof_deps entry: quotient restriction, affine derived
chart comparison and derived open naturality are bypassed; bounded flatness, tilde
homology, tilde adjunction and tilde sections move to the ordinary subargument;
chart total tensor also remains there, and quotient-resolution lifting remains
in the original proof. The report distinguishes these moves from global pruning.
The unit sk-thm-picard-duality has empty realized statement and step lists; no
recorded unit realization is bypassed. Verdict: pass.

5. Compared the node Lean signatures with the source and reviewed proof steps,
uses unions, proof_origin, source, search records and creation/blueprint metadata.
The original node changes only stage-3-owned fields. The new node describes
ordinary tensor homology, not the original intrinsic self-Tor claim. Verdict: pass.

Second-reading changes: narrowed the new module's public dependency from
Sheaf.AlgebraicGeometry.DerivedCategory to
Sheaf.Paper.DerivedHomMayerVietoris (the signature needs moduleRings, not a derived
category). Made Mathlib.Algebra.Category.ModuleCat.Projective and
Mathlib.AlgebraicGeometry.Modules.Tilde proof-only imports in the new module.
Added public Mathlib.AlgebraicGeometry.Modules.Sheaf for Scheme and its module
section API, which are needed by the statement. The tilde APIs are used only by
the planned proof. Added public Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
for the signature's quasi-coherence hypotheses. No proof or statement
needed repair. Recompiled the resulting files and ran the dry-run delivery checks.
