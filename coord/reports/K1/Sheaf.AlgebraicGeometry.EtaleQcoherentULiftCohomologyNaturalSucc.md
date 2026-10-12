## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_etaleTensorSectionsSheaf_cohomology_ulift_natural_succ`
without changing its statement or visibility. Replaced the finite affine Čech route with
an explicitly constructed lifted injective resolution, using the existing coefficient-lift
injectivity and homology-preservation theorems. Added the general natural
resolution-evaluation comparison in
`Sheaf.CategoryTheory.Sites.CohomologyResolutionEvaluationNatural`.
Both existing public imports and the target signature are unchanged. The new helper's
statement has arbitrary site, coefficient and Ext universes, a terminal object, enough
injectives, and a specified injective resolution. Its conclusion concerns evaluation of
one resolution and has no coefficient-universe comparison.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_etaleTensorSectionsSheaf_cohomology_ulift_natural_succ`.
The delivery adds no holes. The new theorem
`CategoryTheory.Sheaf.exists_cohomology_resolution_evaluation_natural_succ`
(`lem-sc-cohomology-resolution-evaluation-natural`) is proved from the existing natural
Ext/derived-Hom comparison and Mathlib's resolution and homology APIs.
No `sorry` remains in either delivered Lean module. Existing dependencies' unfinished
proofs are not changed by this delivery.

The naturality proof constructs an endomorphism of the small resolution and its lifted
endomorphism, proves augmentation compatibility, and combines the two evaluation
naturality equations with group-lift homology naturality. The comparison is fixed before
the sheaf endomorphism. The generic helper checks reindexing by equality of derived
morphisms, so the explicitly requested `HasExt.standard` computation is retained.

## No longer needed

Removed these proof imports from the item:

- `Sheaf.AlgebraicGeometry.EtaleAffineQcoherent`
- `Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech`
- `Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`

The new route does not use these old proof-dependency nodes:

- `lem-sc-etale-affine-qcoherent`
- `lem-sc-etale-affine-qcoherent-succ`
- `lem-sc-cech-spectral`
- `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`
- `lem-weil-pbc-homotopic-maps-equal-cohomology`

The corresponding modules and their proof-only descendants are unnecessary through this
item; other import paths may still need them. The resolution-lift-existence node remains:
its Mathlib match `InjectiveResolution.desc` is used directly. No global pruning count is
claimed. The unit record `sk-prop-cd` has no realized node bindings to bypass, and its
cohomological-dimension route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The old plan was mathematically usable but unnecessarily long. The library now provides
coefficient-lift injectivity and exactness interfaces on the small étale site, allowing
one to construct a lifted resolution directly. This adds no preservation-of-injectives
hypothesis to the item. The old cohomology-to-derived-evaluation theorem lacks a naturality
clause; the new helper supplies it, using the existing proved natural Ext/derived-Hom
comparison rather than adding an unproved comparison. Compactness, separatedness and
quasi-coherence are not needed by the new proof, and remain in the unchanged statement.

The coefficient-lift results and the Ext/derived-Hom result are generic tool lemmas from
other units; they supply homological-algebra interfaces rather than replacing a unit's
mathematical route. No statement correction or forced adaptation was needed.

## New nodes

`lem-sc-cohomology-resolution-evaluation-natural`, in the item's chapter and unit,
records the general natural comparison between Ext-defined cohomology and the homology
of a chosen injective resolution evaluated at a terminal object. Its source is Stacks
Tags 01FT and 06XR. The Lean proof uses `lem-sc-ext-right-derived-hom` and Mathlib.
Searches included LeanSearch (unavailable), LeanFinder, Mathlib grep, library grep and
blueprint searches; the existing comparison without naturality was found and distinguished.
The zero sheaf, zero cohomology groups and arbitrary terminal objects satisfy the same
construction; no nonempty site hypothesis is introduced. No change record is needed.

## Second reading by K1

1. **Visible changes and statements.** Compared both delivered modules and the target node with the repository versions. The target theorem signature and visibility are unchanged byte for byte; the helper is a new, explicitly documented theorem. No existing declaration was weakened or given extra hypotheses.

2. **Proof and axioms.** Compiled both modules with `lcompile.py --all`; both compile cleanly. Searched the delivered sources for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, and `implemented_by`; none occur. The proofs construct the lifted resolution and use the stated naturality equations rather than choosing arbitrary witnesses.

3. **New statement.** Checked the helper on arbitrary terminal objects, zero sheaves, and empty sites: its construction still applies and introduces no nonemptiness assumption. Its naturality hypothesis is exactly augmentation compatibility, and the conclusion is precisely the induced homology map. It is strictly more general than the target and is needed by the target proof; no duplicate library declaration was found.

4. **Pruning and route.** The target proof uses the coefficient-lift injectivity and homology interfaces, the resolution-lift construction, and the new natural comparison. The four old affine/Cech proof imports and their corresponding old proof dependencies are removed and listed above. The unit record `sk-prop-cd` has no realized route binding that this proof bypasses.

5. **DAG agreement and delivery.** Updated the target node proof, dependencies, and origin to match the Lean proof, and added the complete node for the helper with source, proof steps, searches, and Lean attachment. No statement-change record is required. The only remaining holes are in imported dependencies outside this delivery.

Changed during second reading: added this review section; no Lean proof changes were necessary after compilation.
