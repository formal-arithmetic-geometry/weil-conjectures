## What changed

Completed `lean/Sheaf/Algebra/Homology/KernelShiftedMappingCone.lean` without changing
its public theorem signature or visibility. Added the proof-only import
`Mathlib.Algebra.Homology.HomologySequenceLemmas`. All helpers are private and proved.
The comparison is explicitly constructed, including its chain-map equation and both
projection identities. The quotient map to the shifted identity cone is explicitly
constructed; its degreewise kernel property and epimorphism give a short exact sequence.
Mathlib's identity-cone contracting homotopy kills the quotient's homology, and the long
exact sequence proves that the comparison induces a mono and epi in every degree.
Localization then supplies the derived-category isomorphism.

Updated `lem-weil-degreewise-epi-kernel-cocone-qis` to record the homology-sequence route.
The existing docstring's triangle argument remains a valid alternative mathematical proof;
the updated node describes the implementation. The unit's statement and realized steps
are unchanged: this comparison is below that level.

## Proved and sorry left

Closed the single original hole:
`CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi`
(node `lem-weil-degreewise-epi-kernel-cocone-qis`). No holes added or left anywhere in
this delivery; this is a proof, not a decomposition. The explicit constructions use no
unproved existence theorem. Compilation checks the degree/sign conventions, both
projection identities, quasi-isomorphism, and derived-category isomorphism.

## No longer needed

The proof does not use the planned nodes `lem-weil-pbc-complex-ses-triangle`,
`def-weil-triangulated-category`, or `lem-sf-triangle-morphism-iso` as separate proof
steps; they are removed from this node's `proof_deps`. In particular, no direct proof
imports of `Mathlib.Algebra.Homology.DerivedCategory.ShortExact` or the triangle
morphism isomorphism lemmas are needed. These were not direct imports in the original
module, so no existing import line was removed. Their Mathlib definitions may still be
available transitively from the required public derived-category interface; no claim
is made that those Mathlib modules leave the global import closure. No Sheaf proof
dependency module is imported. The two original public imports remain necessary for
the statement and the kernel construction.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt already had a compiling explicit chain map, but left the
entire public theorem unproved and had no report or completed delivery. That construction
was retained and completed. The DAG's triangle comparison is mathematically valid but
longer than the homology exact-sequence argument, which is implemented directly from
proved Mathlib declarations. Searches with leanfinder found
`CochainComplex.mappingCone.quasiIso_descShortComplex`, which concerns the cone of the
first arrow rather than this kernel comparison; loogle rejected the unqualified
`ShortComplex.ShortExact` query, and grep identified the homotopy and homology APIs used.
No statement or definition was disputed or changed. No new statements were introduced;
the proof applies to all integer degrees, including zero complexes and identity maps,
and uses degreewise epimorphy exactly to prove the quotient map epic. No splitting of
f or enough-injectives assumption is used.

## Second reading by D4

1. I compared the delivered module against the repository version. The theorem signature and all existing declaration statements are byte-for-byte unchanged; only a proof-only import and proof bodies changed. The DAG node change records the revised proof route and dependencies.

2. I compiled `lean/Sheaf/Algebra/Homology/KernelShiftedMappingCone.lean` with `lcompile.py`. It has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; the remaining `sorryAx` reported by `#print axioms` comes from imported open declarations. The explicit comparison, quotient map, short exact sequence, and homology argument typecheck.

3. The theorem statement remains the original kernel-to-shifted-cone claim. No split-off statements or new DAG nodes were added, and the proof uses only the existing node dependencies plus Mathlib's homology-sequence lemmas. The edge cases of arbitrary integer degrees, zero complexes, and identity maps are covered by the polymorphic construction and the contractible identity cone.

4. I checked the proof route from the top downward. The homology long exact sequence is a shorter valid realization of the already stated short-exact-complex step; the unit statement and realized route remain unchanged. The removed triangle dependencies are no longer used, and the added `HomologySequenceLemmas` import is proof-only.

5. The DAG node's `proof`, `proof_deps`, and `proof_origin` match the Lean proof: the chain map and projections, the quotient short exact sequence, contractibility, and mono/epi homology argument are all recorded. No definition or public interface was changed.

I changed only the proof import/body and the node's proof metadata; no mathematical correction was needed.
