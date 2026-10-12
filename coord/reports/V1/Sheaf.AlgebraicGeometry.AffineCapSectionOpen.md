## What changed

Proved `AlgebraicGeometry.Scheme.Modules.affine_cap_section_open` using the affine dictionary,
the affine symmetric-algebra construction, and a new restriction compatibility theorem. Added
`Sheaf.AlgebraicGeometry.NonvanishingLocusRestrict` and its DAG node. The proof-only imports are
kept private where possible.

## Proved and sorry left

Closed `affine_cap_section_open`. The new `nonvanishingLocus_restrict` theorem is also proved.
No `sorry` remains in the delivered modules. Holes closed: 1. Holes added: 0.
The imported `affine_cap_section_open_dictionary` and `affine_cap_section_open_algebra`
still contain their existing holes; this delivery proves the parent from them.
The new restriction theorem uses only standard axioms.

## No longer needed

The separate direct dependency on `lem-weil-pbc-affine-tilde-gamma-adjunction` is no longer
needed: the affine dictionary already supplies finite projectivity, stalk rank-one
trivializations, and the prime-membership description. Its module remains a transitive
dependency of the dictionary, so this does not remove it from the target import closure.
No original import was removed; the algebra and dictionary imports are both used.

## Where the brief, the DAG or earlier work was wrong

The DAG omitted the necessary compatibility statement identifying the nonvanishing locus after
restriction to an affine open. This was added as `lem-sc-nonvanishing-locus-restrict`.

## New nodes

`lem-sc-nonvanishing-locus-restrict` is stated and proved in
`lean/Sheaf/AlgebraicGeometry/NonvanishingLocusRestrict.lean`.

## Second reading by V1

1. Compared both delivered modules against the repository. The existing theorem signature is byte-for-byte unchanged; the restriction module is new. No accidental statement or definition changes. Verdict: pass.
2. Both modules compile cleanly through lcompile.py. No sorry, forbidden declarations, or hollow definitions occur in them. Scratch axiom probes show nonvanishingLocus_restrict uses only propext, Classical.choice, Quot.sound; affine_cap_section_open additionally uses sorryAx from existing dependencies. Verdict: pass.
3. Reviewed the restriction statement for general modules, including zero section, zero module, and empty source. The stalk isomorphism preserves maximal-ideal membership in both directions, proving exactly the claimed equality. Independent leanfinder and loogle queries and rg searches found basicOpen restriction lemmas and generatingLocus results, but no duplicate theorem for this general module predicate. There are no new split-off holes. Verdict: pass.
4. The proof uses the existing affine dictionary and algebra nodes without bypassing any unit step; sk-thm-curveestimate.realized is unchanged. All imports are used. A scratch compile without ProjectionFormula fails to synthesize tensor-power invertibility, confirming that proof-only import is required. The only old proof dependency removed is lem-weil-pbc-affine-tilde-gamma-adjunction, already documented above; its transitive module remains. Verdict: pass.
5. Checked the original and new nodes against their Lean declarations and the proof as written: proof steps, proof_deps, and proof_origin agree. The new node has the required provenance, searches, source, chapter, unit, and Lean record. Verdict: pass.

Second reading changed only the report; no Lean or DAG repair was necessary. Checked the 01PV proof in the local Stacks source copy /home/ubuntu/c1-stacks-review/properties.tex.
