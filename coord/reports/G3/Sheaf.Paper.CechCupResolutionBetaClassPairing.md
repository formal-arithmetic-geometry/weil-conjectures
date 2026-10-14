## What changed

Restored `Sheaf.Paper.CechCupResolutionBetaClassPairing` and
`Sheaf.Paper.CechCupSignedAxisPairing`, absent from the current repository,
byte for byte from the returned delivery preserved in the repair note.
The public signatures, definitions, and imports of that delivery remain unchanged.
The beta proof uses the signed-axis theorem through a proof-only import.
No upstream instance renaming is delivered.

## Proved and sorry left

The restored theorem
`AlgebraicGeometry.Scheme.Modules.cupCechResolution_beta_class_pairing`
has a complete proof body, conditional on the signed-axis dependency.
Its three private helpers `betaPairing_cycleClass_surjective`,
`betaPairing_pair_exists_cycle`, and `betaPairing_alpha_surjective` are proved.
The sole direct hole is
`AlgebraicGeometry.Scheme.Modules.cupCech_signed_axis_pairing`, node
`lem-sc-cech-cup-signed-axis-pairing`.
Relative to the returned delivery: zero holes closed, zero holes added.
The original upper-hole reduction to the signed-axis construction is a
one-for-one decomposition, not a completed axiom-free proof of the target.

## No longer needed

No additional imports or nodes were pruned in this repair.
The prior route's `CechCupResolutionTotalPairing`
(`lem-sc-cech-cup-resolution-total-pairing`) remains unused by this proof.
The restored proof dependencies are the signed-axis node and the resolution-data,
comparison-data, module-cup-product, and Cech-cup-product definition nodes.
No unit-level route was replaced.

## Where the brief, the DAG or earlier work was wrong

The source checkout contains neither assigned module nor its signed-axis node,
but the dedicated repair note contains their reviewed sources and signatures.
The return reports an anonymous-instance collision in a global batch probe.
The first reader attempted to rename instances in three upstream modules;
these changes fail the forced-adaptation contract because the original
upstream modules still compile against this delivery. They are withdrawn.
The two restored modules compile together without those changes. A batch-wide
collision, if it recurs, needs a separately authorized maintainer repair.
The unit's current `realized` statement and step lists are empty; this delivery
preserves them and does not invent a new unit route.

## Second reading by G3

1. Interface: both modules are absent in the repository. Compared the complete
   sources byte for byte with their restored versions in the repair note;
   both match. No existing declaration or target statement changes. Pass.
2. Proof: compiled both restored modules together from a fresh sandbox build.
   Inspected every proof and scanned for forbidden declarations and definition
   holes. The named signed-axis theorem is the only direct sorry.
   A scratch copy with both `#print axioms` commands reports only `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. Pass with the reported hole.
3. Split: the signed-axis assertion is the lower total-pairing construction,
   independent of hcup and comparison invertibility, rather than a renamed
   beta comparison theorem. Its sourced docstring describes the construction,
   differential cancellation, quotient descent, and axes. Zero degrees,
   repeated indices, empty index types, and zero inputs obey the same formulas.
   Repeated LeanFinder, Loogle, upstream grep, and local searches with different
   queries. No exact replacement was found. Local
   `exists_cupCech_total_cochain_pairing` and `cupCech_total_cochain_axes`
   provide related cochain-level ingredients, but no total homology descent;
   they also use `n2CechCupCochain` rather than the target's declaration.
   Completing that bridge is not a few-minute repair. Pass.
4. Route and pruning: the upper proof lifts beta classes by alpha surjectivity,
   constructs the resolution product cycle via Leibniz, compares the two axis
   evaluations, and uses hcup. Its imports are needed by the signatures or proof.
   The signed-axis import is plain; the signature imports are public.
   The generic signed construction stays below the unit level. No further
   pruned dependencies beyond the prior total-pairing route were found. Pass.
5. Nodes: read both complete node records and their Lean signatures, source,
   natural-language proof, proof dependencies, and blueprint provenance.
   They agree with the restored proof and preserve the original unit route.
   The new-node metadata and declaration statements are present. Pass.

Second reading changed: withdrew three upstream instance renamings and the
incomplete collision change record; replaced the stale report with this audit.
The restored Lean proofs needed no changes.

## New nodes

`lem-sc-cech-cup-resolution-beta-class-pairing` records the restored beta-axis
statement and its proved reduction to signed pairing and comparison glue.

`lem-sc-cech-cup-signed-axis-pairing` records the restored lower signed-total
homology construction, left as a named sorry with source and proof in words.

Restoration change record: `coord/changes/cech-cup-beta-axis-restoration.md`.
