## What changed

Proved `AlgebraicGeometry.mixedAffineChart_sectionsComplexUnit_isIso` by a real reduction:
apply the existing spectrum theorem `affineTildeDerivedSectionsUnit_isIso`, move from
homotopy-mapped complexes to quotient endpoints using `mapHomotopyCategoryFactors`,
apply conditional affine-isomorphism transport, use `mapHomologicalComplexCompIso`,
and compose the invertible factors of `mixedSectionsComplexUnit`.
Added the proof-only import `Sheaf.AlgebraicGeometry.AffineSectionsUnitTransport`.
The new module states transport for arbitrary spectrum sheaf complexes, conditional
on invertibility of their spectrum comparison. It does not assert affine acyclicity.
Existing declaration signatures, visibility, definitions and options are unchanged.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.mixedAffineChart_sectionsComplexUnit_isIso`
(node `lem-sc-mixed-affine-chart-sections-complex-unit-isIso`).
Added exactly one hole: `AlgebraicGeometry.affineSectionsUnit_transport`
(node `new-affine-sections-unit-transport`), in its own module.
This is a decomposition, not a complete proof: one upper hole closed, one strictly
separate conditional transport hole added, net zero holes closed. The spectrum
acyclicity theorem is actually used, and remains an existing dependency; its
transitive open statements are unchanged. No sorry remains in the item's module.
The first worker's `mixedAffineChart_rightDerivedUnit_isIso` was removed before delivery.

## No longer needed

No original import, node in the old proof_deps, or module is pruned. In particular,
`new-affine-tilde-derived-sections-unit-isIso` and its proof-only import remain used.
Removed the first worker's undelivered near-restatement node
`new-mixed-affine-chart-right-derived-unit-isIso` and its Lean theorem; it is not a
pruned repository node. The new module imports the definitions and instance support
its signature needs directly, rather than importing MixedGlobalExtension or Tilde.

## Where the brief, the DAG or earlier work was wrong

The first worker's split omitted a verbatim Lean signature, statement dependencies,
Mathlib searches, and a complete natural-language proof. Its target docstring was
accidentally deleted and its letI generated a warning. Its report called the result
proved without distinguishing decomposition. The repaired split isolates transport
from the actual spectrum acyclicity theorem, and the target proof uses both.
The existing unit `sk-thm-picard-duality` has empty realized statement/step arrays;
this delivery changes neither those arrays nor any unit or chapter route.
Source checked at https://stacks.math.columbia.edu/tag/06Z0; the local literature
file is absent on this machine. The exact-equivalence transport proof is explicitly
identified as an argument written by the second reader, using the established
K-injective resolution node and standard restriction/derived functor constructions.

## New nodes

`new-affine-sections-unit-transport`, in
`lean/Sheaf/AlgebraicGeometry/AffineSectionsUnitTransport.lean`, assumes the spectrum
comparison is invertible for an arbitrary complex C and transports that assumption
along S.toSpecΓ. Its docstring gives the exact-equivalence, scalar-identification,
K-injective resolution and derived-unit uniqueness argument. Zero rings, zero
complexes and the identity affine isomorphism introduce no extra hypotheses.
No statement or definition changes and no change records.

## Second reading by F1

1. Compared all delivered modules with the repository. The original two signatures
   are byte-for-byte unchanged, the body of mixedSectionsComplexUnit is unchanged,
   and the original target docstring is restored. The new theorem is in its own
   module; no existing declaration or visible import was altered. Verdict: pass.
2. Compiled both files through lcompile.py. The item has no sorry and the new
   theorem alone has `:= by sorry`. No axiom, unsafe, opaque, implemented_by, extern,
   or data chosen from an unproved existence statement is introduced. A scratch
   copy with #print axioms reports only propext, Classical.choice and Quot.sound
   for mixedSectionsComplexUnit, plus sorryAx for the target and transport theorem.
   Verdict: valid reduction with its one declared open transport theorem.
3. Checked the new conditional statement, including zero ring/zero complex and
   identity transport. Its natural-language proof specifies the scalar map in
   the correct direction and the resolution comparison. Searched LeanFinder and
   Loogle with different queries, Mathlib and project sources; LeanSearch returned
   Internal Server Error, recorded as unavailable. Generic localization/derived
   comparison lemmas were found, but no duplicate of this conditional transport.
   It is strictly the transport part, not the affine-tilde acyclicity claim.
   Verdict: true, needed intermediate statement; decomposition honestly reported.
4. Checked the shortest available route: the target now applies the existing
   spectrum result before the transport hole and handles only formal factor
   isomorphisms afterward. All original imports remain necessary for the interface
   or that proof route; the added import is proof-only. All old proof dependencies
   remain used. Inspected the unit's realized fields and preserved them and the
   affine-identification route. Verdict: pass; no repository modules pruned.
5. Checked both node files against the Lean declarations. The existing node now
   lists the spectrum theorem and conditional transport, in the order used.
   The new node has its verbatim signature, full statement and proof, source,
   dependency records, creation/blueprint fields and actual Mathlib searches.
   Its K-injective resolution dependency is supplied by its imports. Verdict: pass.

Second reading changed the near-restatement split into conditional arbitrary-complex
transport, made the spectrum theorem actually participate in the proof, restored the
original docstring, removed the letI warning, completed the node metadata, and
corrected the progress accounting. Compiled and axiom-checked; dry run and delivery
are performed by deliver3.py.
