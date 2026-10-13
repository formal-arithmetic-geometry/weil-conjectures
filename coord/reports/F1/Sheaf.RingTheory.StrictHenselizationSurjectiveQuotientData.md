## What changed

Proved `Algebra.strictHenselization_surjective_quotient_data` without changing its signature,
visibility, or existing public import. Constructed the canonical separable closure of the
residue field of B, its B-algebra and scalar tower, and the quotient B-algebra by descending
A → C → C/IC with Mathlib's `RingHom.liftOfSurjective`. No data is chosen from an unproved
existence theorem. Updated the existing node's proof and proof origin to this construction.

## Proved and sorry left

Closed `Algebra.strictHenselization_surjective_quotient_data`
(node `lem-sbc-strict-henselization-surjective-quotient-data`): 1 of 1 original holes closed.
Added no holes; no sorry remains in the delivery. The first worker's proposed hole
`Algebra.exists_quotient_algebra_of_surjective` was eliminated by a direct Mathlib construction;
its proposed module and node are not delivered. Net holes closed: 1, not a decomposition.

## No longer needed

No original imports, proof-dependency nodes, or library modules were pruned: the original
node's proof_deps was empty. Removed the first worker's proposed proof-only import
`Sheaf.RingTheory.SurjectiveQuotientAlgebra`, its new module, and its proposed node
`new-stage3-surjective-quotient-algebra`; these were never dependencies of the repository version.

## Where the brief, the DAG or earlier work was wrong

The old node's plan spoke of finality and colimits, although this auxiliary statement only
asks for residue and quotient algebra data. The new proof establishes exactly that data.
The proposed split-off was unnecessary: Mathlib already provides the surjective descent.
The condition hI is stronger than this data construction needs; its binding is retained
unchanged and acknowledged in the proof to preserve the original interface without warnings.
The first worker's new sorry lacked a complete natural-language proof, and its node had a
placeholder Lean statement and empty proof. Removing the split resolves these faults.

## Second reading by F1

1. Compared the delivered module with the repository version using diff and checked that
   the entire text preceding the proof is byte-for-byte unchanged. No definitions, public
   imports, target statements, existing signatures, or visibility were altered. PASS.
2. Compiled the original proposal, found style warnings, and repaired them. The final
   delivery has no sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow definition.
   A scratch copy with `#print axioms` and the delivery tool's kernel probe verify the axioms.
   Canonical closure and descended ring homomorphism provide concrete data. PASS.
3. Checked the quotient descent on I = 0 (π an isomorphism), C = A, and the zero quotient
   (including a zero ring C): in each case IC kills ker π, so the construction remains valid.
   Searched with Loogle (`RingHom.liftOfSurjective`), LeanFinder (factor a ring homomorphism
   through a surjective homomorphism when its kernel vanishes), and rg in Mathlib and both
   library roots. Mathlib's descent equivalence supplies the needed map; no split-off
   statements or new declarations survive. PASS.
4. Used the shorter Mathlib route and retained the existing public import, which supplies
   signature notions (IsSepClosure, local residue fields, quotient algebra). Removed the
   unnecessary proposed helper. The unit sk-prop-input-spreading has empty realized statement
   and step lists; these are unchanged. This auxiliary data proof replaces no unit or chapter
   step and prunes no existing dependency. PASS.
5. Read the existing node and its unit. Updated proof/proof_deps/proof_origin to the actual
   construction. No node dependencies are needed for the Mathlib construction, and the old
   proof_deps was empty. Removed the defective proposed new node. PASS.

Changes by the second reader: eliminated the split-off sorry/module/node using direct descent,
replaced letI with let to remove linter warnings, retained the hI binder, corrected the node's
proof plan, and rewrote the report to record a complete proof rather than a decomposition.

Source checked: [Stacks Project, Tag 05WS](https://stacks.math.columbia.edu/tag/05WS).
