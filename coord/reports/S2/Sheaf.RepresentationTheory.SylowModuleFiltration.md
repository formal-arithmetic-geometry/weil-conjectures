## What changed

Proved `Rep.exists_openSubgroup_primary_module_filtration` with its statement unchanged.
The finite action image supplies the Sylow reduction, and the open kernel is the finite
intersection of stabilizers. Added two fully proved helper modules: PrimaryInvariantExtension
and PrimaryPGroupFiltration. Their fixed-point/Cauchy argument and maximal attainable chain
avoid scalar structures on ℓ-power quotients and concatenation of quotient flags.
All three modules compile locally and on the server without warnings.
`#print axioms` for each theorem lists only propext, Classical.choice, Quot.sound.
The dry run passed preflight except for the second reading, to be supplied by the reader. The unit sk-prop-h2 has no realized
statement or step involving this node; its route is unchanged.

## Proved and sorry left

Proved `Rep.exists_openSubgroup_primary_module_filtration` (lem-sc-sylow-module-filtration),
`Representation.exists_primary_filtration_of_isPGroup` (lem-sc-primary-pgroup-filtration),
and `Representation.exists_primary_invariant_extension` (lem-sc-primary-invariant-extension).
No sorry remains or is added. Zero modules use a length-zero chain; a zero quotient never
requires an extension. The p-group acting on the module need not be finite or faithful.

## No longer needed

Removed proof imports `Sheaf.RepresentationTheory.DiscreteContinuousCohomology` and
`WeilConjectures.Mathlib.RepresentationTheory.Invariants`.
The proof no longer needs nodes def-exc-continuous-cohomology and
lemma-weil-pbc-finite-l-group-filtration, or their modules on this branch. Open stabilizers
are already part of DiscreteContinuousRep. The latter's vector-space filtration is replaced
by Mathlib fixed-point counting, Cauchy's theorem, and a proved finite maximal-chain argument.
The statement's public imports are preserved for importers.

## Where the brief, the DAG or earlier work was wrong

No statement error. The planned powers-of-ℓ filtration and refinement are unnecessary.
The finite action image makes the compactness argument for a finite quotient unnecessary.
The source documents are absent in this clone; Tags 0A3R, 0GIZ, 0GJ0 were read online.
Tag 0GIZ omits its proof and hints at augmentation ideal nilpotence; the new algebraic
proof is explicitly agent-written rather than attributed to that omitted proof.
LeanSearch returned an Internal Server Error; the attempt is recorded, and LeanFinder,
Loogle and source grep supplied the verified Mathlib lemmas.

## New nodes

lem-sc-primary-invariant-extension: fully proved enlargement of a proper stable subgroup,
using the nonzero invariants in its primary quotient and Cauchy's theorem.

lem-sc-primary-pgroup-filtration: fully proved finite-chain construction by maximality,
using the extension theorem. Both belong to sec-curve-estimates, sk-prop-h2.
No change record is needed: existing signatures and public imports are unchanged.

## Second reading by S2

1. Compared the existing module with the repository using diff and checked the theorem
   signature byte for byte. It is unchanged, as are all public imports; there are no
   existing definitions changed. The two helper modules and nodes are genuinely new.
   Verdict: pass; no change record is required.
2. Compiled all three modules in import order through lcompile.py without errors or
   warnings. Scratch copies with #print axioms for each of the three public theorems
   show exactly propext, Classical.choice, Quot.sound. Inspected all proof bodies:
   no sorry, forbidden declaration, or hollow definition occurs. Verdict: pass.
3. There are no split-off holes. Both new helper statements are fully proved, and
   each is a strictly smaller part of the argument. Checked zero V, W = bottom,
   W proper, trivial Q, and modules of exponent greater than the prime: the quotient
   is nonzero exactly when an extension is required; Cauchy's theorem applies to
   its nonzero primary invariants. Nonfinite Q is allowed by Mathlib's p-group
   fixed-point theorem. Repeated semantic search with the query "finite abelian p
   group automorphisms invariant composition series trivial factors", plus source
   searches for composition series, invariant subgroups, and filtrations in Mathlib,
   Sheaf, and the upstream representation library found no exact existing theorem.
   The upstream vector-space flag requires ZMod scalars and does not directly cover
   primary groups of higher exponent. Verdict: pass.
4. Read the proof downward: finite action image, Sylow inverse image, finite maximal
   attainable chain, and fixed-point/Cauchy extension. Imports needed only by proofs
   are plain imports. The public imports of the existing statement are preserved.
   No shorter direct library theorem was found. No longer needed lists both removed
   old proof dependencies and both removed module imports. The realized record of
   sk-prop-h2 has no statement or step involving this node, so the unit route stays.
   Verdict: pass.
5. Compared the three DAG proofs and their proof_deps with the Lean bodies. Their
   dependencies and agent-written proof origins agree; the new nodes have source,
   complete proof steps, search records, creation, blueprint, chapter, unit, and Lean
   records. The existing node changes only proof, proof_deps, and proof_origin.
   Verdict: pass.

Changed the existing theorem's stale proof docstring to describe the finite action
image and fixed-point/Cauchy maximal-chain proof actually implemented. No proof,
statement, definition, import, or node needed repair. One original hole is closed
(Rep.exists_openSubgroup_primary_module_filtration); zero holes are added. The two
new helper theorems are fully proved, so this is a proof rather than a decomposition.
