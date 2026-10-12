## What changed

The existing declaration `ExteriorAlgebra.exists_koszul_conormal_comparison`
keeps its signature and now obtains a normalized map and applies the
quasi-isomorphism criterion. Its two added imports are proof-only.
The new modules `KoszulConormalComparisonMap` and
`KoszulConormalComparisonQuasiIso` state the construction and cohomology
subarguments separately. Their public imports support their signatures;
the existing conormal basis is imported privately as a dependency of their
recorded proof plans. No definition or existing statement changes.

## Proved and sorry left

Closed the original local hole in
`ExteriorAlgebra.exists_koszul_conormal_comparison` by a reduction to two
strictly smaller statements. This is a decomposition, not an axiom-free proof
of the original result, and not positive net sorry progress: one hole closed,
two new holes added.

Added holes:
- `ExteriorAlgebra.exists_koszul_conormal_comparison_map`, node
  `new-s3-koszul-conormal-comparison-map`, construction of the normalized map.
- `ExteriorAlgebra.koszul_conormal_comparison_is_quasiIso`, node
  `new-s3-koszul-conormal-comparison-quasi-iso`, calculation of cohomology for
  an already supplied normalized map.

Neither theorem is the original existence-of-a-quasi-isomorphism statement:
the first only constructs a cochain map; the second assumes that map and proves
its homological property. Neither chooses data for any definition. No other
new holes are introduced; imported existing holes remain open. All three
local declarations have only the allowed axioms and `sorryAx` in their closure.

## No longer needed

No existing import is removed; no module is claimed to be pruned.
The target's old direct `proof_deps` are replaced by the two split nodes:
`def-weil-pbc-koszul-regular-sequence`, `def-sc-koszul-dual-complex`,
`def-sc-koszul-conormal-comparison`, `def-weil-pbc-koszul-complex`,
`lem-sc-exterior-power-dual-pairing`, and `lem-sc-koszul-conormal-basis`.
All six remain needed below the two split nodes or in the target's statement;
this is relocation of the subarguments, not removal from the import closure.
The last is explicitly imported in the split modules, the pairing and Koszul
complex are already accessible through their signature imports.

## Where the brief, the DAG or earlier work was wrong

The first report called the target completely proved, although its reduction
still depends on two newly unproved theorems. The new nodes had copied old
review stamps, generic proof steps, Lean syntax in their natural-language
statements, and copied searches not present in this sandbox's search log.
The split-theorem docstrings omitted sources and the complete proof arguments.
The second reading repaired these records and documentation.

## New nodes

`new-s3-koszul-conormal-comparison-map` records the signed quotient evaluation
construction, its chain-map equation, and determinant normalization.
`new-s3-koszul-conormal-comparison-quasi-iso` records complementary-wedge
self-duality, the top cokernel, and the induced determinant isomorphism.
Both remain within the diagonal Koszul calculation of `lem-sc-finite-duality`
and the unit `sk-thm-picard-duality`. No change record is needed.

## Second reading by S3

1. Compared the delivered target with its repository file using `diff`:
   only two private imports and the proof body differ. The entire existing
   signature, universes, hypotheses, conclusion, visibility, and docstring
   are unchanged. The other two delivered modules are new. No definitions
   are added or edited, and no target statement changes. Verdict: pass.
2. Compiled all three modules in import order using only `lcompile.py`.
   Scanned their sources for forbidden declarations and checked each of the
   three theorem axioms in a scratch copy with `#print axioms`. There are
   exactly two new named theorem holes and no sorry in a definition; the
   theorem closures use only standard axioms and `sorryAx`. Verdict: pass
   as a decomposition, not as a closed proof.
3. Read `IsKoszulConormalComparison`, the signed dual boundary, the genuine
   exterior Koszul construction, and `exists_koszul_conormal_basis`.
   Read [Stacks Tag 0BQZ](https://stacks.math.columbia.edu/tag/0BQZ),
   lemma-regular-immersion-ext, especially its complementary contraction
   calculation and quotient map on top cohomology, and
   [Tag 062I](https://stacks.math.columbia.edu/tag/062I),
   lemma-H1-regular-quasi-regular, first paragraph giving the conormal basis.
   The finite-ring statements implement that local calculation and allow
   r=0 and I=A. For r=0, I=0, the empty wedge is 1, normalization forces
   the identity and there is no incoming differential. For r=1 the complex
   is A --(-f_0)--> A: Koszul-regularity makes f_0 injective and the top
   cokernel is A/(f_0). For I=A the quotient and normal determinant are zero
   and the Koszul complex is contractible (a linear combination of f_i is 1).
   The zero ring and characteristic two introduce no exception. Construction
   needs the conormal basis but not the cohomological argument; the criterion
   assumes a map and needs only self-duality and its top normalization. These
   are true, distinct strict parts of the argument. Re-ran LeanFinder with
   different words, Loogle for QuasiIso and single complexes, Mathlib grep,
   and LeanSearch (unavailable, recorded as such). Grepped this library and
   slopmaster2: Mathlib has the determinant evaluation formula but no
   Koszul comparison; the stronger library theorem imports this item and
   cannot be used without a cycle. Verdict: pass after documentation repairs.
4. The target reduction directly combines construction and the homological
   criterion. No shorter acyclic upstream theorem was found. Signature imports
   remain public and proof dependencies private. Listed every replaced old
   direct dependency above, with no false pruning claim. Read the unit record:
   its `realized` field is empty and unchanged; no unit-level node or route is
   bypassed. The decomposition stays under its diagonal Koszul calculation.
   Neither split hole was closeable in a few minutes with the current interface.
   Verdict: pass as a decomposition.
5. Checked the original and delivered nodes against every declaration. The
   target step obtains phi from the map node and uses the criterion on phi,
   exactly as Lean does. Replaced generic split steps by actual construction,
   differential, determinant, and cohomology steps; their proof_deps are exactly
   the unions of uses. New records have complete source, creation, chapter,
   unit, signature, search and blueprint fields. Removed spurious copied review
   metadata. Blueprint search for Koszul found no matching imported statement;
   the ancestor helper's created.item chain is broken by module-valued entries,
   so the existing parent blueprint records identify lem-sc-finite-duality and
   the specific diagonal Koszul calculation. Verdict: pass after node repairs.

Changes by this second reader: completed both split docstrings and module
source headers; added the existing conormal-basis proof dependency privately;
repaired new-node statements, exact proof steps, dependencies, verbatim Lean
signatures, blueprint provenance and actual search records; removed inherited
review stamps; corrected the decomposition count and pruning report. The
existing theorem proof and all theorem signatures are unchanged.
