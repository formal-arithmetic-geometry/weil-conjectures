## What changed

Proved the four additive multiplication laws in
`Sheaf.AlgebraicGeometry.InvertibleSectionRing`: `sectionRing_mul_zero`,
`sectionRing_zero_mul`, `sectionRing_mul_add`, and `sectionRing_add_mul`.
Each proof unfolds graded multiplication and applies the existing tensor-section
zero or additivity lemma, then additive map preservation.

The second reading also proved `sectionRing_gradedMonoid` using
`DirectSum.of_mul_of`, and `sectionRing_isInternal` using the bijective
componentwise range restrictions of the direct-sum inclusions. No imports,
statements, definitions or declaration visibility changed. Updated
`dag/nodes/sec-curve-estimates/def-sc-invertible-section-ring.json` in the
stage-3 proof fields to describe the actual partial proof and remaining holes.

## Proved and sorry left

Closed six original holes, by declaration name:
`AlgebraicGeometry.Scheme.Modules.sectionRing_mul_zero`,
`AlgebraicGeometry.Scheme.Modules.sectionRing_zero_mul`,
`AlgebraicGeometry.Scheme.Modules.sectionRing_mul_add`,
`AlgebraicGeometry.Scheme.Modules.sectionRing_add_mul`,
`AlgebraicGeometry.Scheme.Modules.sectionRing_gradedMonoid`, and
`AlgebraicGeometry.Scheme.Modules.sectionRing_isInternal`.

Added holes: none. Split-off statements: none. Four original holes remain:
`AlgebraicGeometry.Scheme.Modules.sectionRing_one_mul`,
`AlgebraicGeometry.Scheme.Modules.sectionRing_mul_one`,
`AlgebraicGeometry.Scheme.Modules.sectionRing_mul_assoc`, and
`AlgebraicGeometry.Scheme.Modules.sectionRing_mul_comm`.
All are recorded on node `def-sc-invertible-section-ring`, with their existing
Stacks-source docstrings and natural-language arguments intact.

The four additive laws and `sectionRing_isInternal` have only `propext`,
`Classical.choice`, and `Quot.sound`. `sectionRing_gradedMonoid` still has
`sorryAx` transitively through the section-ring monoid instance.
`sectionRingGCommRing` and `sectionRingGradedRing` likewise depend on the four
remaining multiplicative laws. Six explicit holes closed, zero added; this is
partial proof progress, not a complete proof of the section-ring construction.

## No longer needed

None. Both existing public imports are needed by the public definitions or
signatures: the tensor-section API specifies homogeneous multiplication and the
graded-algebra API supplies the grading classes. The old `proof_deps` was empty,
so no old proof-dependency node was pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's four proofs are correct. The node's empty `proof` and null
`proof_origin` did not describe the implemented proof, so the second reading
filled those fields without changing the node statement. The two original
grading holes have short proofs through the existing Mathlib direct-sum API.

## New nodes

None. No change records are necessary: every existing signature and definition
is unchanged.

## Second reading by W2

1. Compared the complete delivered module with the repository version using
   `diff`, and checked the declaration diff with the project's parser. Pass:
   only six theorem proof bodies differ; all existing signatures, definitions,
   docstrings, imports and visibility are byte-for-byte unchanged.
2. Compiled the module locally through `lcompile.py` without errors or warnings.
   In a scratch copy, ran `#print axioms` on all 17 declarations. Pass: only
   `propext`, `Classical.choice`, `Quot.sound`, and the expected transitive
   `sorryAx` occur. The only explicit sorries are the four listed original named
   theorems. No forbidden declarations or hollow definitions occur. The existing
   choice of decomposition is justified by a bijection, determining its inverse
   uniquely; that bijection is now proved.
3. No new or split-off statements exist. Pass: the unchanged remaining holes
   have their original source/proof docstrings and node. Checked the upstream
   tensor-section proofs and searched Mathlib's direct-sum, graded-monoid and
   decomposition APIs and `lean/` using alternative terms (range restriction,
   internal direct sum, homogeneous products). Reused the existing API rather
   than introducing any duplicate theorem. Degree zero, zero sections, the empty
   scheme and zero summands cause no exceptional cases in the implemented proofs.
4. Pass: the four original proofs already use the shortest direct tensor-section
   reductions. Closed both grading holes using existing Mathlib results. Both
   imports remain necessary, and the pruning report covers the empty old
   `proof_deps`. Read `dag/units/sk-thm-curveestimate.json`: its realized statement
   is `thm-sc-proper-cohomology`; this auxiliary construction changes no unit step
   or route, and no unit realization was bypassed.
5. Pass after repair: the existing node's `proof`, `proof_deps` and `proof_origin`
   now describe the six implemented proofs, the four remaining laws, and the
   packaging of the explicit operations. No statement fields or unit records
   changed, and no new nodes are required.

Second reading changed: closed `sectionRing_gradedMonoid` and
`sectionRing_isInternal`; synchronized node proof metadata; corrected the report
from four to six holes closed and from six to four remaining. Retained the first
worker's four correct proofs verbatim.
