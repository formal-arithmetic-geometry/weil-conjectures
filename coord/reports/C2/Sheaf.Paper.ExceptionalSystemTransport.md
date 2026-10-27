## What changed

Replaced the single sorry in AlgebraicGeometry.exceptionalSystemTransport by a reduction
which constructs the origin adjunctions explicitly. The private Hom equivalence composes
the fully faithful inclusions, the canonical comparison, the two site adjunctions and
the etale adjunction. Both inverse laws, both naturality laws and the required transpose
normalization are proved in Lean. The same construction supplies every finite adjunction.
The proof also establishes right origin stability, the origin comparison isomorphism,
preservation of normalization and the common lower bound, then assembles all twelve
transport coherence clauses.

Four separate sourced geometric/evaluation statements have been isolated in new modules.
None repeats the original conclusion: they respectively construct the site equivalence,
construct proper/open comparison without any new exceptional adjunction, supply exactness
and scalar structures, and identify evaluations of already given adjunctions. No data is
chosen from an unproved existence theorem inside a definition: all existential elimination
is inside the proof of the original theorem.

The pre-existing definitions move unchanged from ExceptionalSystemTransport into the
unclaimed ExceptionalSystemInterfaces, preserving the latter's alias and public interface
import. ExceptionalSystemTransport publicly reexports them. This is necessary to import the
four lower statements without a cycle. The two existing definition ownership nodes are
rebound to their new file. Local priority and opacity annotations cache existing
site-size and sheafification proofs during elaboration; the public data and signatures are preserved.
See coord/changes/exceptional-system-interface-extraction.md for the verbatim before/after
blocks and the complete consumer list. No WeilConjectures source module is modified.

## Proved and sorry left

The original module had one hole, AlgebraicGeometry.exceptionalSystemTransport. Its body
now has zero sorry and is proved from the four named lower statements. This is a
DECOMPOSITION: one upper hole closed, four holes added, net minus three holes, not a
claim that the whole geometric theorem is now axiom-free.

The private CategoryTheory.reverseHom, originEquiv, originEquiv_left, originEquiv_right,
originAdjunction, originAdjunction_transpose and makeOriginAdjunction are fully proved or
constructed without holes. The private exceptionalSystemRight_lowerBound and
exceptionalSystemRight_normalized are fully proved from the recorded etale clauses and
the site equivalences.

Every remaining sorry in the delivery is a sole public theorem body in its own module:

- AlgebraicGeometry.exceptionalSiteOriginComparison:
  lem-sf-exceptional-site-origin-comparison.
- AlgebraicGeometry.exceptionalProperOpenOriginComparison:
  lem-sf-exceptional-proper-open-origin-comparison.
- AlgebraicGeometry.exceptionalProOriginExactLinear:
  lem-sf-exceptional-pro-origin-exact-linear.
- AlgebraicGeometry.exceptionalOriginAdjunctionEvaluation:
  lem-sf-exceptional-origin-adjunction-evaluation.

All four have a source and complete proof plan in their docstring. There is no new axiom,
hollow definition, changed target, or private admitted theorem.

Validation: all six delivery modules compiled together, including the complete main
proof and the unchanged interface definitions. The corrected main proof also compiled
alone in 18.3 seconds. The set check emitted one long-line warning in the proper/open
lemma's docstring; that line is wrapped in the current source. An intermediate experiment
with a general smallness-instance priority was discarded; explicit proved site-size
caches compile. The compile service supplied the unpublished StrictEtaleExceptionalAdjointInterfaces
dependency in its private overlay.
Three byte-identical consumer copies were checked as an auxiliary set; the compile service
failed while rebuilding the unrelated dependency ExceptionalReconstructionPresentations,
because its published ExceptionalSystemTransport.olean was absent. Those unchanged copies
were removed from the delivery packet. This is a validation limitation, not a consumer
adaptation or evidence that their statements changed.

## No longer needed

The following original private proof imports are removed from the item. Some remain
mathematically needed within the new geometric lemmas' plans: this extraction does not
claim that their modules are globally pruned.

- `Sheaf.Paper.EtaleSystemBrownConstruction`
- `Sheaf.Paper.EtaleSystemEvaluationBound`
- `Sheaf.CategoryTheory.ExactDerivedAdjunctionBounds`
- `Sheaf.Paper.SemilinearDerivedSections`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.CategoryTheory.SystemDerivedEvaluation`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
- `Sheaf.Paper.EtaleProEtaleScalarPullbackCube`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.CategoryTheory.Adjunction.Basic`
- `Mathlib.CategoryTheory.Adjunction.Mates`

The original top-level tool approvals are withdrawn from this node because its Lean proof
uses the four new declarations instead. The corresponding lower-node plans retain the
relevant dependencies. The natural-Hom-bijection step itself is now proved directly using
Mathlib Adjunction.mkOfHomEquiv, so it does not use the project's generic bijection theorem.
The withdrawn approval entries are:

- `lem-weil-pbc-comparison-pullback`
- `lem-weil-pbc-comparison-direct-image-canonical-mate`
- `thm-weil-pbc-site-comparison`
- `lem-pur-system-derived-evaluation`
- `lem-pur-exact-derived-adjunction-bounds`
- `lem-weil-pbc-adjunction-of-natural-bijection`
- `lem-sfb-etale-proetale-scalar-pullback-cube`
- `lem-weil-pbc-mate-pasting`
- `lem-sf-exact-functor-derived-triangulated`
- `lem-pc-right-derived-functor-triangulated`

No existing mathematical module or node is withdrawn. No blueprint unit route is bypassed.
The unit sk-thm-sf-compatibility has no realized step list to replace. The theorem and all
its statement dependencies are unchanged.

## Where the brief, the DAG or earlier work was wrong

The DAG's construction steps describe several nontrivial system-level constructions that
are not the statements of the cited finite-level tools. The finite site comparison theorem
is on fixed-ring module sheaves; the actual strict-system comparison must additionally be
constructed at the already chosen evaluations. The finite normalized descent package
assumes absolute separatedness of the schemes and thus cannot replace this theorem, whose
hypothesis only separates f. The new statements record those missing portions explicitly.

The earlier interface split was reverted because the landing declaration index rejected
an intra-delivery relocation. This packet records the actual relocation and definition
ownership changes rather than duplicating names; its acceptability must be checked by the
current delivery tool and independent reader. It is needed to avoid an import cycle.

Edge cases checked when formulating the new statements: level zero means exponent one;
the zero quotient ring and empty scheme do not require a nonzero coefficient hypothesis;
identity compactification reduces comparison to site triangles; no absolute separatedness
of X or Y is introduced; quotient transposes are in unbounded categories, so no quotient
flatness or bound on an intermediate tensor is assumed. Equality of derived system maps
is never inferred solely from equality of all evaluations.

## New nodes

lem-sf-exceptional-site-origin-comparison isolates bounded-below actual site comparison
at fixed etale evaluations, including finite origins, units/counits and normalization.
It is step 2 of the original argument, sourced to Zheng Construction 4.1 and Lemma 4.10.

lem-sf-exceptional-proper-open-origin-comparison isolates construction of ordinary/derived
pro-etale open support, the canonical proper/open mate, origin stability and its evaluation.
It supplies no exceptional adjunction. Sources: Zheng Construction 5.15 and Lemmas 4.10,
5.16 and 5.22.

lem-sf-exceptional-pro-origin-exact-linear isolates triangulated and scalar-linear
structures on the two actual functors, independently of existence of any restricted
adjunction. Sources: Zheng Proposition 2.29(2), Construction 5.15 and Lemma 5.22.

lem-sf-exceptional-origin-adjunction-evaluation isolates the evaluated unit, counit and
quotient word for already constructed origin adjunctions. Sources: Zheng Lemmas 4.10,
5.22 and Proposition 5.24; Stacks 0B65. No comparison equivalence or adjunction is
constructed by this statement.

Change record: coord/changes/exceptional-system-interface-extraction.md.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
