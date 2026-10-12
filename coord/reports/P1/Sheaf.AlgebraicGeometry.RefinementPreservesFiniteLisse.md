## What changed

Proved `AlgebraicGeometry.Scheme.refinement_preserves_finite_lisse` without changing its
statement or public imports. Added proof-only imports of EtaleSetInverseImageRestriction,
EtaleSetInverseImageStalkGerm and EtaleSetInverseImageCompositionUnits. Added five fully
proved private helpers for constant inverse image, localized restriction, locally constant
inverse image, constant descent, and locally constant descent; an additional private helper
transports a trivializing cover along a sheaf isomorphism. Updated the node proof to describe
the actual argument. There are no new public declarations or new nodes.

The proof uses the fibre product rather than claiming that image containment factors one
immersion through the other. Its first projection is a surjective closed immersion. Local
constancy is pulled back along the second projection, transported across the square and
descended along the first. Finiteness is proved independently by lifting each geometric
point and transferring finite instances through both stalk comparisons and the square
isomorphism. The constant-sheaf argument allows all sets in Type (u + 1), without reducing
the coefficients to ULift of a Type u set.

## Proved and sorry left

Proved the module's sole original sorry:
`AlgebraicGeometry.Scheme.refinement_preserves_finite_lisse`
(node `lem-weil-pbc-refinement-preserves-finite-lisse`). Every private helper is proved.
No sorry remains in the module and no sorry is added elsewhere.

Local compilation succeeded. The prescribed delivery dry run performs the additional
axiom probe, server compile and preflight checks.

## No longer needed

Removed redundant proof-only direct imports:
`WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`. Both are
already provided by the public Refinement import, and their declarations remain used.
None of the original proof-dependency nodes is pruned. The public
Refinement import is still required to state Stratification.Refines and supplies the
range-containment, closed-immersion and geometric-point-lifting lemmas. No module in the
original route is bypassed. The assigned unit has empty realized statement and step lists.
Two initially proposed set-valued local-constancy modules were fully proved and folded
into private helpers of the assigned module; neither is part of the delivery.

## Where the brief, the DAG or earlier work was wrong

The existing upstream refinement, local-constancy pullback and descent theorems require
abelian coefficients and cannot be specialized to Type (u + 1). Their arguments do extend
to sets, using the general constant-sheaf adjunction and the existing set-valued inverse
image comparison. The needed set-valued extension is now proved here, not left as another
sorry. The DAG did not list the restriction comparison, which the actual proof uses; it is
now included in proof_deps. Searches with LeanFinder and Loogle found no exact set-valued
preservation theorem; grep found the upstream abelian proofs and the general constant-sheaf
lemma. LeanSearch was unavailable (service Internal Server Error); other searches and
source inspection sufficed. Stacks Tags 095A and 03SI were read directly. Edge cases:
empty schemes and empty covers are admitted, no nonemptiness or finiteness of the
trivializing cover or constant coefficient sets is assumed, and no reducedness of strata
is needed.


## Second reading by P1

1. Compared the sole delivered Lean module against the repository with diff and checked
   the original theorem signature byte for byte by extracting the text before `:= by`.
   Verdict: identical; no existing definition, statement, or public import changed. The
   only added declarations are six fully proved private proof helpers. No change record
   is needed.
2. Independently compiled the module with lcompile.py: no errors or warnings. Scanned
   the delivered Lean text for sorry, axiom, unsafe, opaque, implemented_by, extern and
   skipKernelTC: none. Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.refinement_preserves_finite_lisse`: exactly propext,
   Classical.choice and Quot.sound, with no sorryAx. There are no delivered definitions
   and no hollow data. Verdict: the theorem is fully proved, including its dependencies.
3. No statements are split off and no new public statement or node is added. Read the
   six helpers: constancy transport uses actual sheaf isomorphisms, inverse image of
   constant sheaves works for all coefficient sets in Type (u + 1), and the descended
   etale family covers by surjectivity. The finiteness argument lifts each field-valued
   point through the surjective closed immersion and uses the two stalk bijections in
   the correct directions. Empty schemes/covers and empty or infinite constant sets
   introduce no extra hypotheses. Verdict: no unproved or restated auxiliary theorem.
4. Searched independently with LeanFinder for reflection of local constancy under site
   equivalence, Loogle for Sheaf.IsConstant (identifier unavailable in its index), and
   rg for constancy pullback/descent and isomorphism transport in both library roots.
   Inspected upstream Refinement, UniversalHomeomorphism and Pullback, and the set-valued
   PullbackFiniteLocallyConstant, EtaleLocallyConstantOpenPullback and
   EtaleConstantTrivializationPullback modules. No existing exact set-valued refinement
   theorem or shorter applicable general local-constancy theorem was found. The general
   Mathlib constant-sheaf results are already used; the upstream refinement/descent
   statements impose abelian coefficient hypotheses. Every retained direct import is
   used; the two removed direct imports are redundant through Refinement. All four old
   proof-dependency nodes remain used. Unit sk-prop-sf-cbc has empty realized.statement
   and realized.steps, and its route is unchanged. Verdict: pruning and route preserved.
5. Compared the delivered node with the original and read each proof step against the
   Lean proof. proof_deps is precisely the union of its steps' uses: the four existing
   dependencies plus the restriction comparison. The universal-homeomorphism instance,
   equivalence of sheaf categories, composition and stalk comparisons are all used.
   proof_origin describes the implemented upstream adaptation. The node's Lean signature
   agrees with the unchanged theorem. Verdict: metadata agrees; no new-node checks apply.

Changed only this report: corrected the list of removed redundant direct imports and
added this independent second-reading record. The Lean proof and DAG proof fields needed
no repair.
