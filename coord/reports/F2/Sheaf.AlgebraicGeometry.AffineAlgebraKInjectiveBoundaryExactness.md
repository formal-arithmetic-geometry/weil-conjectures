## What changed

Replaced the sorry in AlgebraicGeometry.affine_algebra_kinjective_boundary_exactness
with a complete categorical assembly from a proved generic truncation lemma and one strictly simpler affine intermediate
statement. The original signature and public imports are unchanged. Added proof
imports of AffineAlgebraUpperTruncationEdge and RingedSpaceModuleEnoughInjectives.

LeftExactUpperTruncationComparison constructs mapped left homology data using an actual
cokernel of the mapped differential into cycles. It constructs the derived unit on
complexes and a specified comparison from that cokernel to derived homology of upper
truncation. All data are real constructions; the inverse in the comparison is uniquely
determined by the asserted invertibility. The naturality argument proving invertibility
of the upper-truncation unit for K-injective I is complete Lean.

AffineAlgebraUpperTruncationEdge proves preservation of finite limits by direct image
from its sectionwise definition, and states the affine derived edge calculation, including
its equality with the actual homology class map. The final proof identifies cokernel.desc
with the composite of two isomorphisms, proves it monic, and uses Mathlib's exactness
criterion. No witness of an unproved mere-existence statement is used to define data.

## Proved and sorry left

Closed: AlgebraicGeometry.affine_algebra_kinjective_boundary_exactness
(new-affine-algebra-kinjective-boundary-exactness), 1 of 1 original holes.

Proved in the new generic module:
CategoryTheory.Functor.upperTruncation_raw_comparison,
CategoryTheory.Functor.upperTruncation_derived_comparison,
CategoryTheory.Functor.upperTruncation_comparisons, and
CategoryTheory.Functor.isIso_complexDerivedUnit_upperTruncation
(lem-sc-left-exact-upper-truncation-comparison). The raw proof transports cycles through
preserved kernels and uses a diagram lemma; the derived proof uses the truncation
triangle, bounded-below/unbounded compatibility, and negative vanishing.

Added hole (the only sorry in the delivery):
AlgebraicGeometry.affine_algebra_upper_truncation_edge
(lem-sc-affine-algebra-upper-truncation-edge): affine derived edge isomorphism and its
cycle formula, without K-injectivity.

This is a decomposition, not a sorry-free proof: 1 original hole closed and 1 lower hole
added. All assembly, generic comparisons, definitions, and finite-limit preservation
are complete Lean. The edge does not assert exactness of the pushed boundary complex:
that requires the K-injective unit argument proved here. Its object is derived homology
of upper truncation and it has no K-injectivity hypothesis, so is not a renamed original
statement.

## No longer needed

Removed redundant proof imports from the new generic module:
WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
(already publicly reached through PlusCompatibility/PlusSingle), and
WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus (no declaration of it
is used). No modules are claimed globally pruned. The original seven direct
proof dependencies are no longer direct dependencies of the item's proof: affine
vanishing, module/source comparison, the unbounded bound, single-object identification,
K-injective definition, K-injective resolutions, and restriction to opens. The first
four still support the new affine edge. K-injective resolutions remain in the public
interface and provide instances; restriction to opens is not required in this route,
because the affine edge is formulated without K-injectivity and the unit argument is
performed globally. The item's node now records its two actual intermediate dependencies.
No blueprint unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing abstract affine cohomology isomorphism has no equality relating it to the
raw cycle-class map, so cannot prove the desired exactness by itself. The proof uses
an edge with the requisite formula rather than treating an unrelated isomorphism as
canonical. The original node's Step 3 combines several substantial arguments; the
naturality square separates its genuinely generic K-injective part from the affine
edge calculation.

The local Stacks TeX files are absent on this machine. Read official tag pages 05TC,
08D4, and 0AVW; source records retain the project's source document identifiers.
LeanSearch returned Internal Server Error; recorded as unavailable, not as no match.
The blueprint ancestor command returned None for this module-created node; new nodes
inherit the explicit existing blueprint ancestor lem-sc-finite-duality and its via chain.

## New nodes

lem-sc-left-exact-upper-truncation-comparison: generic raw and derived comparison for
upper truncation, now proved completely in Lean, with source, proof in words, recorded
searches, and Lean signature.

lem-sc-affine-algebra-upper-truncation-edge: the derived affine edge and its cycle-class
formula. Its domain is derived homology, and no K-injectivity is assumed. Source and
proof follow the original affine calculation with bound one. Zero complexes, empty
opens, and every integer degree satisfy both statements; no boundedness is assumed.
No interface changes or forced adaptations, hence no change record is needed.


## Second reading by F2

1. Compared the existing module with the repository using diff. The theorem's
signature, hypotheses, conclusion and docstring are byte for byte unchanged.
The only changes there are two private proof imports, a local elaboration option,
and the proof body. The other two modules are new; no existing definitions or
interfaces are changed, and no change record is required. Verdict: pass.

2. Compiled all three modules in import order using lcompile.py after repairs:
2.9 s, 6.3 s and 10.9 s respectively, with no errors or warnings. Searched every
delivered Lean file for sorry and forbidden constructs: the only sorry is the
public named affine_algebra_upper_truncation_edge, with its source, full proof
in words and node. Scratch-copy #print axioms checks show only propext,
Classical.choice and Quot.sound for all seven public generic declarations and
for affineAlgebraDirectImage_preservesFiniteLimits. The affine edge and the
item additionally depend on sorryAx, as explicitly reported. mappedCyclesHomologyData
uses preserved kernel data and a real cokernel; complexDerivedUnit is a composite
of actual natural transformations; upperTruncationBoundaryComparison inverts a
specified map whose invertibility is proved. The existential edge witness is
eliminated only inside the theorem proof, never used to manufacture definition
data. Verdict: pass as a decomposition, not a sorry-free target proof.

3. Read official Stacks tags 0AVW, 08D4 and 05TC. The affine edge retains affineness
and quasi-coherence in every degree; the lower tail has upper bound n-1, so 08D4
with N=1 gives the necessary vanishing at n and n+1. The bottom identification
uses left exactness; the formula uses naturality for the quotient to the single
homology object, not an arbitrary abstract isomorphism. Removing K-injectivity
from this intermediate is valid because that assumption belongs to the separate
unit-invertibility argument. Tested the mathematical zero-complex and empty-open
cases (both sides and maps zero), complexes concentrated in degree n (ordinary
bottom comparison), and complexes concentrated in n-1 (the required degree-n
vanishing). All integer degrees and unbounded lower tails remain covered.
Independent searches used leanfinder with "Left exact functor maps cycles and
derived truncation cohomology comparison for affine pushforward of quasicoherent
complexes", loogle with "ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi"
(unknown identifier, not evidence of nonexistence), and grep with
"trunc.*(unit|comparison)|preserv.*cycles|cycles.*preserv"; also searched the
repository and upstream right-derived modules directly. The existing affine
sections comparison supplies an abstract natural isomorphism, but lacks this
cycle-unit formula and is for global sections on Spec, so cannot replace the
edge in one line. The existing truncation theorem is for bounded-below objects
and requires Grothendieck hypotheses, so does not replace the unbounded generic
statement. The affine edge is the only split-off hole; closing it requires the
remaining geometric comparison formalization, not a short local repair.
Verdict: true intermediate, strictly part of the argument, not a renamed item.

4. Read the generic kernel/cokernel proof, derived truncation triangle proof,
unit naturality square, and final exactness assembly in order. The final proof
cancels the cokernel projection, identifies cokernel.desc with a composite of
isomorphisms, and uses exact_iff_mono_cokernel_desc. No shorter applicable route
was found. Removed two redundant proof imports from the new generic module.
The HomologySequence public import is necessary because homologyFunctor and
homologyFunctorFactors are defined there and appear in public signatures/data;
a private-import experiment confirmed this and was reverted. The original
seven dependencies removed from the item's direct proof_deps are:
lem-pc-affine-vanishing, lem-sc-module-cohomology-source-comparison,
lem-pc-unbounded-derived-functor-cohomological-bound,
lem-sp-derived-functor-single-identification, def-pur-kinjective-complex,
prop-pur-kinjective-resolutions-exist, lem-sc-derived-k-injective-restrict-open.
The first four remain in the affine edge plan; resolutions and K-injectivity
remain needed for the generic unit argument. Only restriction to opens is
unneeded by this global route. No global module pruning is claimed. Inspected
dag/units/sk-thm-picard-duality.json: realized.statement and its sole step are
empty; this auxiliary module is not a realized unit step. The finite-duality
ancestor and affine derived-equivalence route are retained. Verdict: pass.

5. Checked all three node statements against their Lean signatures, proof steps,
proof_deps unions, sources, blueprint ancestry, chapter/unit and lean records.
Found and repaired a citation mismatch: the generic derived proof uses
F.rightDerivedFunctor.map_distinguished on the unbounded category, so its
triangulatedness dependency is lem-pc-right-derived-functor-triangulated,
whose declarations are in RightDerivedFunctor.Triangulated, rather than the
bounded-below lem-weil-pbc-derived-direct-image-triangulated. Negative vanishing
and PlusCompatibility match the other two dependencies. The existing item's
node correctly records the generic comparison and affine edge used by its new
proof. Verdict: pass after repair.

Second reading changed: removed two redundant proof imports and corrected the
unbounded triangulatedness node citation; no Lean statement or proof changed.
Source pages read: https://stacks.math.columbia.edu/tag/0AVW,
https://stacks.math.columbia.edu/tag/08D4,
https://stacks.math.columbia.edu/tag/05TC.
