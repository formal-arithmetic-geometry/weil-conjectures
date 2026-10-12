## What changed

Replaced the sorry in AlgebraicGeometry.serreSectionCoordinateSurjective by a complete
Lean reduction, preserving its signature and public imports. The proof takes the integer
Serre bound b, chooses N=(b+1).toNat, and proves z-1>=b by omega. It applies
Abelian.Ext.covariant_sequence_exact₃ to the coordinate short exact sequence after the
exact forgetful functor Scheme.Modules.toAb. Vanishing of the kernel's H1 kills the
boundary, so the H0 class lifts. H.zeroLinearEquiv and its naturality identify that lift
with a global section. The biproduct projections and biprod.desc_eq then give the two
coordinate preimages, using additivity and composition of Hom.app.

Added two separate modules for the geometric sequence and the Proj-model H1 vanishing
input. Their public theorem statements each have exactly one named sorry and a complete
source-based argument in their docstrings. Updated the item's DAG proof to match the
actual Lean combination; added the two matching nodes. No existing signature,
definition, visibility, or target changed. No forced adaptations.

The existing plan is retained: the coordinate sequence and Serre vanishing remain the
two mathematical inputs. The original unit record has no realized statement or steps
at this node; no blueprint unit route has been bypassed.

## Proved and sorry left

Closed: AlgebraicGeometry.serreSectionCoordinateSurjective
(node lem-sc-p1-section-coordinate-surjective). No sorry remains in the item's module.

Added: AlgebraicGeometry.exists_proj_coordinate_shortExact
(node lem-sc-p1-proj-coordinate-short-exact, module ProjLineCoordinateShortExact).

Added: AlgebraicGeometry.exists_subsingleton_H_one_tensor_proj_twist
(node lem-sc-p1-proj-serre-h1-vanishing, module ProjLineSerreVanishing).

This is a decomposition, not a completed axiom-free proof: one upper hole was closed
and two strictly separate geometric holes were added. The vanishing theorem has no
section-surjectivity conclusion. The sequence theorem has no coherence hypothesis,
no eventual bound, and no claim of surjectivity on global sections. The connecting
argument is fully proved in the item's Lean module.

Edge cases checked mathematically: G=0 satisfies both new statements. The geometric
sequence is split locally for every integer z and every G, including nonflat G.
For G=O and z=-1, the sequence is still short exact, while H1(O(-2)) is nonzero, so
it correctly does not imply the false lifting of constants from O(-1). For G=O,
H1(O(d)) vanishes for d>=-1. Negative integer bounds remain valid: choosing the
natural toNat of b+1 still ensures z-1>=b, even if b+1<0. All field characteristics
use the same two local splittings.

## No longer needed

Removed the direct proof imports:

- Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
- Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist
- Sheaf.AlgebraicGeometry.ProjectiveLineTwistExists
- Sheaf.Paper.PQFCohomology
- WeilConjectures.AlgebraicGeometry.Cohomology.Serre
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
- WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

The coherence, shifted-free comparison, twist existence, Serre and projective-space
twist imports are retained as the proof plan dependencies of ProjLineSerreVanishing;
they are not globally pruned. Twist.Modules is already reexported by the unchanged
public Twist import. The Proj tensor addition theorem is already available there.

The unused delta-functor comparison theorem
AlgebraicGeometry.sheafCohomologyAndHigherDirectImages, its node pqf-def-cohomology,
and its proof module Sheaf.Paper.PQFCohomology are not required by the actual section
lifting proof: it uses the existing Ext-based Scheme.Modules.H directly. The node
still records the mathematical meaning of cohomology in the new vanishing statement,
but its comparison theorem is not a proof dependency. Whether any removed module
leaves the whole targets' closure is for the maintainer's ledger to determine.

## Where the brief, the DAG or earlier work was wrong

The original DAG marked the entire coordinate-sequence construction elementary, but
its listed declarations do not state that sequence for arbitrary G. In particular,
tensoring it requires local splitting, not a flatness assumption. This missing geometry
is now one explicit theorem with its two local splitting computations documented.

The recorded Serre theorem is on relative ProjectiveSpace with ProjectiveSpace.twist;
it does not directly apply to polynomial Proj with Proj.twist. The model comparison
and coherence transport are isolated in the H1 vanishing theorem. The existing
ProjShiftedFreeTwist and ProjectiveLineTwistExists statements remain its planned inputs.
The original PQFCohomology statement concerns RingedSpace.moduleCohomology, whereas
the ready-to-use H0/Ext exactness declarations concern Scheme.Modules.H. Using these
existing declarations directly avoids an unnecessary comparison theorem.

LeanFinder found only unrelated projective or algebraic exactness statements; the
Mathlib grep found no matching coordinate or Serre-vanishing theorem. LeanSearch
returned Internal Server Error and is recorded as unavailable, not as a negative
mathematical search. Blueprint searches for coordinate surjectivity, Serre vanishing,
and split exactness found no existing coordinate sequence node; the existing relative
Serre theorem was read and retained. The ancestor helper reported no ancestor for the
item even though its recorded blueprint.from names lem-sc-p1-graded-resolution; the
new nodes follow that recorded ancestor and its finite-generation proof clause.

## New nodes

lem-sc-p1-proj-coordinate-short-exact: tensoring the locally split coordinate sequence
with G(z) gives a short exact sequence with the prescribed coordinate quotient map.
This is the geometric input only, valid in all degrees without coherence or flatness.
Its source is the original item's coordinate-sequence argument and Stacks 01MN for
the twisting sheaves. Each standard chart supplies a written right inverse and kernel.

lem-sc-p1-proj-serre-h1-vanishing: eventual H1 vanishing for coherent G in the polynomial
Proj model. This isolates the model/twist comparison and coherence transport needed
to specialize the existing Serre theorem. Source: Stacks 01YS (4), 01MN (1),(2), and
step 2 of the original item's proof. Neither new node restates the item's conclusion.

No change record is needed: no existing interface or definition was changed.

## Second reading by R3

1. PASS — Compared the item module against the read-only repository with `diff -u`.
   Its existing theorem signature, docstring, visibility, and all three public imports
   are byte-for-byte unchanged. The only changes are proof imports and the proof body.
   The two other modules are new; there are no definitions or forced adaptations.
2. PASS — Compiled all three delivered files using lcompile.py. A scratch copy with
   `#print axioms` for all three declarations reports only propext, Classical.choice,
   Quot.sound, and sorryAx. Exactly the two named input theorems contain sorry; there
   are no forbidden declarations or hidden data definitions. The existential sequence
   witness is eliminated inside a proof, never chosen to define an object.
3. PASS — Read both split statements and their complete docstring arguments. The
   coordinate sequence is locally split for arbitrary G, so tensoring needs no flatness.
   On the second chart its kernel vector is (-1,x0/x1), including characteristic two.
   G=0 and negative twists satisfy the same calculation. For G=O and z=-1, H1(O(-2))
   need not vanish, so no false low-degree lifting follows. The H1 statement is the
   q=1 specialization of Serre vanishing after the stated model comparison; it imposes
   coherence and an eventual integer bound. Verified Stacks 01YS (4) and 01MN (1),(2)
   online. Additional LeanFinder searches for a Koszul sequence of two generating
   sections and for eventual first-cohomology vanishing on polynomial Proj returned
   no matching theorem. Mathlib grep for Koszul, eulerSequence, coordinate_short and
   H_one_tensor_proj returned no applicable result. Inspected the existing Proj twist
   maps, shifted-free comparison, TwistData uniqueness, and relative Serre theorem:
   none directly states either input. Neither input is a renamed copy of the target.
4. PASS — Followed the proof downward: integer bound, Ext exactness, H0 naturality,
   biproduct projections. Each private import supplies a used declaration; the new
   modules' public imports support their signatures. The new inputs retain their
   stated proof-plan imports. No evident shorter existing route was found. The unit
   sk-thm-picard-duality has empty realized statement and step lists; no realized node
   is bypassed. All old direct proof dependencies are now absent from the item's
   proof_deps: def-weil-pbc-proj-twisting-sheaf, lem-pc-twist-tensor,
   lem-pc-projective-space-serre-vanishing, lem-sc-p1-proj-shifted-free-twist,
   lem-sc-p1-twist-exists, pqf-def-cohomology, pqf-lem-coherent-ft-locnoeth.
   The twist definition remains in the item's public interface; twist tensor addition
   remains an input to the coordinate node; Serre, shifted-free comparison, twist
   uniqueness and coherence transport remain inputs to the vanishing node.
   Only the unused cohomology-comparison proof dependency is discarded altogether;
   no whole-target-closure pruning is claimed without the maintainer's ledger.
5. PASS — Read the three delivered JSON nodes against the Lean declarations and the
   original item node. The original node changes only proof, proof_deps and proof_origin.
   Its two dependencies are precisely the two new theorems used. Each new node records
   its statement, source, proof steps, dependency union, searches, split status,
   provenance, chapter/unit, and verbatim Lean signature. The sequence and vanishing
   nodes describe strictly separate parts of the argument, with no section lifting
   asserted in either one.

Second-reading changes: added this review and made the removed-dependency accounting
explicit above. No repair to the Lean proof or statements was necessary. One original
hole is replaced by two lower holes: this delivery is a decomposition (net -1 holes
closed before any closure pruning), not an axiom-free proof of the target.
