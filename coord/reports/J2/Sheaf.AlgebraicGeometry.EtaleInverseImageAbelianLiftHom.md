## What changed

Proved AlgebraicGeometry.etaleInverseImageAbelianLift_hom with its signature unchanged.
The proof uses Mathlib Adjunction.mapCommGrp directly, transports the lifted adjunction
using fully faithful equivalences, constructs the underlying natural isomorphism, and
proves the hom-set equation using the restriction formula, naturality, and adjoint uniqueness.
Added Sheaf.AlgebraicGeometry.EtaleAbelianDirectImageInternal for the remaining direct-image
square. Updated the parent DAG proof and dependencies to match the Lean argument.
All added proof imports are non-public; the original public imports and interface are kept.
Both modules compile locally. The final delivery dry run supplies the server check and probes.

## Proved and sorry left

Hole closed by reduction: AlgebraicGeometry.etaleInverseImageAbelianLift_hom
(node lem-weil-pbc-etale-inverse-image-abelian-lift-hom). No sorry remains in the item's module.

The delivery leaves exactly one new sorry:
AlgebraicGeometry.etaleAbelianDirectImageInternal
(node lem-weil-pbc-etale-abelian-direct-image-internal).
This isolates the equivalence and right-direct-image square from steps 2–3 of the original
plan. It mentions neither inverse image nor the finite-limit hypothesis on inverse image.
The parent constructs the left lift, its adjunction and comparison, and proves the equation;
the new theorem is not a renamed or repackaged version of the parent theorem.
Existing sheavesAlgebraicStructuresAbelian remains the intended dependency for the new item.

Accounting: one old hole closed and one new hole added. This is a decomposition,
not a completed axiom-free proof; the local hole-count net is zero. Any progress
from pruned modules is for the pinned-baseline sorry ledger to determine.

## No longer needed

Removed the proof imports Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects and
Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects. Used Mathlib Adjunction.mapCommGrp
and the abelian component instead of the combined group/ring interfaces.

The following modules are absent from this item's new import closure (other targets or
modules may still need them):
- Sheaf.CategoryTheory.Adjunction.FiniteProductRingFunctor
- Sheaf.CategoryTheory.Adjunction.LiftedCommGrpBranch
- Sheaf.CategoryTheory.Adjunction.LiftedCommRingBranch
- Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
- Sheaf.CategoryTheory.Adjunction.RingHomEquivCore
- Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
- Sheaf.CategoryTheory.SheavesAlgebraicStructuresRing
- Sheaf.CategoryTheory.SheavesAlgebraicStructuresRingCore
- Sheaf.CategoryTheory.SheavesAlgebraicStructuresRingMorphism

Their corresponding nodes no longer used on this route are:

- lem-weil-pbc-adjunction-lifts-group-ring-objects
- lem-weil-pbc-finite-product-ring-functor
- lem-weil-pbc-lifted-comm-group-branch
- lem-weil-pbc-lifted-comm-ring-branch
- lem-weil-pbc-ring-hom-equiv-core
- lem-weil-pbc-sheaf-algebraic-structures-objects
- lem-weil-pbc-sheaf-algebraic-structures-ring-component
- lem-weil-pbc-sheaf-algebraic-structures-ring-core
- lem-weil-pbc-sheaf-algebraic-structures-ring-morphism

The abelian identification component is retained through the new direct-image item.
The continuity, site definitions, and recorded inverse/direct-image definitions remain used.
The blueprint unit sk-def-exchange has no proof steps realized by this helper; its statement
realizations are unchanged, so no unit route was bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement correction is needed. Mathlib already implements the commutative-group lift
with its underlying unit and counit, so the larger group/ring theorem is unnecessary here.
The remaining direct-image transport was not supplied as a separate declaration by the
original dependencies; it is now an explicit smaller item rather than hidden glue.

The abelian-component DAG node currently cites the combined algebraic-structures node,
while the combined node's proof cites the abelian component. Their Lean import direction is
acyclic, but these recorded proof dependencies form a pre-existing DAG cycle. This delivery
does not edit either node; the maintainer should reconcile that existing metadata.

The recorded sites.tex is absent from this local clone. Read the primary source online:
https://stacks.math.columbia.edu/tag/00YV and https://stacks.math.columbia.edu/tag/00X2.
LeanSearch returned Internal Server Error and was recorded as unavailable. LeanFinder,
Loogle and Mathlib grep ran successfully, and found the generic categorical tools rather
than the coefficient-specific direct-image square. Blueprint searches for 00YV and abelian
inverse image found no duplicate. The ancestor tool prints None because created.item is a
module name; the new node uses the parent's explicit blueprint ancestor and route.

## New nodes

lem-weil-pbc-etale-abelian-direct-image-internal, in
lean/Sheaf/AlgebraicGeometry/EtaleAbelianDirectImageInternal.lean: sectionwise equivalences
between abelian sheaves and internal commutative group objects, together with the natural
right-direct-image square and its precise underlying equation. Its proof docstring describes
both directions of the comparison and naturality. Edge cases checked in words: f need not
be etale; identity f gives the same sectionwise operations on both sides; the zero sheaf and
empty scheme/site have the same singleton group operations and no extra nonempty-section
assumption is used. Universes are exactly u+1 on both coefficient and set sheaves. No change
record is needed: no existing definition, statement or public import is changed.


## Second reading by J2

1. Interface preservation: PASS. Compared the entire existing module with the
repository version using diff, and programmatically compared the theorem signature
byte for byte. The signature and existing docstring are unchanged; no definitions,
targets, hypotheses or conclusions changed. The parent node differs only in proof,
proof_deps and proof_origin. No applicable open change record names this item.

2. Proof and trust: PASS. Both modules compile cleanly through lcompile.py.
The parent contains no sorry; the sole added sorry is the named public theorem
AlgebraicGeometry.etaleAbelianDirectImageInternal. There are no definitions with
holes and no forbidden declarations or kernel bypasses. Scratch-copy #print axioms
checks show only propext, Classical.choice, Quot.sound and sorryAx. The last axiom
is expected from the explicitly open direct-image theorem; the parent is therefore
a proved reduction, not yet an axiom-free theorem. Read the construction of Lt,
q, gamma and ea, the restricted homEquiv calculation, and the unit compatibility
of leftAdjointUniq; each has the correct direction and matches the final equation.

3. Split statement: PASS. Read the new statement, complete proof docstring, node,
and the existing abelian-component theorem. The new statement is strictly the
right-adjoint square, independent of inverse image and its finite-limit hypothesis;
it does not restate the parent. Checked the source at Stacks 00YR and 00YV and the
actual lowerStar definition and section formulas. Products, terminal objects and
operations are sectionwise, so the underlying comparison preserves addition and
zero and its inverse does too. Negation follows from the group laws; faithfulness
proves naturality. Identity f, the zero sheaf and empty schemes introduce no extra
assumption. Repeated searches using pushforward/precomposition terminology via
LeanFinder, Loogle and Mathlib grep, plus local rg and reading the generic site
pullback theorem, found no exact square. Mathlib mapCommGrp and its adjunction are
already used; the remaining sectionwise transport is not a few-minute closure.

4. Route and pruning: PASS. The proof takes Mathlib's direct commutative-group
lift and fully faithful restriction before introducing any new hole. Both old
proof dependencies removed from proof_deps are named under No longer needed,
together with the extra modules on their discarded ring route. The abelian
component is retained as the intended proof dependency of the new module.
Read dag/units/sk-def-exchange.json: its realized statement nodes and empty proof
step list are preserved; no blueprint unit route is bypassed. Tested removing
Sites.Adjunction from the new module: compilation fails because sheafForget is
needed in the statement, so restored the necessary public import. All added
proof-only imports are plain imports.

5. Node agreement: PASS. Checked both proof_deps arrays against the union of
proof-step uses, the new node's verbatim Lean signature, its source, creation,
blueprint, chapter, unit, status and search fields. The parent proof steps match
the actual Mathlib lift, direct-image square, restriction, naturality and adjoint
uniqueness argument. The pre-existing abelian/combined metadata cycle remains
reported above and is outside this delivery.

Changes by the second reader: clarified Proved and sorry left to count one closed
hole and one added hole as a decomposition with local net zero; added this review.
No Lean proof, statement, definition, final import or node changes were necessary.
