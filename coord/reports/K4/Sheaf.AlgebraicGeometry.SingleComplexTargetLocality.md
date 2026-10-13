## What changed

Replaced the sorry in `AlgebraicGeometry.singleComplexBaseChange_targetLocal` with a
complete Lean reduction. The proof selects compatible affine neighbourhoods using
Mathlib, constructs the restricted cartesian square with `Scheme.Hom.isPullback_resLE`,
proves quasi-coherence of the two explicitly restricted complexes, applies `h_affine`,
conjugates its conclusion by the comparison isomorphisms, and applies the proved
`schemeDerived_isIso_of_openRestriction`.

Added `Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionComparison` with two real
constructions, `singleComplexOpenPullbackIso` and `singleComplexRestrictedCoefficient`.
The former uses the pinned tensor-pullback adjunction and left-derived counit and
`leftDerivedUnique`; the latter composes those open comparisons and the same derived
pullback composition comparisons used by `schemeDerivedBaseChangeMap`. Neither has a
sorry. The coefficient objects are exact restrictions and the coefficient morphism is
constructed, rather than chosen from an unproved existence statement. Only comparison
isomorphisms used to transport invertibility are existential in the remaining theorem.

All existing signatures and visibility are unchanged. A local unused-variable linter
option surrounds the existing theorem because the preserved nested affine-premise
binders `hK₀`, `hK₀'`, and `h_stalk₀` are proof hypotheses not referenced within that
premise's result. No dependency adaptation or statement change is required.

## Proved and sorry left

Closed: `AlgebraicGeometry.singleComplexBaseChange_targetLocal` (1 original hole).
Its proof is complete from the named restricted-comparison theorem and existing
quasi-coherence and locality declarations.

Added: `AlgebraicGeometry.singleComplexBaseChange_openRestrictionComparison`, exactly
`:= by sorry`, node `lem-pc-single-complex-open-restriction-comparison` (1 new hole).
This is a decomposition, not an unconditional proof: 1 closed, 1 added, net 0 holes.
The remaining theorem concerns restriction of fixed data for a fixed pair of opens.
It has no affine-base criterion premise, no isomorphism conclusion for the original
arrow, and no neighbourhood-selection or global-locality step. It asserts stalk
preservation and an equality up to two comparison isomorphisms for the explicitly
constructed restricted coefficient. Its docstring and node give the complete proof.

The private helper `qcoh_openRestriction` and both new definitions are fully implemented.
Both modules compile together with lcompile.py; the new module is below the 60-second
single-file limit. The delivery dry run is the final validation.

## No longer needed

Removed the direct proof imports `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`
and `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` from the target-locality
module. The direct-image comparison remains needed by the new comparison lemma.
The affine tensor/tilde module was also removed from the new module during second
reading: canonical pullback composition and the constructed exact open-pullback
comparison replace it. No claim is made that either module leaves the full target
import closure, which has other import paths.

The target-locality node now depends directly on
`lem-pc-single-complex-open-restriction-comparison`,
`lem-pc-derived-open-restriction-qcoh-iff`, and
`lem-sc-derived-open-restriction-detects-iso`.
Old proof dependency `lem-pc-affine-derived-pullback-tensor-tilde` is no longer used
by this reduction or its comparison proof plan. Old dependency
`lem-pc-restrict-derived-direct-image-open` is used only through the new comparison
node; `lem-sc-derived-open-restriction-detects-iso` remains a direct dependency.
No entire module is certified pruned from the full target closure. Source-open
Mayer--Vietoris is not used by this reduction. The unit's realized route is preserved;
its `realized` lists are empty and this item remains on the parent qcqs induction route.

## Where the brief, the DAG or earlier work was wrong

The listed functor isomorphisms alone do not state restriction compatibility for the
canonical base-change arrow or preservation of the universally quantified coordinate
stalk condition. Applying arbitrary functor isomorphisms cannot prove those claims.
The new theorem records precisely that missing compatibility for a constructed
coefficient morphism. It uses the existing coordinate-invariance theorem to pass from
restricted coordinates to all coordinates.

Checked the locality paragraph of Stacks Tag 0DJ9 and the counit construction in Tag 08HY
on their official pages; the local literature source is not present in this checkout.
The mathematical proof plan is consistent with them. Small cases checked: top opens
and identities recover the original square up to canonical comparisons; empty opens
have vacuous stalk conditions and zero derived objects; zero coefficients and arbitrary
unbounded coefficients impose no extra finiteness or boundedness hypothesis. The top
proof never assumes inverse images of affine opens are affine. Only the two bases are
required affine, exactly as in `h_affine`.

## New nodes

`lem-pc-single-complex-open-restriction-comparison` in
`dag/nodes/sec-picard-framework/` carries the constructed open-pullback and coefficient
comparisons and the remaining theorem. It is the canonical restriction step of the
existing target-locality plan, strictly separate from affine-neighbourhood selection,
quasi-coherence, the affine criterion, and global detection of isomorphisms. Mathlib
searches (LeanFinder, Loogle, grep) were run through msearch.py. LeanSearch was also
called and returned an Internal Server Error, recorded as unavailable; project and blueprint
searches found no duplicate. No change record is needed.


## Second reading by K4

1. PASS. Diffed both delivered modules against the repository (the comparison
   module is new). The existing target-locality declaration's signature and
   visibility are byte-for-byte unchanged. No existing definition changes, no
   target edits, and no change record or forced adaptation is needed.
2. PASS. Both files compile with lcompile.py. The only textual sorry is the
   complete proof of `singleComplexBaseChange_openRestrictionComparison`, listed
   above with its node. No forbidden declaration or hollow definition occurs.
   The two new definitions construct their data: exact restriction, the mate of
   the ordinary tensor-pullback adjunction, left-derived uniqueness with the
   pinned counit, and the pinned composition comparisons. Existence choices
   serve universal properties and never select arbitrary coefficient objects.
   The delivery probe checks every declaration's axioms; scratch #print axioms
   checks show exactly [propext, Classical.choice, Quot.sound] for both new
   definitions. The remaining comparison theorem and the original target-locality
   theorem show those three plus sorryAx, as expected from the recorded open hole.
3. PASS AS DECOMPOSITION. The new hole fixes the opens and the coefficient data;
   it has no affine criterion and does not assert global invertibility. The top
   proof separately selects affine neighbourhoods, constructs their pullback,
   restricts quasi-coherence, applies the affine premise, and invokes locality.
   Checked top opens/identities, empty opens, zero coefficients, and unbounded
   coefficients. The restricted source opens need not be affine. The docstring
   gives the K-flat/K-injective coordinate argument, local-ring and stalk
   transport, coordinate invariance, and the derived-counit computation. The
   ordinary adjunction uniqueness used in the open comparison is a mate of the
   identity on the common right adjoint; it is not an arbitrary functor twist.
   Read the coordinate-invariance theorem and the pinned base-change definition.
   Additional independent LeanFinder, Loogle and grep searches used the counit
   and adjunction wording; no existing theorem states this fixed-data result.
   The remaining compatibility proof is substantial and was not closed in a few
   minutes. Net hole change is zero, not an unconditional completed target.
4. PASS AFTER REPAIR. The unit's realized statement/step lists are empty; the
   parent qcqs induction route and affine-premise reduction are retained. Removed
   AffineDerivedPullbackTensorTilde from the comparison module and its DAG plan;
   the construction already supplies the open-pullback comparison, so no affine
   formula is used. Imported KFlatPullback directly for the remaining proof plan.
   Kept PointwiseLeftDerived public: an attempted private import caused Lean to
   reject its use in the exposed body of singleComplexOpenPullbackIso, so this
   import is needed by a definition, not solely by a theorem proof. Completed
   No longer needed with all old proof dependencies and their dispositions.
5. PASS AFTER REPAIR. Read both node records and all used declaration statements.
   The old node records the actual affine selection/restriction/locality proof;
   the new node records the constructions and remaining compatibility argument,
   source, searches, blueprint ancestry, and Lean declarations/signature. Removed
   the unused affine tensor/tilde node from every new-node proof step and from
   proof_deps, whose union still agrees. No existing statement field changed.

Changes by the second reader: pruned the unused affine tensor/tilde comparison
import and dependency, replaced it by direct K-flat preservation import, and
completed the pruning and review report. The mathematical reduction and all
Lean signatures were retained. Sources checked directly:
[Stacks 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9),
[Stacks 08HY](https://stacks.math.columbia.edu/tag/08HY), and
[Stacks 08FE](https://stacks.math.columbia.edu/tag/08FE).
