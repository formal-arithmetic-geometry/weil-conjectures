## What changed
Proved AlgebraicGeometry.Scheme.affine_lift_eventual_free_kernels unchanged.
Repair removes the duplicate private affine_sections_flat_of_flat_stalks theorem
and uses the public relative_flat_of_stalks specialized to the identity morphism.
Updated the DAG dependency and removed the now-unused stalk-presentation and
flat-localization imports. Six private helpers remain, all proved.
Change record: coord/changes/affine-lift-eventual-free-kernels-local-commands.md.

## Proved and sorry left
Closed the one original hole AlgebraicGeometry.Scheme.affine_lift_eventual_free_kernels
(lem-sc-affine-lift-eventual-free-kernels). Zero holes added; no sorry remains.

## No longer needed
Relative to the repository baseline, removed the proof-only imports
Sheaf.AlgebraicGeometry.AffineTruncationKernelFiniteLocallyFree and
Sheaf.AlgebraicGeometry.AffineFiniteFreeSheafComplexLift.
Every former proof dependency absent from the new route is listed here:
lem-sc-affine-truncation-kernel-finite-locally-free,
lem-pc-affine-finite-free-sheaf-complex-lift, and
lem-weil-pbc-affine-tilde-gamma-adjunction.
These are dependencies pruned from this proof; global reachability is for the ledger.

The prior attempt's direct imports
Sheaf.AlgebraicGeometry.IntrinsicFlatModuleStalkTensorPresentation and
Mathlib.RingTheory.Flat.Localization are absent from this module, but remain used
transitively by RelativeFlatOfStalks. Their modules and the intrinsic presentation
node are therefore not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong
The prior private helper duplicated a library statement. That existing helper
is private and cannot be imported by name. The public relative_flat_of_stalks
provides the needed generalization without duplicating the localization proof.
The existing public statement is unchanged; no unit step is bypassed.

## Earlier second reading (a previous round; superseded)
The prior independent reader passed the original public proof and checked its
signature, axiom list, empty-open and rank-zero cases, route and DAG. That review
predates this repair; the repaired helper and DAG need a fresh second reading.

## Second reading by Y2

1. Compared the entire delivered module and node with the repository baseline.
   The sole existing public declaration's signature is byte-for-byte unchanged;
   the node's Lean statement also matches it byte-for-byte. Public imports and
   existing visibility are unchanged. Added helpers are private. The change record
   accurately describes the extra private universe and declaration-scoped commands.
   Verdict: pass; no change to a target, hypothesis, conclusion, or public data.
2. Compiled the module locally with lcompile.py: clean, 26.2 seconds. Compiled a
   scratch copy with #print axioms for all six private helpers and the public theorem:
   clean, 25.0 seconds, only propext, Classical.choice, Quot.sound for each.
   No sorry or forbidden declaration occurs. The derived localization helper
   constructs its functor from the supplied equivalence; it chooses no arbitrary
   data from an unproved existence theorem. Verdict: pass.
3. No statement was split off and no new node or hole was added. Read all private
   helpers, including the identity-morphism scalar comparisons. Checked the empty
   open, zero sheaf, and rank-zero cases: the compactness theorem inserts endpoint
   zero, and finite presentations allow empty index sets. Searched independently
   with rg and msearch grep/loogle (opcycles flat finite presentation;
   HasDerivedCategory, CategoryTheory.Equivalence). Existing analogous presentation
   and localization helpers are private; the public relative_flat_of_stalks and
   upstream flat_opcycles_of_exactAt are already used. Verdict: pass.
4. Read the proof from the target down. Ordinary vanishing comes directly from
   tensoring with the unit; K-flat comparisons give universal tensor exactness.
   At r <= a-1, the opcycles flatness test uses degree r-2 < a. Exactness at r-1
   and r makes the opcycles-to-cycles map monic and epic, giving the required kernel.
   Every added import supplies a used proof construction and is proof-only.
   Checked sk-thm-picard-duality's realized field and searched all unit records:
   none of the three removed dependency nodes realizes a unit step. All former
   proof_deps absent from this proof are now listed under No longer needed.
   Verdict: pass; unit route preserved, no shorter available public theorem found.
5. Compared the DAG's five proof steps with the Lean implementation, including
   relative_flat_of_stalks specialized to the identity. proof_deps is exactly the
   union of uses, and proof_origin describes the implemented categorical route.
   There are no new nodes to validate. Verdict: pass.

Second reading changed only this report: corrected the pruning claim to distinguish
removed direct imports from the intrinsic stalk presentation still used transitively,
and recorded this independent audit. No Lean or DAG repair was necessary.
