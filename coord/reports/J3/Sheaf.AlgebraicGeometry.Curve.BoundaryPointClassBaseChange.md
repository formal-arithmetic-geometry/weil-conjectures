## What changed

Proved `AlgebraicGeometry.boundary_point_class_base_change` directly, preserving its
signature byte for byte and all existing public imports. The projection defines a bijection
on boundary points: old boundary points are closed by the dimension-one open-complement
lemma; rational sections lift uniquely by the proved DensePoints API. The inverse bijection
lies over the projection. Flat base change of kernel ideals identifies the two point ideals;
the existing invertible-ideal dual-pullback isomorphism then gives the Picard equality.

Removed the first worker's two proposed modules and nodes. No new public declaration,
definition, statement change, change record, or split node is delivered. The existing item's
proof, proof_deps and proof_origin now describe the actual argument.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.boundary_point_class_base_change`.
Added zero holes. No sorry remains in the delivered module. This is a proof, not a decomposition.
The first worker's proposed `boundary_points_equiv` and
`boundary_point_class_compatibility` holes were removed with their undelivered modules.

The scratch axiom check reports exactly `[propext, Classical.choice, Quot.sound]` for the
original theorem, with no sorryAx. The final module compiles locally without warnings.

## No longer needed

Removed the original proof-only import `Sheaf.AlgebraicGeometry.BaseChangeCurve`, and removed
`lem-sc-base-change-curve` from the original proof_deps: no base-change curve theorem is used.
Both relative-dimension instances are already hypotheses, and boundary closedness upstairs
comes from the lifted rational section. The unit still uses the base-change curve result in
its separate curve-reduction step; this delivery changes no unit realization or chapter route.

Removed the redundant original proof-only import
`WeilConjectures.AlgebraicGeometry.EffectiveCartier`: its needed proved declarations are
already publicly available through Curve.Picard. That module remains transitively imported;
this is removal of a redundant import, not a claim that the whole module leaves the closure.
All other original proof_deps remain used. Added `def-pc-rational-point` for the explicit
base-changed sections and `lem-pc-recd-pullback` for the recorded dual-pullback declaration.

The proposed BoundaryPointsEquiv and BoundaryPointClassCompatibility modules and their
new-boundary-points-equiv and new-boundary-point-class-compatibility nodes are not delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker's `boundary_point_class_compatibility` asserted compatibility for an arbitrary
boundary equivalence, without saying it lay over the projection. This is false: for the
identity extension on a smooth elliptic curve with two distinct points removed, swapping
those boundary points would assert O(P)=O(Q), although P-Q is nontrivial in Picard degree zero.
Its proof also discarded all geometric information from `boundary_points_equiv`, whose
conclusion was only an arbitrary equivalence together with True. The proposed nodes had
placeholder Lean statements, empty search records, and incomplete natural-language proofs.

The repair needs no new lemma: existing proved rational-point and ideal-pullback interfaces
suffice. Boundary finiteness and the full baseChange_curve result in the old plan are stronger
than what this argument needs. No existing statement or definition was changed.

## Second reading by J3

1. Compared the delivered module to the repository version with diff, then compared the text
   from `theorem boundary_point_class_base_change` through its `:=` marker: byte-for-byte
   equal. All hypotheses, universe, let-bound objects, boundary subtypes, existential and
   pointwise Picard equality are unchanged. All original public imports remain unchanged.
2. Compiled the initial three-module proposal, finding a line-length warning in addition to
   its mathematical fault. Compiled the final single module cleanly through lcompile.py.
   Scanned for sorry, axiom, unsafe, opaque, implemented_by and extern: none. A scratch copy's
   #print axioms check lists only the three allowed axioms. There are no data definitions or
   unproved choices: the inverse chosen by Equiv.ofBijective is determined by a proved bijection.
3. Rejected the arbitrary-equivalence compatibility statement using the elliptic-curve
   permutation case. Removed both proposed split statements and nodes; no split statement
   remains to audit. Searched Mathlib using LeanFinder, Loogle, grep and LeanSearch (the latter
   unavailable), and searched both local Lean roots with ofClosedPoint, point/baseChange and
   vanishingIdeal/comap terms. Read DensePoints.baseChangeFieldPoint_eq_of_fst_eq,
   Picard.ker_pointOfClosedPoint, Scheme.Hom.ker_of_isPullback and the existing effective
   Cartier dual-pullback theorem; these close the entire argument without duplication.
4. The proof now follows the shortest available direct route through proved library results.
   Original private imports were removed and candidate added imports were tested and removed
   as redundant. Read dag/units/sk-prop-ext-invariance.json: its affine step requires the
   same rational boundary and point-class transport, which this proof supplies. Its realized
   arrays are empty and no realization is changed. Empty and singleton boundaries require
   no choices of a boundary base point; subtype bijectivity and the forall proof cover them
   directly. The identity extension returns the geometric correspondence, not a permutation.
5. Read the original item's node and its old dependencies. Updated only proof, proof_deps,
   proof_origin; the union of step uses equals proof_deps. The steps name the actual Lean
   helpers and explain every reduction. The old base-change-curve dependency is the only
   old node dependency removed; No longer needed records it. Read the blueprint theorem
   from the local blueprint snapshot and the unit's full affine proof text. The reduction
   preserves that affine boundary route and introduces no new nodes.

Changed after reading: replaced the unsound two-hole decomposition with the complete direct
proof; removed both proposed helper modules/nodes and redundant private imports; repaired
node metadata and this report. Validation and delivery are run with deliver3.py.
