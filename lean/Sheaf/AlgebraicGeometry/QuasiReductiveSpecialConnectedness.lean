module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Sheaf.RingTheory.HenselianSmoothAlgebraLifting
import WeilConjectures.AlgebraicGeometry.DensePoints

/-! # Connected geometric special fibres of quasi-reductive models

Source: Prasad--Yu, On quasi-reductive group schemes, Theorem 1.2(c),
Proposition 4.4(i), and the first paragraph of Section 5
(blueprint: lem-sfb-quasi-reductive-special-connectedness).

The affine presentation is an isomorphism over Spec A. A closed reduced subgroup with
image the connected component of the identity presents the reduced neutral component;
its group law is induced because the inclusion is a morphism of group objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The geometric special fibre of a finite-type quasi-reductive model over a DVR
is connected, in every residue characteristic.

Source: Prasad--Yu, Theorem 1.2(c), Proposition 4.4(i), Section 5 first paragraph
(blueprint: lem-sfb-quasi-reductive-special-connectedness).

Proof:
1. Apply lem-sfb-group-model-potential-smooth-normalization to obtain a henselian
DVR extension with residue field the specified algebraic closure, a smooth affine
normalization N, and a finite surjective special-fibre group homomorphism q to G.
The generic fibre of N remains geometrically connected by scalar extension.
2. By lem-sfb-finite-group-cover-reductive-neutral, the reduced neutral component
of the special fibre of N is reductive. This allows inseparable finite kernels.
3. By lem-sfb-smooth-model-reductive-neutral-lift, N contains a split reductive
open affine subgroup D with the same generic fibre and special fibre N_special^0.
4. The integral-closure coordinate ring E of N embeds in its generic coordinate
ring. Generic restriction embeds N(R) in the generic rational points. For each
regular generic function f = pi^(-a) e, with e in E, all evaluations on N(R) have
valuation at least -a. Thus this subgroup is bounded and contains D(R).
By lem-sfb-split-reductive-integral-maximal-bounded it equals D(R).
5. Every rational special point of N lifts to an R-point: apply
lem-weil-pbc-smooth-ring-map-iff-smooth-affine and
lem-trf-henselian-smooth-algebra-lifting to E and the maximal ideal of R.
Step 4 puts this lift in D(R); injectivity of generic restriction shows that its
reduction belongs to D_special.
6. By lem-pc-rational-points-dense, rational points are dense in N_special. They
all lie in its closed neutral component D_special, so N_special is connected.
7. The continuous surjection q carries this connected space onto G_special;
a nontrivial open partition of the latter would pull back to one of the former. -/
theorem quasiReductive_special_connected
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (Ω : Type u) [Field Ω] [Algebra (IsLocalRing.ResidueField A) Ω]
    [IsAlgClosure (IsLocalRing.ResidueField A) Ω]
    (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [Module.Flat A B] (G : Grp (Over (Spec (.of A))))
    (e : G.X ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [Smooth (pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap A K))))]
    [GeometricallyConnected
      (pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap A K))))]
    (H : Grp (Over (Spec (.of Ω))))
    (j : H ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom
      ((algebraMap (IsLocalRing.ResidueField A) Ω).comp
        (IsLocalRing.residue A))))).mapGrp.obj G)
    [IsClosedImmersion j.hom.hom.left] [IsReduced H.X.left]
    (hH : Set.range j.hom.hom.left = connectedComponent
      (GrpObj.onePoint ((Over.pullback (Spec.map (CommRingCat.ofHom
        ((algebraMap (IsLocalRing.ResidueField A) Ω).comp
          (IsLocalRing.residue A))))).mapGrp.obj G).X))
    (hred : ReductiveTorusCentralizer.IsReductive H)
    (hdim : topologicalKrullDim H.X.left = topologicalKrullDim
      (pullback (C := Scheme.{u}) G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap A K))))) :
    ConnectedSpace (pullback (C := Scheme.{u}) G.X.hom (Spec.map (CommRingCat.ofHom
      ((algebraMap (IsLocalRing.ResidueField A) Ω).comp (IsLocalRing.residue A))))) := by
  sorry

end AlgebraicGeometry
