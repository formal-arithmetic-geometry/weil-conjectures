/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CyclicTotalTriangulated
public import WeilConjectures.CategoryTheory.RelativeRestrictionMateForgetting
public import WeilConjectures.CategoryTheory.RelativeLatticeBridge
public import WeilConjectures.CategoryTheory.ProductActionExactForgetting
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedInjectiveResolutionNaturality
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.CondensedDerivedRestrictionCalculus

/-! # Invariant-normalized cyclic row comparison with residual action

Source: blueprint, six-functors direct-image stability proof, paragraph (3), auxiliary
relative cyclic calculation, extracted steps 9--12; Stacks Tags 0133, 05T6, 05TH, 05TI.
The combined external reference is WANTED in the DAG source.
(blueprint: lem-sfb-cyclic-row-derived-comparison).

The total, its augmentation, invariants, computation units, residual forgetting and
lattice/universe transports are the existing constructions. Uniqueness below uses the
unit equation on every bounded-below complex, with no degree-zero uniqueness assumption.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CondensedBar
open Profinite.CondensedAction (inflate)

namespace CategoryTheory.RelativeCyclic

/-- Cache the existing canonical topological group structure on the discrete lifted
integers, so repeated action-category types do not search unrelated normed instances.
Source: paragraph (3), discrete cyclic group
(blueprint: lem-sfb-cyclic-row-derived-comparison). -/
instance (priority := 3000) cyclicRow_integerTopology : IsTopologicalGroup Z.{u} :=
  inferInstanceAs (IsTopologicalGroup (Multiplicative (ULift.{u} ℤ)))

variable (A : CondensedBar.Ring.{u}) (G : Type u)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The all-complex computation-unit equation for theta, with the localization comparisons
shown explicitly. This is the equation theta alpha = Qb, in categorical composition order.
Source: paragraph (3), extracted step 10
(blueprint: lem-sfb-cyclic-row-derived-comparison). -/
def RowNormalized (K : TotalModel A G)
    (F : DerivedCategory.Plus (Equivariant A (G × Z.{u})) ⥤
      DerivedCategory.Plus (Equivariant A G))
    (e : plusQ A (G × Z) ⋙ F ⋙ DerivedCategory.Plus.ι ≅
      CochainComplex.Plus.ι _ ⋙ K.functor ⋙ DerivedCategory.Q)
    (θ : descent A G ⟶ F ⋙ DerivedCategory.Plus.ι) : Prop :=
  ∀ P : CochainComplex.Plus (Equivariant A (G × Z.{u})),
    unit A G Z P.obj ≫
        (derived A G Z).map ((plusQιIso A (G × Z)).inv.app P) ≫
        θ.app ((plusQ A (G × Z)).obj P) ≫ e.hom.app P =
      DerivedCategory.Q.map (K.augmentation.app P.obj)

/-- An injective module has an acyclic augmented cyclic row, retaining the residual action.
Source: paragraph (3), extracted step 9; Stacks 05TH
(blueprint: lem-sfb-cyclic-row-derived-comparison).
Proof: forget G. The exact induction left adjoint makes the forgotten module injective
(lem-sfb-product-action-exact-forgetting). In rank one the lattice comparison takes the
invariant inclusion to the derived unit (lem-sfb-discrete-lattice-koszul-resolution).
That unit is invertible on an injective module (lem-weil-pbc-right-derived-plus-injective),
so its row augmentation is a quasi-isomorphism. Forgetting G preserves the two coordinates
and reflects derived isomorphisms; cohomology reflects this back to the relative row. -/
theorem cyclicRow_injective_module (K : TotalModel A G)
    (I : Equivariant A (G × Z.{u})) [Injective I] :
    QuasiIso (K.augmentation.app (single A (G × Z) I).obj) := by
  sorry

/-- The assembled row augmentation is a quasi-isomorphism on every bounded-below termwise
injective complex. The instance also makes its derived inverse available in the formula.
Source: paragraph (3), extracted steps 9--10; Stacks 0133
(blueprint: lem-sfb-cyclic-row-derived-comparison).
Proof: put I in cyclic columns zero and one with horizontal map T-1, and put Gamma(I)
on column zero of the augmentation bicomplex. Invariant inclusion commutes with the
vertical differential and is killed by T-1, so these are a bicomplex map. The preceding
injective-module row calculation gives quasi-isomorphisms on rows. Move the lower bound
to zero and transpose with the signs of lem-sfb-cyclic-total-triangulated, which are one
on the augmentation axis. Apply lem-sc-first-quadrant-total-column-comparison and undo
these signed identifications. Its total map is exactly b_I. -/
@[instance] theorem cyclicRow_injective_complex (K : TotalModel A G)
    (I : CochainComplex.Plus (Equivariant A (G × Z.{u})))
    [∀ n : ℤ, Injective (I.obj.X n)] : QuasiIso (K.augmentation.app I.obj) := by
  sorry

/-- There is exactly one theta normalized on all bounded-below complexes; it is invertible
and commutes with the canonical signed shifts. F and e are the localized total of the
signed-total theorem, with its specified localization comparison.
Source: paragraph (3), extracted steps 10--11; Stacks 05TI, 05S7
(blueprint: lem-sfb-cyclic-row-derived-comparison).
Proof: b is natural because its coordinates are the invariant inclusion and zero.
The signed-total theorem descends K through homotopies and quasi-isomorphisms. Apply
clause (1) of lem-weil-pbc-right-derived-plus-injective to Qb to obtain a unique theta
with the displayed all-complex equation. On injective complexes it is Qb alpha inverse,
so it is invertible by the preceding row comparison and clause (2). Every bounded-below
complex has a bounded-below injective resolution, by 05T6, including its lower bound;
naturality along that inverted resolution proves invertibility everywhere. Signed shift
and cone comparisons are identity on the augmentation axis. The unit comparison on
injectives respects them, and resolution naturality extends this to all objects. -/
theorem cyclicRow_derived_comparison (K : TotalModel A G)
    (_hK : HasSignedTotalShift A G K)
    (F : DerivedCategory.Plus (Equivariant A (G × Z.{u})) ⥤
      DerivedCategory.Plus (Equivariant A G)) [F.CommShift ℤ]
    (e : plusQ A (G × Z) ⋙ F ⋙ DerivedCategory.Plus.ι ≅
      CochainComplex.Plus.ι _ ⋙ K.functor ⋙ DerivedCategory.Q)
    (_he : NatTrans.CommShift e.hom ℤ) :
    (∃! θ : descent A G ⟶ F ⋙ DerivedCategory.Plus.ι, RowNormalized A G K F e θ) ∧
    (∀ θ : descent A G ⟶ F ⋙ DerivedCategory.Plus.ι,
      RowNormalized A G K F e θ → IsIso θ ∧ NatTrans.CommShift θ ℤ) := by
  sorry

/-- The inverse comparison on actual complexes has precisely the existing HasComparison
normalization and signed shift. This supplies the input consumed by lambda and cyclicMap.
Source: paragraph (3), extracted steps 10--11
(blueprint: lem-sfb-cyclic-row-derived-comparison).
Proof: choose the triangulated descent and comparison of the signed-total theorem.
Invert theta above and whisker by plusQ, then compose its localization comparison e.
The all-complex equation becomes the normalization in HasComparison, and the signed
shift equation is unchanged. No comparison is selected merely by degree-zero data. -/
theorem cyclicRow_hasComparison (K : TotalModel A G)
    (_hK : HasSignedTotalShift A G K) : HasComparison A G K := by
  sorry

/-- Every specified injective resolution computes the same lambda, with the exact order
of the four arrows in the resolution formula; hence there is no resolution choice left.
Source: paragraph (3), extracted step 11; Stacks 05TH, 05TI
(blueprint: lem-sfb-cyclic-row-derived-comparison).
Proof: naturality gives Q(Ka) theta_N = theta_I RG(Qa). On I the all-complex equation
is theta_I = Qb_I alpha_I inverse. Substitute and invert to obtain this formula. Both
sides are the existing lambda_N for every a, so changing the resolution does not change
it. Injectivity is asserted for I, never for the restriction of another resolution. -/
theorem cyclicRow_resolution_formula {K : TotalModel A G} (C : HasComparison A G K)
    {N I : CochainComplex.Plus (Equivariant A (G × Z.{u}))}
    [∀ n : ℤ, Injective (I.obj.X n)] (a : N ⟶ I) [QuasiIso a.hom] :
    (lambda A G C N).hom =
      DerivedCategory.Q.map (K.functor.map a.hom) ≫
        inv (DerivedCategory.Q.map (K.augmentation.app I.obj)) ≫ unit A G Z I.obj ≫
        inv ((derived A G Z).map (DerivedCategory.Q.map a.hom)) := by
  sorry

/-- Naturality of the actual inverse comparison on every diagram, in particular diagrams
of specified injective resolutions and their actual cones. No resolution is chosen here.
Source: paragraph (3), extracted step 11; Stacks 0156
(blueprint: lem-sfb-cyclic-row-derived-comparison).
Proof: the unique theta is a natural transformation. Invert its naturality square and
transport by plusQιIso to get this square for lambda. Substituting the preceding formula
identifies the square on any specified resolutions. The cone comparison in
lem-sp-derived-injective-resolution-naturality uses the actual specified cone, so the same
square includes maps of cones, not an unrelated choice of injective model. -/
theorem cyclicRow_resolution_naturality {K : TotalModel A G} (C : HasComparison A G K)
    {N P : CochainComplex.Plus (Equivariant A (G × Z.{u}))} (f : N ⟶ P) :
    DerivedCategory.Q.map (K.functor.map f.hom) ≫ (lambda A G C P).hom =
      (lambda A G C N).hom ≫ (derived A G Z).map (DerivedCategory.Q.map f.hom) := by
  sorry

/-- The inverse comparison respects the signed shifts, including cone boundaries.
The boundary equality is written for every triangle arrow of degree one, and therefore
applies to the negative cone projection with no unsigned replacement.
Source: paragraph (3), extracted step 11; Stacks 0156
(blueprint: lem-sfb-cyclic-row-derived-comparison).
Proof: the signed shift has coordinates (x,(-1)^s y), hence is identity on b. On injective
complexes alpha is the canonical computation comparison and commutes with shifts.
Resolution naturality on the specified cone extends the equality to lambda. Naturality
at the third arrow followed by the shift equation is precisely the boundary square. -/
theorem cyclicRow_shift_boundary {K : TotalModel A G} (C : HasComparison A G K) :
    NatTrans.CommShift C.iso.hom ℤ ∧
    (∀ (N P : CochainComplex.Plus (Equivariant A (G × Z.{u})))
      (f : P ⟶ (shiftFunctor _ (1 : ℤ)).obj N),
      (CochainComplex.Plus.ι _ ⋙ K.functor ⋙ DerivedCategory.Q).map f ≫
          ((CochainComplex.Plus.ι _ ⋙ K.functor ⋙ DerivedCategory.Q).commShiftIso
            (1 : ℤ)).hom.app N ≫
          (shiftFunctor _ (1 : ℤ)).map (C.iso.hom.app N) =
        C.iso.hom.app P ≫ (plusQ A (G × Z) ⋙ descent A G).map f ≫
          ((plusQ A (G × Z) ⋙ descent A G).commShiftIso (1 : ℤ)).hom.app N) := by
  sorry

/-- Forgetting the row gives the scalar all-complex normalization. The inverse of the
fixed-section comparison identifies the augmentation's domain; both row coordinates and
the differential are unchanged by forgetting.
Source: paragraph (3), extracted step 12; Stacks 05TH
(blueprint: lem-sfb-cyclic-row-derived-comparison).
Proof: on a relative injective resolution, forgetting preserves injectivity and the
invariant inclusions are identical. The defining equation of forgetDerivedExist and
lambda Qb = alpha cancel to give this equality. Naturality along any injective resolution
extends it to every bounded-below complex, including ones not termwise injective. -/
theorem cyclicRow_forgotten_normalization {K : TotalModel A G} (C : HasComparison A G K)
    (N : CochainComplex.Plus (Equivariant A (G × Z.{u}))) :
    DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (forgetInvariants A G (J := Z)) (.up ℤ)).inv.app
            N.obj ≫
          ((CondensedBar.forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ)).map
            (K.augmentation.app N.obj)) ≫ (forgottenLambda A G C N).hom =
      scalarUnit A Z (((forgetResidual A G Z).mapHomologicalComplex (.up ℤ)).obj N.obj) := by
  sorry

/-- Canonical shifts for residual forgetting on bounded-below complexes, transported
through the existing full-subcategory inclusion, with no new signed comparison.
Source: paragraph (3), extracted step 12
(blueprint: lem-sfb-cyclic-row-derived-comparison). -/
instance cyclicRow_forgetResidualPlusShift :
    (forgetResidual A G Z).mapCochainComplexPlus.CommShift ℤ :=
  Functor.CommShift.ofComp (forgetResidual A G Z).mapCochainComplexPlusCompι ℤ

/-- Canonical shifts for reinserting the trivial residual action on bounded-below complexes.
Source: paragraph (3), extracted step 12
(blueprint: lem-sfb-cyclic-row-derived-comparison). -/
instance cyclicRow_addResidualPlusShift :
    (addTrivialResidual A).mapCochainComplexPlus.CommShift ℤ :=
  Functor.CommShift.ofComp (addTrivialResidual A).mapCochainComplexPlusCompι ℤ

/-- The forgotten relative row is naturally the scalar row, realized by the trivial
residual group. The two coordinate equations fix the comparison, and its square identifies
lambda on all complexes. Its inverse identifies theta, with canonical shifts and boundaries.
Source: paragraph (3), extracted step 12
(blueprint: lem-sfb-cyclic-row-derived-comparison).
Proof: the original modules, T-1 and vertical differentials agree after forgetting.
The identity in both coordinates therefore gives the unique chain isomorphism, natural
in every chain map. Both invariant augmentations agree. On injective complexes the units
and inverse augmentations compute both lambdas, so their square commutes. Naturality along
resolutions extends it to all complexes. The signed shift is (x,(-1)^s y) on both sides;
the cone permutation and its negative boundary agree as well. -/
theorem cyclicRow_forgetting {K : TotalModel A G} (C : HasComparison A G K)
    {K₀ : TotalModel A PUnit.{u + 1}} (C₀ : HasComparison A PUnit.{u + 1} K₀) :
    ∃! k : CochainComplex.Plus.ι _ ⋙ K.functor ⋙
        (CondensedBar.forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ) ≅
      (forgetResidual A G Z).mapCochainComplexPlus ⋙
        (addTrivialResidual A).mapCochainComplexPlus ⋙ CochainComplex.Plus.ι _ ⋙
        K₀.functor ⋙ (CondensedBar.forgetAction
          (A := A) (G := PUnit.{u + 1})).mapHomologicalComplex (.up ℤ),
      (∀ (N : CochainComplex.Plus (Equivariant A (G × Z.{u}))) (n : ℤ),
        (k.hom.app N).f n ≫
            (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).map
              ((K₀.coordinates
                ((addTrivialResidual A).mapCochainComplexPlus.obj
                  ((forgetResidual A G Z).mapCochainComplexPlus.obj N)).obj n).hom ≫
                biprod.fst) =
          (CondensedBar.forgetAction (A := A) (G := G)).map
            ((K.coordinates N.obj n).hom ≫ biprod.fst) ∧
        (k.hom.app N).f n ≫
            (CondensedBar.forgetAction (A := A) (G := PUnit.{u + 1})).map
              ((K₀.coordinates
                ((addTrivialResidual A).mapCochainComplexPlus.obj
                  ((forgetResidual A G Z).mapCochainComplexPlus.obj N)).obj n).hom ≫
                biprod.snd) =
          (CondensedBar.forgetAction (A := A) (G := G)).map
            ((K.coordinates N.obj n).hom ≫ biprod.snd)) ∧
      (∀ N : CochainComplex.Plus (Equivariant A (G × Z.{u})),
        DerivedCategory.Q.map (k.hom.app N) ≫
            (forgottenLambda A PUnit.{u + 1} C₀
              ((addTrivialResidual A).mapCochainComplexPlus.obj
                ((forgetResidual A G Z).mapCochainComplexPlus.obj N))).hom ≫
            (CondensedDerivedRestriction.derived A Z).map
              (DerivedCategory.Q.map
                (scalarizationIso A ((forgetResidual A G Z).mapCochainComplexPlus.obj N)).hom) =
          (forgottenLambda A G C N).hom) ∧ NatTrans.CommShift k.hom ℤ := by
  sorry

/-- The canonical coordinate-preserving natural row identification. The existence theorem
characterizes it uniquely, so this definition chooses no unspecified mathematical data.
Source: paragraph (3), extracted step 12
(blueprint: lem-sfb-cyclic-row-derived-comparison). -/
def rowForgetIso {K : TotalModel A G} (C : HasComparison A G K)
    {K₀ : TotalModel A PUnit.{u + 1}} (C₀ : HasComparison A PUnit.{u + 1} K₀) :
    CochainComplex.Plus.ι _ ⋙ K.functor ⋙
        (CondensedBar.forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ) ≅
      (forgetResidual A G Z).mapCochainComplexPlus ⋙
        (addTrivialResidual A).mapCochainComplexPlus ⋙ CochainComplex.Plus.ι _ ⋙
        K₀.functor ⋙ (CondensedBar.forgetAction
          (A := A) (G := PUnit.{u + 1})).mapHomologicalComplex (.up ℤ) :=
  Classical.choose (cyclicRow_forgetting A G C C₀)

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The actual composite c on a bounded-below complex: beta followed by lambda inverse,
with the exact restriction/localization comparison. Its module case is cyclicMap.
Source: paragraph (3), extracted step 12
(blueprint: lem-sfb-cyclic-row-derived-comparison). -/
def rowRestrictionMap {K : TotalModel A G} (C : HasComparison A G K)
    (v : Z.{u} →ₜ* H) (N : CochainComplex.Plus (Equivariant A (G × H))) :
    (derived A G H).obj (DerivedCategory.Q.obj N.obj) ⟶
      DerivedCategory.Q.obj (K.functor.obj
        ((inflate (R := A.toMon) (productMap (G := G) v)).mapCochainComplexPlus.obj N).obj) :=
  (beta (A := A) (G := G) v).app (DerivedCategory.Q.obj N.obj) ≫
    (derived A G Z).map
      ((inflate (R := A.toMon) (productMap (G := G) v)).mapDerivedCategoryFactors.hom.app
        N.obj) ≫
    (lambda A G C
      ((inflate (R := A.toMon) (productMap (G := G) v)).mapCochainComplexPlus.obj N)).inv

/-- Forgetting c is exactly scalar derived restriction followed by the inverse scalar row
comparison. The last factor is the scalar comparison identified by cyclicRow_forgetting;
all exact-functor localization identifications are displayed.
Source: paragraph (3), extracted step 12
(blueprint: lem-sfb-cyclic-row-derived-comparison).
Proof: apply exact forgetting to beta followed by lambda inverse. The mate-forgetting
identity identifies beta with scalar group restriction. The preceding natural row square
identifies lambda with its scalar value; invert that square. Compose the two equalities.
Both factors respect signed shifts and boundaries, by the mate theorem and the row square,
so the equality also respects the negative cone boundary. No inverse of beta is used. -/
theorem cyclicRow_restriction_forgetting [CompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] {K : TotalModel A G} (C : HasComparison A G K)
    (v : Z.{u} →ₜ* H) (N : CochainComplex.Plus (Equivariant A (G × H))) :
    (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategory.map
        (rowRestrictionMap A G C v N) ≫
      (CondensedBar.forgetAction (A := A) (G := G)).mapDerivedCategoryFactors.hom.app
        (K.functor.obj
          ((inflate (R := A.toMon) (productMap (G := G) v)).mapCochainComplexPlus.obj N).obj) =
    (forgetDerived A G (J := H)).hom.app (DerivedCategory.Q.obj N.obj) ≫
      (CondensedDerivedRestriction.groupMap A v).app
        ((forgetResidual A G H).mapDerivedCategory.obj (DerivedCategory.Q.obj N.obj)) ≫
      (CondensedDerivedRestriction.derived A Z).map
        ((forgetRestrictionDerived (A := A) (G := G) v).hom.app
            (DerivedCategory.Q.obj N.obj) ≫
          (forgetResidual A G Z).mapDerivedCategory.map
            ((inflate (R := A.toMon) (productMap (G := G) v)).mapDerivedCategoryFactors.hom.app
              N.obj) ≫
          (forgetResidual A G Z).mapDerivedCategoryFactors.hom.app
            ((inflate (R := A.toMon) (productMap (G := G) v)).mapCochainComplexPlus.obj N).obj) ≫
      (forgottenLambda A G C
        ((inflate (R := A.toMon) (productMap (G := G) v)).mapCochainComplexPlus.obj N)).inv := by
  sorry

end CategoryTheory.RelativeCyclic

namespace Profinite.DiscreteLattice


open CategoryTheory.RelativeCyclic

/-- The lattice existential witness can be chosen to be the normalized scalar row
comparison in rank one, simultaneously with all its coefficient squares and rank-zero
identity. The bridge fixes the action and localization universes by their computation
units, and the two actual subset coordinates fix the chain comparison.
Source: paragraph (3), extracted step 12; Stacks 05TH, 05S7
(blueprint: lem-sfb-cyclic-row-derived-comparison).
Proof: construct the scalar comparison by the row augmentation on injective resolutions.
Its invariant inclusion normalization is lambda Qb = alpha. DiscreteBridge identifies
locally constant integer actions with the action of their positive generator, and its
invariant comparison identifies actual fixed sections. DiscreteDerivedBridge transports
the two derived localizations by their units on every complex. Both coordinates of the
rank-one Koszul complex are the scalar row, with differential T-1; comparison on the
common injective model gives the displayed equality. For coefficient restriction s,
exactness preserves b_I as a quasi-isomorphism even though sI need not be injective.
The equation theta alpha = Qb then makes alpha(sI) invertible. The normalized coefficient
map is represented by inverse alpha(sI) followed by s alpha(I). Substituting the row
formula cancels these factors and gives the coefficient square, also after a map f.
Retain the existing witnesses in other ranks, including the rank-zero identity. Thus
this is a witness to the entire lattice assertion, not just a degree-zero normalization. -/
theorem cyclicRow_lattice_witness (A : CondensedBar.Ring.{u}) (G : Type u)
    [_root_.Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {M : CategoryTheory.RelativeCyclic.TotalModel A G}
    (C : CategoryTheory.RelativeCyclic.HasComparison A G M) :
    ∃ (K : ∀ (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ), KoszulModel R r)
      (comparison : ∀ (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ),
        Comparison R r (K R r)),
      (∀ (R R' : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] [IsCommMonObj R'.X]
        (φ : R ⟶ R') (r : ℕ),
        ∃ c : CoefficientComparison φ r,
        ∀ P' : Equivariant R' r,
        ∃ k : (K R r).functor.obj ((equivariantRestriction φ r).obj P') ≅
          ((restriction φ).mapHomologicalComplex (.up ℤ)).obj ((K R' r).functor.obj P'),
        (∀ (a : ℤ) (I J : Subsets r a),
          biproduct.ι _ I ≫ ((K R r).coordinates _ a).inv ≫ k.hom.f a ≫
            (restriction φ).map (((K R' r).coordinates P' a).hom ≫ biproduct.π _ J) =
              if I = J then 𝟙 _ else 0) ∧
        (∀ (P : Equivariant R r) (f : P ⟶ (equivariantRestriction φ r).obj P'),
          (comparison R r).iso.hom.app P ≫
              (derivedInvariants R r).map ((DerivedCategory.singleFunctor _ 0).map f) ≫
              (c.iso P').hom =
            DerivedCategory.Q.map ((K R r).functor.map f ≫ k.hom) ≫
              (restriction φ).mapDerivedCategoryFactors.inv.app
                ((K R' r).functor.obj P') ≫
              (restriction φ).mapDerivedCategory.map ((comparison R' r).iso.hom.app P'))) ∧
      (∀ (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (P : Equivariant R 0),
        ∃ (e : P.V ≅ (invariants R 0).obj P)
          (k : (K R 0).functor.obj P ≅ (HomologicalComplex.single _ (.up ℤ) 0).obj P.V),
          e.hom ≫ limit.π
            ((Action.functorCategoryEquivalence (Modules R) (Group 0)).functor.obj P)
              PUnit.unit = 𝟙 P.V ∧
          k.hom.f 0 = ((K R 0).coordinates P 0).hom ≫
            biproduct.π _ ⟨∅, rfl⟩ ≫
              (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P.V).inv ∧
          (comparison R 0).iso.hom.app P = DerivedCategory.Q.map k.hom ≫
            (DerivedCategory.singleFunctor _ 0).map e.hom ≫ invariantUnit R 0 P) ∧
    ∃ (B : DiscreteBridge A) (E : DiscreteDerivedBridge A B),
    ∀ N : CategoryTheory.CondensedBar.Equivariant A (G × Z.{u}),
      ∃ k : ((CondensedBar.forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ)).obj
          (M.functor.obj (single A (G × Z) N).obj) ≅
        (K A.toMon 1).functor.obj (B.equivalence.functor.obj ((forgetResidual A G Z).obj N)),
      (k.hom.f 0 ≫
          ((K A.toMon 1).coordinates
            (B.equivalence.functor.obj ((forgetResidual A G Z).obj N)) 0).hom ≫
          biproduct.π _ ⟨∅, rfl⟩ ≫ B.underlying.hom.app ((forgetResidual A G Z).obj N) =
        zeroCoordinate M N) ∧
      (k.hom.f 1 ≫
          ((K A.toMon 1).coordinates
            (B.equivalence.functor.obj ((forgetResidual A G Z).obj N)) 1).hom ≫
          biproduct.π _ ⟨{0}, by simp⟩ ≫ B.underlying.hom.app ((forgetResidual A G Z).obj N) =
        oneCoordinate M N) ∧
      DerivedCategory.Q.map k.hom ≫
          (lowerQ A).inv.app
            ((K A.toMon 1).functor.obj
              (B.equivalence.functor.obj ((forgetResidual A G Z).obj N))) ≫
          (lowerDerived A).map
            ((comparison A.toMon 1).iso.hom.app
              (B.equivalence.functor.obj ((forgetResidual A G Z).obj N))) ≫
          (lowerDerived A).map ((Profinite.DiscreteLattice.derivedInvariants A.toMon 1).map
            ((B.equivalence.functor.mapDerivedCategorySingleFunctor 0).inv.app
              ((forgetResidual A G Z).obj N))) ≫
          E.iso.hom.app ((DerivedCategory.singleFunctor _ 0).obj
            ((forgetResidual A G Z).obj N)) =
        (forgottenLambda A G C (single A (G × Z) N)).hom ≫
          (CondensedDerivedRestriction.derived A Z).map
            (DerivedCategory.Q.map
              ((HomologicalComplex.singleMapHomologicalComplex (forgetResidual A G Z)
                (.up ℤ) 0).hom.app N)) := by
  sorry

end Profinite.DiscreteLattice
