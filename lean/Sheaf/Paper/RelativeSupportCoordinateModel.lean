/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.CoefficientTwistsDetailed
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.AlgebraicGeometry.EtaleCoordinateSupport
public import Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback

public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
import Sheaf.AlgebraicGeometry.ModuleCohomologyConventions
import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
import Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage
import Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity
import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
import WeilConjectures.RingTheory.Etale.LocalDimension
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial
import WeilConjectures.SixFunctors.OpenClosed.Stalk
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.StrictlyHenselianConstantCohomology
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Algebra.Category.Grp.AB
import Sheaf.AlgebraicGeometry.CartierKummerMap
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.SupportedCupFunctoriality

/-!
# Relative supported stalks in simultaneous etale coordinates

Source: Stacks Project, Tags 0FUE and 09XP; the normal-slice comparison and its
nine-step proof in the DAG (blueprint: lem-pur-relative-support-coordinate-model).

The support sheaf is the kernel of the open-complement adjunction unit. Its stalk
is derived in the category of coefficient modules. Exactness of geometric stalks
identifies this with the stalk of the derived support sheaf. The coordinate map
is the inverse of ordinary pullback from the normal affine space over k; the
underived map is fixed by its kernel-inclusion equation.

## Main declarations

- `RelativeSupportCoordinates`: the entire given geometric chart, including its cartesian square.
- `RelativeSupportCoordinates.comparison`: the canonical normal-coordinate pullback comparison.
- `RelativeSupportCoordinates.comparison_twist_identification`: signed tensor compatibility.
- `RelativeSupportCoordinates.relative_support_coordinate_model`: invertibility and codimension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory




namespace AlgebraicGeometry

/-- The finite coefficient characteristic is positive at every positive truncation.
Source: the finite coefficient datum and DAG step 2
(blueprint: lem-pur-relative-support-coordinate-model).
Proof: the positive quotient of the valuation ring is a nonzero finite ring. Its
characteristic is therefore positive, and ULift preserves that characteristic. -/
theorem coordinateCoefficientCharacteristic_pos (P : WeilConjectures.PurityFiniteSetting.{u}) :
    0 < ringChar P.Coefficient := by
  sorry

/-- The characteristic of the finite coefficient ring is invertible on a ground-field
scheme. Source: the distinct residue-characteristic convention and DAG step 2
(blueprint: lem-pur-relative-support-coordinate-model).
Proof: the characteristic of the positive truncated valuation ring is a positive power
of the coefficient prime. This prime differs from the characteristic of `k`. Its
image in `k`, hence in every global section ring of a `k`-scheme, is a unit. -/
theorem coordinateCoefficientCharacteristic_unit (P : WeilConjectures.PurityFiniteSetting.{u})
    {T : Scheme.{u}} (s : T ⟶ Spec (.of P.field.k)) :
    IsUnit (ringChar P.Coefficient : Γ(T, ⊤)) := by
  sorry

/-- The roots comparison and all signed coefficient comparisons for one map.
Source: Stacks 03PK and [lem-asd-etale-finite-twist-pullback]
(blueprint: lem-pur-relative-support-coordinate-model). -/
structure CoordinateTatePullbackData (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) {T T' : Scheme.{u}} (v : T' ⟶ T) where
  roots : (Etale.upperStar AddCommGrpCat.{u + 1} v).obj (T.rootsOfUnitySheaf m) ≅
    T'.rootsOfUnitySheaf m
  twists : ∀ r : ℤ,
    (Etale.upperStar (ModuleCat.{u + 1} A) v).obj
        (Scheme.finiteEtaleTateSheaf A m T hA r) ≅
      Scheme.finiteEtaleTateSheaf A m T' hA r

/-- Root restriction, coefficient generators, the constant unit, positive tensor
recursion and negative evaluation uniquely normalize the signed pullback family.
Source: Stacks 03PK and [lem-asd-etale-finite-twist-pullback]
(blueprint: lem-pur-relative-support-coordinate-model). -/
def CoordinateTatePullbackData.IsNormalized {A : Type (u + 1)} [CommRing A]
    {m : ℕ} {hA : (m : A) = 0} {T T' : Scheme.{u}} {v : T' ⟶ T}
    (d : CoordinateTatePullbackData A m hA v) : Prop :=
  ((Etale.upperStar AddCommGrpCat.{u + 1} v).map (kernel.ι (m • 𝟙 T.gmSheaf)) ≫
      Scheme.upperStarGmSheafToGmSheaf v =
    d.roots.hom ≫ kernel.ι (m • 𝟙 T'.gmSheaf)) ∧
  (∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf m).obj.obj W),
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
      (d.twists 1).hom).hom.app W (Scheme.finiteEtaleTateOneGenerator A m T hA W a z) =
      Scheme.finiteEtaleTateOneGenerator A m T' hA
        ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj W) a
        (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
          d.roots.hom).hom.app W z)) ∧
  (d.twists 0 = (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).app
    (ModuleCat.of A A)) ∧
  (∀ n : ℕ, d.twists (.ofNat (n + 2)) =
    asIso (Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
      (Scheme.finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))
      (Scheme.finiteEtaleTateLine T m A hA)) ≪≫
        tensorIso (d.twists (.ofNat (n + 1))) (d.twists 1)) ∧
  (∀ n : ℕ,
    (Etale.upperStar (ModuleCat.{u + 1} A) v).map
        ((ihom.ev (Scheme.finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
          (Scheme.finiteEtaleTateSheaf A m T hA 0)) ≫ (d.twists 0).hom =
      Functor.OplaxMonoidal.δ (Etale.upperStar (ModuleCat.{u + 1} A) v)
        (Scheme.finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))
        (Scheme.finiteEtaleTateSheaf A m T hA (.negSucc n)) ≫
      tensorHom (d.twists (.ofNat (n + 1))).hom (d.twists (.negSucc n)).hom ≫
        (ihom.ev (Scheme.finiteEtaleTateSheaf A m T' hA (.ofNat (n + 1)))).app
          (Scheme.finiteEtaleTateSheaf A m T' hA 0))

/-- The normalized pullback data exist uniquely, a compact interface to the published
finite Tate theorem. Source: Stacks 03PK and [lem-asd-etale-finite-twist-pullback]
(blueprint: lem-pur-relative-support-coordinate-model).
Proof: take its roots and signed pullback families and the five displayed
normalizations. The roots map is unique by the monic inclusion into the pulled-back
multiplicative-group sheaf. The coefficient-extended root generators determine degree
one; the constant comparison determines degree zero. Induction determines positive
powers. Evaluation on the locally free rank-one positive twist determines the negative
dual comparison uniquely. These component equalities give equality of the two records. -/
theorem coordinateTatePullback_existsUnique (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤))) :
    ∃! d : CoordinateTatePullbackData A m hA v, d.IsNormalized := by
  sorry

/-- The unique root/evaluation-normalized signed pullback, without unfolding the
large global existence-and-coherence theorem at each chart.
Source: Stacks 03PK and [lem-asd-etale-finite-twist-pullback]
(blueprint: lem-pur-relative-support-coordinate-model). -/
def coordinateTatePullback (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) {T T' : Scheme.{u}} (v : T' ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) (hT' : IsUnit (m : Γ(T', ⊤))) (r : ℤ) :
    (Etale.upperStar (ModuleCat.{u + 1} A) v).obj
        (Scheme.finiteEtaleTateSheaf A m T hA r) ≅
      Scheme.finiteEtaleTateSheaf A m T' hA r :=
  (coordinateTatePullback_existsUnique A m hm hA v hT hT').choose.twists r

/-- The unit, concatenation, associativity, symmetry and evaluation normalizations of
signed Tate products. Source: Stacks 03PK, [lem-asd-etale-finite-twist-pullback]
(blueprint: lem-pur-relative-support-coordinate-model). -/
def IsNormalizedCoordinateTateProduct (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u})
    (p : ∀ r s : ℤ, Scheme.finiteEtaleTateSheaf A m T hA r ⊗
      Scheme.finiteEtaleTateSheaf A m T hA s ≅ Scheme.finiteEtaleTateSheaf A m T hA (r + s)) :
    Prop :=
  (∀ r : ℤ, p 0 r = λ_ (Scheme.finiteEtaleTateSheaf A m T hA r) ≪≫
    eqToIso (congrArg (Scheme.finiteEtaleTateSheaf A m T hA) (zero_add r).symm)) ∧
  (∀ r : ℤ, p r 0 = ρ_ (Scheme.finiteEtaleTateSheaf A m T hA r) ≪≫
    eqToIso (congrArg (Scheme.finiteEtaleTateSheaf A m T hA) (add_zero r).symm)) ∧
  (∀ n : ℕ, p (.ofNat (n + 1)) 1 = Iso.refl _) ∧
  (∀ r s d : ℤ,
    (p r s).hom ▷ Scheme.finiteEtaleTateSheaf A m T hA d ≫ (p (r + s) d).hom =
      (α_ (Scheme.finiteEtaleTateSheaf A m T hA r)
        (Scheme.finiteEtaleTateSheaf A m T hA s)
        (Scheme.finiteEtaleTateSheaf A m T hA d)).hom ≫
      Scheme.finiteEtaleTateSheaf A m T hA r ◁ (p s d).hom ≫
        (p r (s + d)).hom ≫
          eqToHom (congrArg (Scheme.finiteEtaleTateSheaf A m T hA) (add_assoc r s d).symm)) ∧
  (∀ r s : ℤ,
    (β_ (Scheme.finiteEtaleTateSheaf A m T hA r)
      (Scheme.finiteEtaleTateSheaf A m T hA s)).hom ≫ (p s r).hom ≫
        eqToHom (congrArg (Scheme.finiteEtaleTateSheaf A m T hA) (add_comm s r)) =
      (p r s).hom) ∧
  (∀ n : ℕ,
    (p (.ofNat (n + 1)) (.negSucc n)).hom ≫
      eqToHom (congrArg (Scheme.finiteEtaleTateSheaf A m T hA)
        (add_neg_cancel (Int.ofNat (n + 1)))) =
      (ihom.ev (Scheme.finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
        (Scheme.finiteEtaleTateSheaf A m T hA 0))

/-- The normalized product family exists uniquely.
Source: Stacks 03PK and [lem-asd-etale-finite-twist-pullback]
(blueprint: lem-pur-relative-support-coordinate-model).
Proof: the published p-family gives existence. Its unit and concatenation rules
fix all nonnegative products. Evaluation fixes contraction of each positive line
with its negative dual. Locally choose a basis of the root line; associativity and
symmetry then determine every mixed-sign and negative product on the basis and its
dual. The forced coefficients are one, so the maps are independent of the checking
basis. Equality can be checked on this etale cover, giving global uniqueness. -/
theorem coordinateTateProduct_existsUnique (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u}) (hT : IsUnit (m : Γ(T, ⊤))) :
    ∃! p : ∀ r s : ℤ, Scheme.finiteEtaleTateSheaf A m T hA r ⊗
        Scheme.finiteEtaleTateSheaf A m T hA s ≅ Scheme.finiteEtaleTateSheaf A m T hA (r + s),
      IsNormalizedCoordinateTateProduct A m hA T p := by
  sorry

/-- The unique concatenation/evaluation-normalized signed product.
Source: Stacks 03PK and [lem-asd-etale-finite-twist-pullback]
(blueprint: lem-pur-relative-support-coordinate-model). -/
def coordinateTateProduct (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (r s : ℤ) :
    Scheme.finiteEtaleTateSheaf A m T hA r ⊗
        Scheme.finiteEtaleTateSheaf A m T hA s ≅
      Scheme.finiteEtaleTateSheaf A m T hA (r + s) :=
  (coordinateTateProduct_existsUnique A m hm hA T hT).choose r s

/-- The geometric data of precisely one simultaneous-coordinate chart in the item.
The map on the support and its cartesian square express scheme-theoretic inverse image,
not just equality of underlying closed sets. Source: Stacks 0FUE
(blueprint: lem-pur-relative-support-coordinate-model). -/
structure RelativeSupportCoordinates (P : WeilConjectures.PurityFiniteSetting.{u}) where
  S : Scheme.{u}
  X : Scheme.{u}
  Y : Scheme.{u}
  T : Scheme.{u}
  base : S ⟶ Spec (.of P.field.k)
  pX : X ⟶ S
  pY : Y ⟶ S
  [smoothX : Smooth pX]
  [smoothY : Smooth pY]
  i : Y ⟶ X
  [closed : IsClosedImmersion i]
  overBase : i ≫ pX = pY
  e : T ⟶ X
  [etale : Etale e]
  a : ℕ
  b : ℕ
  h : T ⟶ AffineSpace (ULift.{u} (Fin (a + b))) S
  [etaleCoordinates : Etale h]
  coordinatesOver : h ≫ (AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S) = e ≫ pX
  supportCoordinates : pullback i e ⟶ AffineSpace (ULift.{u} (Fin a)) S
  cartesian : IsPullback supportCoordinates (pullback.snd i e)
    (AffineSpace.zeroLastCoordinates S a b) h

attribute [instance] RelativeSupportCoordinates.smoothX RelativeSupportCoordinates.smoothY
  RelativeSupportCoordinates.closed RelativeSupportCoordinates.etale
  RelativeSupportCoordinates.etaleCoordinates

namespace RelativeSupportCoordinates

variable {P : WeilConjectures.PurityFiniteSetting.{u}} (C : RelativeSupportCoordinates P)

/-- The normal affine space is over the ground field, not over the arbitrary base.
Source: the coordinate comparison of DAG step 6
(blueprint: lem-pur-relative-support-coordinate-model). -/
abbrev normalSpace : Scheme.{u} :=
  AffineSpace (ULift.{u} (Fin C.b)) (Spec (.of P.field.k))

/-- The origin of the normal affine space is its actual zero section.
Source: Stacks 09XP and DAG step 6
(blueprint: lem-pur-relative-support-coordinate-model). -/
abbrev origin : Spec (.of P.field.k) ⟶ C.normalSpace :=
  AffineSpace.zeroSection (ULift.{u} (Fin C.b)) (Spec (.of P.field.k))

/-- The normal map retains, in order, exactly the last `b` coordinates of the chart.
Source: Stacks 0FUE and DAG steps 5--6
(blueprint: lem-pur-relative-support-coordinate-model). -/
def normalMap : C.T ⟶ C.normalSpace :=
  AffineSpace.homOfVector (C.e ≫ C.pX ≫ C.base)
    (fun j ↦ C.h.appTop (AffineSpace.coord C.S (ULift.up (Fin.natAdd C.a j.down))))

/-- The support is the inverse image of the origin under the specified normal map.
Source: Stacks 0FUE and the coordinate zero-locus formula
(blueprint: lem-pur-relative-support-coordinate-model).
Proof: the cartesian square identifies the support with the common zero locus of the
last coordinates. The zero-section locus is the common zero locus of all normal
coordinates. Pulling those coordinates back by `normalMap` gives exactly the last
coordinates of `h`, hence the two closed subsets agree. -/
theorem normal_support :
    Set.range (pullback.snd C.i C.e).base =
      C.normalMap.base ⁻¹' Set.range C.origin.base := by
  sorry

/-- Signed finite Tate coefficients at the actual coefficient-ring characteristic.
This permits every positive truncation index, without any ramification divisibility
hypothesis. Source: Stacks 03PK, [def-asd-finite-etale-tate-sheaf], DAG steps 2, 7
(blueprint: lem-pur-relative-support-coordinate-model). -/
def normalTwist (r : ℤ) :
    Sheaf C.normalSpace.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient) :=
  Scheme.finiteEtaleTateSheaf P.Coefficient (ringChar P.Coefficient) C.normalSpace
    (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) r

/-- The coefficient sheaf viewed in degree zero in the bounded-below derived category.
Source: the right-derived-support convention, Stacks 09XP
(blueprint: lem-pur-relative-support-coordinate-model). -/
def normalTwistComplex (r : ℤ) :
    DerivedCategory.Plus
      (Sheaf C.normalSpace.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj (C.normalTwist r)

/-- The coordinate comparison in its canonical pullback direction. Its inverse is the
isomorphism displayed in the node. The source is global supported cohomology on the
normal affine space, and the target is the supported stalk on the chart. Exactness of
geometric stalks identifies the latter with the stalk of the derived support sheaf.
Source: Stacks 09XP and DAG steps 1, 5--6
(blueprint: lem-pur-relative-support-coordinate-model). -/
def rawComparison {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ C.T) (r : ℤ) :
    (Etale.coordinateGlobalSupport P.Coefficient C.origin).rightDerivedFunctorPlus.obj
        (C.normalTwistComplex r) ⟶
      (Etale.coordinateSupportedStalk P.Coefficient
        (pullback.snd C.i C.e) t).rightDerivedFunctorPlus.obj
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
            C.normalMap).mapDerivedCategoryPlus.obj (C.normalTwistComplex r)) :=
  (Etale.coordinateDerivedGlobalToStalk P.Coefficient C.origin (pullback.snd C.i C.e)
    C.normalMap C.normal_support t).app (C.normalTwistComplex r)

/-- The normalized signed Tate pullback from the published all-index theorem.
That theorem fixes positive powers on roots and negative powers by evaluation; its
choice therefore determines the pullback comparison, not an arbitrary line isomorphism.
Source: finite Tate inverse-image theorem, DAG steps 2, 7
(blueprint: lem-pur-relative-support-coordinate-model). -/
def twistPullback (r : ℤ) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) C.normalMap).obj
        (C.normalTwist r) ≅
      Scheme.finiteEtaleTateSheaf P.Coefficient (ringChar P.Coefficient) C.T
        (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) r :=
  coordinateTatePullback P.Coefficient (ringChar P.Coefficient)
    (coordinateCoefficientCharacteristic_pos P)
    (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) C.normalMap
    (coordinateCoefficientCharacteristic_unit P (C.normalSpace ↘ Spec (.of P.field.k)))
    (coordinateCoefficientCharacteristic_unit P
      (C.normalMap ≫ (C.normalSpace ↘ Spec (.of P.field.k)))) r

/-- The same signed finite Tate coefficient, on the chart itself.
Source: finite Tate sheaf, DAG steps 2, 7
(blueprint: lem-pur-relative-support-coordinate-model). -/
def chartTwist (r : ℤ) :
    Sheaf C.T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient) :=
  Scheme.finiteEtaleTateSheaf P.Coefficient (ringChar P.Coefficient) C.T
    (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) r

/-- Place the chart coefficient in degree zero.
Source: Stacks 09XP (blueprint: lem-pur-relative-support-coordinate-model). -/
def chartTwistComplex (r : ℤ) :
    DerivedCategory.Plus (Sheaf C.T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj (C.chartTwist r)

/-- The canonical coordinate comparison with exactly the specified Tate sheaf on the
chart and exactly the geometric stalk of the derived support sheaf as target.
Source: Stacks 09XP and DAG steps 1, 5--7
(blueprint: lem-pur-relative-support-coordinate-model). -/
def comparison {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ C.T) (r : ℤ) :
    (Etale.coordinateGlobalSupport P.Coefficient C.origin).rightDerivedFunctorPlus.obj
        (C.normalTwistComplex r) ⟶
      ((Scheme.pointSmallEtale t).sheafFiber
        (A := ModuleCat.{u + 1} P.Coefficient)).mapDerivedCategoryPlus.obj
        ((Etale.coordinateSupportSheaf P.Coefficient
          (pullback.snd C.i C.e)).rightDerivedFunctorPlus.obj
            (C.chartTwistComplex r)) :=
  C.rawComparison t r ≫
    (Etale.coordinateSupportedStalk P.Coefficient
      (pullback.snd C.i C.e) t).rightDerivedFunctorPlus.map
        (((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          C.normalMap).mapDerivedCategoryPlusSingleFunctor 0).hom.app (C.normalTwist r) ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map (C.twistPullback r).hom) ≫
    (Etale.coordinateSupportedStalkDerivationIso P.Coefficient
      (pullback.snd C.i C.e) t).hom.app (C.chartTwistComplex r)

/-- The normalized signed product identification for the two indicated twists.
Its data is the product from the published all-index theorem, with only the index
`b+(r-b)=r` transported. Source: finite Tate tensor theorem and DAG step 7
(blueprint: lem-pur-relative-support-coordinate-model). -/
def twistProduct (r : ℤ) :
    C.normalTwist (C.b : ℤ) ⊗ C.normalTwist (r - C.b) ≅ C.normalTwist r :=
  coordinateTateProduct P.Coefficient (ringChar P.Coefficient)
    (coordinateCoefficientCharacteristic_pos P)
    (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) C.normalSpace
    (coordinateCoefficientCharacteristic_unit P (C.normalSpace ↘ Spec (.of P.field.k)))
    (C.b : ℤ) (r - C.b) ≪≫
      eqToIso (congrArg C.normalTwist
        ((add_comm (C.b : ℤ) (r - C.b)).trans (sub_add_cancel r (C.b : ℤ))))

/-- The comparison respects the signed tensor identification `A(r)=A(b)⊗A(r-b)`.
The product is the normalized product of the finite Tate pullback theorem. This
is a square between the
comparison on the actual tensor sheaf and on `A(r)`, not a choice of trivializations.
Source: finite Tate tensor identifications and DAG step 7
(blueprint: lem-pur-relative-support-coordinate-model).
Proof: the kernel-normalized comparison is natural on all bounded-below coefficient
complexes. Apply its naturality to the degree-zero image of the tensor identification.
The normalizing germ map sends each pure tensor to the tensor of its restrictions, so
this square uses the same tensor identification on both sides, including dual powers. -/
theorem comparison_twist_identification {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ C.T) (r : ℤ) :
    (Etale.coordinateGlobalSupport P.Coefficient C.origin).rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor _ 0).map (C.twistProduct r).hom) ≫
        C.rawComparison t r =
      (Etale.coordinateDerivedGlobalToStalk P.Coefficient C.origin
        (pullback.snd C.i C.e) C.normalMap C.normal_support t).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            (C.normalTwist (C.b : ℤ) ⊗ C.normalTwist (r - C.b))) ≫
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          C.normalMap).mapDerivedCategoryPlus ⋙
          (Etale.coordinateSupportedStalk P.Coefficient
            (pullback.snd C.i C.e) t).rightDerivedFunctorPlus).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map (C.twistProduct r).hom) := by
  sorry

/-- The normal-slice comparison and the dimension assertion, including arbitrary base
schemes and every positive finite coefficient level.
Source: Stacks 0FUE, 09XP and the nine-step argument of this node
(blueprint: lem-pur-relative-support-coordinate-model).
Proof:
1. Using [lem-kun-04ca], [lem-exc-closed-ambient], [lem-exc-closed-support-triangle],
[lemma-weil-pbc-finite-direct-image-exact] and [prop-weil-pbc-inverse-image-modules-exact],
identify the support kernel with the exact closed pushforward of its extraordinary
inverse image, using the closed-supported sheaf equivalence and the ordinary closed
adjoint. This identifies its derived global sections and gives the localization triangle.
2. Use [cor-pur-affine-space-zero-section-purity], [lem-amb-cartier-kummer-map],
[def-weil-exceptional-inverse-image], [thm-weil-pbc-site-comparison], and
[lem-asd-etale-finite-twist-pullback]. Over a finite-type affine base, the ordered Cartier-Kummer
zero-section calculation
and the fully faithful site comparison give supported cohomology concentrated in degree
`2b`, with coefficient line `A(r-b)`. Tensor by this finite free constant line, also for
negative twists, using the signed Tate tensor and dual identifications.
3. Use [lem-kun-0eym]. Write any affine base as the directed union of its finitely generated
ground-field
subalgebras. The punctured normal spaces have finitely many principal-open charts, so
their inclusions are qcqs. Apply higher-direct-image continuity to these open inclusions.
4. Use [prop-weil-pbc-geometric-stalks-exact], [lem-kun-stalks-commute-colimits],
[lemma-openclosed-stalk-upperstar], [lemma-openclosed-stalk-lowerstar],
[det-pbc-conventions-module-cohomology] and
[lem-weil-pbc-filtered-colimit-abelian-groups-exact]. Take geometric stalks. Stalks commute with
colimits and are exact; module cohomology
agrees with abelian cohomology. The localization exact sequence in degrees zero and one
and its higher-degree identities commute with filtered colimits. The finite-stage
orientations have identity transition maps, hence give the same single nonzero group.
5. Use [lem-weil-pbc-etale-inverse-image-restriction],
[lem-weil-pbc-etale-restriction-injectives]. Restrict the chart etale-locally over an affine base
neighbourhood. Etale restriction
is literal restriction, is exact and preserves injectives, so it preserves the support
kernel and its derived stalk. The chart therefore has that same coordinate orientation.
6. Use [sbc-lem-strict-henselian-constant-cohomology]. Over the ground field the supported complex
has that same group, since the field is
algebraically closed. The canonical normal pullback takes the ordered coordinate class
to itself. Good truncation in degree `2b` consequently makes it an isomorphism.
7. Use [lem-pur-supported-cup-functoriality] and [lem-asd-etale-finite-twist-pullback].
Restriction, the continuity exchange maps, the ordered Cartier classes and good
truncation are functorial. The same signed tensor identifications at every stage give
twist compatibility. Empty products cover `b=0`; empty support has no supported points.
8. Use [lem-weil-pbc-etale-covering-base-change],
[lem-weil-pbc-etale-morphism-open-map], [sbc-lem-affine-space-smooth],
[lem-pc-smooth-flat] and [lem-weil-pbc-flat-lfp-open]. For a nonempty chart, its support has open
image in the base. Choose a minimal base
prime in that image and the generic point of the tangential affine fibre, then a point
of the support above it.
9. Use [lem-sc-etale-local-dimension] and [lem-weil-pbc-mv-polynomial-maximal-height].
Localizing at this minimal prime and quotienting its nil maximal ideal does not
change prime chains. On the fibre, the support local dimension at the chosen point is
zero and the ambient dimension is `b`, by etale dimension invariance and polynomial
maximal height. The two etale maps to `X` and `Y` preserve these local dimensions.
The dimension hypothesis at this point reads `b=0+c`. No infinite dimension is cancelled.
-/
theorem relative_support_coordinate_model (P : WeilConjectures.PurityFiniteSetting.{u})
    (C : RelativeSupportCoordinates P) :
    (∀ {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ C.T)
      (ht : Set.range t.base ⊆ Set.range (pullback.snd C.i C.e).base) (r : ℤ),
        IsIso (C.comparison t r)) ∧
    (∀ c : ℕ,
      (∀ y : C.Y,
        ringKrullDim (C.X.presheaf.stalk (C.i.base y)) =
          ringKrullDim (C.Y.presheaf.stalk y) + (c : WithBot ℕ∞)) →
      Nonempty (pullback C.i C.e : Scheme.{u}) → C.b = c) := by
  sorry

end RelativeSupportCoordinates
end AlgebraicGeometry
