/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients

import WeilConjectures.AlgebraicGeometry.Principal.PrincipalDualizingReduction
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalQuotientInternalHom
import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality

/-! # Finite reduction of the specified integral Verdier bidual map -/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
-- Keep the existing derived structures opaque during proof elaboration, as in
-- IntegralCoefficients. These attributes are local to this new proof module.
attribute [local irreducible] _root_.DerivedCategory.monoidalClosed
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryFactors
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open Scheme
attribute [local instance] _root_.DerivedCategory.braidedCategory'
attribute [local instance 2000] CommRing.toRing
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

universe v w

universe uA uB

section AbstractBidual
variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  (B : Type uB) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  (X : Scheme.{u})

end AbstractBidual

section IntegralVerdierFiniteSteps
variable {Λ : Type (u + 1)} [CommRing Λ] [IsDomain Λ]
  {r : Λ} (hr : r ∈ nonZeroDivisors Λ) (m : ℕ) (hm : 1 ≤ m)
  [Finite (Λ ⧸ Ideal.span {r ^ m})] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent (Λ ⧸ Ideal.span {r ^ m}) (Spec (.of k))]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX]
  [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
  [(R(aX)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint]
  (W : DerivedCategoryModule Λ X)
  (eW : W ≅ (R(aX)_![ModuleCat.{u + 1} Λ]).rightAdjoint.obj
    (constantComplex Λ (Spec (.of k))))
  {K : DerivedCategoryModule Λ X} {a b : ℤ}
  (hbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
    ((reductionModIdeal Λ X (Ideal.span {r ^ m})).obj K))
  (ht : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
    ((reductionModIdeal Λ X (Ideal.span {r ^ m})).obj K))

include hr hm eW hbc ht in
end IntegralVerdierFiniteSteps
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Cancel two invertible comparison maps in an abstract category. -/
private lemma iv_cancel_comparisons {C : Type v} [Category.{w} C]
    {P Q R S : C} (f : P ⟶ Q) (g : Q ≅ R) (h : R ⟶ S) [IsIso h]
    (q : P ⟶ S) (hq : IsIso q) (he : q = f ≫ g.hom ≫ h) : IsIso f := by
  have : IsIso (f ≫ g.hom ≫ h) := he ▸ hq
  exact IsIso.of_isIso_comp_right f (g.hom ≫ h)

/-- Precomposition by an isomorphism is invertible, proved before specialization. -/
private lemma iv_pre_isIso {C : Type v} [Category.{w} C] [MonoidalCategory C]
    [MonoidalClosed C] {P Q : C} (e : P ≅ Q) (W : C) :
    IsIso ((MonoidalClosed.pre e.inv).app W) := by infer_instance

/-- Cancel the canonical bidual comparison before specializing coefficient categories. -/
private lemma iv_abstract_bidual
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
    (W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (WB : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
    (α : ∀ M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A),
      E.obj ((ihom M).obj W) ≅ (ihom (E.obj M)).obj WB)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (he : (derivedHomToIhomIhomNatTrans B X WB).app (E.obj K) =
      E.map ((derivedHomToIhomIhomNatTrans A X W).app K) ≫
        (α ((ihom K).obj W)).hom ≫ (MonoidalClosed.pre (α K).inv).app WB)
    (hq : IsIso ((derivedHomToIhomIhomNatTrans B X WB).app (E.obj K))) :
    IsIso (E.map ((derivedHomToIhomIhomNatTrans A X W).app K)) := by
  have := iv_pre_isIso (α K) WB
  exact iv_cancel_comparisons _ (α ((ihom K).obj W)) _ _ hq he

/-- Restriction of derived coefficient extension is ordinary reduction. -/
private lemma iv_restrictionExtension {R : Type (u + 1)} [CommRing R]
    (r : R) (m : ℕ) (X : Scheme.{u}) (K : DerivedCategoryModule R X) :
    Nonempty ((principalRestriction r m X).obj ((principalExtension r m X).obj K) ≅
      (reductionModIdeal R X (Ideal.span {r ^ m})).obj K) := by
  obtain ⟨e⟩ := nonempty_iso_derivedRestrictScalars_derivedExtendScalars
    (Ideal.Quotient.mk_surjective (I := Ideal.span {r ^ m})) Ideal.mk_ker X K
  let eQ := (Submodule.quotEquivOfEq _ _
    (Ideal.mk_ker (I := Ideal.span {r ^ m}))).toModuleIso
  exact ⟨e ≪≫ ((derivedTensor (ModuleCat.{u + 1} R) X).obj K).mapIso
    ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).mapIso eQ))⟩

/-- A cone argument using only abstract triangulated structure and object comparisons. -/
private lemma iv_generic_reduction_iso {C D : Type v} [Category.{w} C] [Category.{w} D]
    [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (E : C ⥤ D) (U : D ⥤ C) [U.CommShift ℤ] [U.IsTriangulated]
    (adj : E ⊣ U)
    (F : C ⥤ C) [F.CommShift ℤ] [F.IsTriangulated]
    (he : ∀ M : C, Nonempty (U.obj (E.obj M) ≅ F.obj M))
    {K L : C} (f : K ⟶ L) (hf : IsIso (E.map f)) : IsIso (F.map f) := by
  let : E.CommShift ℤ := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  have : E.IsTriangulated := adj.isTriangulated_leftAdjoint
  obtain ⟨M, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
  have hM : IsZero (E.obj M) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ (E.map_distinguished _ hT)).2 hf
  obtain ⟨e⟩ := he M
  have hF : IsZero (F.obj M) := (U.map_isZero hM).of_iso e.symm
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
    (F.map_distinguished _ hT)).1 hF

/-- Exactness transfers an extended isomorphism back to reduction. -/
private lemma iv_reduction_iso {R : Type (u + 1)} [CommRing R]
    (r : R) (m : ℕ) (X : Scheme.{u}) {K L : DerivedCategoryModule R X} (f : K ⟶ L)
    (hf : IsIso ((principalExtension r m X).map f)) :
    IsIso ((reductionModIdeal R X (Ideal.span {r ^ m})).map f) := by
  let E := principalExtension r m X
  let adj := derivedExtendScalarsAdjunction
    (Ideal.Quotient.mk_surjective (I := Ideal.span {r ^ m})) Ideal.mk_ker X
  exact iv_generic_reduction_iso E (principalRestriction r m X) adj
    (reductionModIdeal R X (Ideal.span {r ^ m}))
    (iv_restrictionExtension r m X) f hf

/-- The reduction of the actual evaluation-transpose bidual map is invertible.

Source: latest blueprint, thm-coef-integral-verdier.proof.md, paragraph 2.
(blueprint: lem-k7-principal-verdier-bidual-reduction)

Proof: extension of K is constructible with quotient Tor interval [a+1,b]. Identify the
extended dualizing object with the finite dualizing complex. The principal quotient Hom
comparison gives the displayed canonical bidual identity. The finite bidual map and
both comparison factors are invertible; cancel them to prove extension of the given
bidual map invertible. Extension is triangulated by its adjunction to exact restriction.
Its image of a cone of this map is therefore zero. Restrict and use the objectwise
extension/reduction comparison on that cone. Its reduction is zero, so exactness of
reduction proves the stated map invertible. No naturality of arbitrarily chosen
objectwise isomorphisms is assumed. -/
theorem principalVerdierBidualReduction :
    IsIso ((reductionModIdeal Λ X (Ideal.span {r ^ m})).map
      ((derivedHomToIhomIhomNatTrans (ModuleCat.{u + 1} Λ) X W).app K)) := by
  let B := Λ ⧸ Ideal.span {r ^ m}
  let E := principalExtension r m X
  obtain ⟨eK⟩ := iv_restrictionExtension r m X K
  have hKbc : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} B) X (E.obj K) :=
    (boundedConstructible_derivedRestrictScalars_iff (Ideal.span {r ^ m}) _).1
      ((DerivedCategory.boundedConstructible _ X).prop_of_iso eK.symm hbc)
  have hKt : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} B) X (a + 1) b (E.obj K) := by
    apply torAmplitudeIn_derivedExtendScalars Ideal.Quotient.mk_surjective Ideal.mk_ker
      (pow_mem hr m)
    let eQ := (Submodule.quotEquivOfEq _ _
      (Ideal.mk_ker (I := Ideal.span {r ^ m}))).toModuleIso
    let e := ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapIso
      ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso eQ))
    exact (DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso e.symm ht
  obtain ⟨w⟩ := principalDualizingReduction hr m aX W eW
  obtain ⟨β, _, _, _, _, hδ⟩ := principalQuotient_internalHom r m X
    (mul_right_injective₀ (nonZeroDivisors.ne_zero hr)) hm
  have hfin := isIso_verdierDualDoubleDual_app B aX ⟨hKbc, a + 1, b, hKt⟩
  change IsIso ((derivedHomToIhomIhomNatTrans (ModuleCat.{u + 1} B) X
    (dualizingComplex B aX)).app (E.obj K)) at hfin
  have hN : IsIso (E.map
      ((derivedHomToIhomIhomNatTrans (ModuleCat.{u + 1} Λ) X W).app K)) :=
    iv_abstract_bidual (ModuleCat.{u + 1} Λ) (ModuleCat.{u + 1} B) X E W
      (dualizingComplex B aX) (principalDualIso r m X β w) K
      (hδ W (dualizingComplex B aX) w K) hfin
  exact iv_reduction_iso r m X _ hN

end AlgebraicGeometry.Etale
