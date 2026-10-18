/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Sheaf.AlgebraicGeometry.BoundedConstructibleHomSingle
import Sheaf.AlgebraicGeometry.BoundedConstructibleDevissage
import Sheaf.AlgebraicGeometry.EllAdicBoundedTriangulated
/-! # Internal-Hom preservation by finite truncations -/
@[expose] public section
universe u v w
open CategoryTheory Limits MonoidalCategory MonoidalClosed DerivedCategory
open ZeroObject
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
section Induction
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
private lemma prop_of_isGE_of_isLE_allSingles (Q : ObjectProperty (DerivedCategory C))
    [Q.ContainsZero] [Q.IsTriangulatedClosed₂]
    [Q.IsClosedUnderIsomorphisms] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ (X : C) (n : ℤ), P X → Q ((singleFunctor C n).obj X)) (n : ℕ) :
    ∀ (a : ℤ) (M : DerivedCategory C), M.IsGE a → M.IsLE (a + n - 1) →
      (∀ q, a ≤ q → q < a + n → P ((homologyFunctor C q).obj M)) → Q M := by
  induction n with
  | zero =>
    intro a M _ _ _
    have : M.IsLE (a - 1) := by simpa using ‹M.IsLE (a + ↑(0 : ℕ) - 1)›
    exact Q.prop_of_isZero (TStructure.t.isZero M (a - 1) a (by lia))
  | succ n ih =>
    intro a M _ _ hM
    set b : ℤ := a + n
    have hT := TStructure.t.triangleLTGE_distinguished b M
    -- the third term is `H^b M` placed in degree `b`
    have : ((TStructure.t.triangleLTGE b).obj M).obj₃.IsLE b := by
      have : M.IsLE b := TStructure.t.isLE_of_le M (a + ↑(n + 1) - 1) _ (by lia)
      exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj M) b)
    have : ((TStructure.t.triangleLTGE b).obj M).obj₃.IsGE b := by
      infer_instance
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((TStructure.t.triangleLTGE b).obj M).obj₃ b
    have h₁ : IsZero ((homologyFunctor C (b + 1)).obj ((TStructure.t.triangleLTGE b).obj M).obj₁) :=
      isZero_of_isLE _ (b - 1) _ (by lia)
    have h₀ : IsZero ((homologyFunctor C b).obj ((TStructure.t.triangleLTGE b).obj M).obj₁) :=
      isZero_of_isLE _ (b - 1) _ (by lia)
    have := isIso_homologyMap_mor₂ _ hT b (b + 1) rfl h₀ h₁
    have hY : P Y := P.prop_of_iso
      (asIso ((homologyFunctor C b).map ((TStructure.t.triangleLTGE b).obj M).mor₂) ≪≫
        (homologyFunctor C b).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C b).app Y)
      (hM b (by lia) (by lia))
    have h₃ : Q ((TStructure.t.triangleLTGE b).obj M).obj₃ := by
      exact Q.prop_of_iso e.symm (hP Y b hY)
    -- the first term is handled by induction
    have h₁ : Q ((TStructure.t.triangleLTGE b).obj M).obj₁ := by
      refine ih a _ ?_ ?_ fun q hq hq' ↦ ?_
      · exact inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj M) a)
      · exact TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      · have : IsIso ((homologyFunctor C q).map ((TStructure.t.triangleLTGE b).obj M).mor₁) :=
          isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
            (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
        exact P.prop_of_iso
          (asIso ((homologyFunctor C q).map ((TStructure.t.triangleLTGE b).obj M).mor₁)).symm
          (hM q hq (by lia))
    obtain ⟨M', hM', ⟨e'⟩⟩ := Q.ext_of_isTriangulatedClosed₂' _ hT h₁ h₃
    exact Q.prop_of_iso e'.symm hM'

end Induction
namespace CondensedRing
open Scheme
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ] {k : Type u} [Field k]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
/-- Internal-Hom closure follows from the single-sheaf calculation by two finite
truncation arguments, using exactness in its contravariant first variable.
Source: Bhatt--Scholze, Proposition 6.8.11(3), and `lem-sfb-dc-hom-preserves`.
(blueprint: lem-sfb-dc-hom-preserves) -/
theorem boundedConstructible_hom_closure
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)]
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hK : boundedConstructible (condensedRingObj Λ X.left) K)
    (hL : boundedConstructible (condensedRingObj Λ X.left) L) :
    boundedConstructible (condensedRingObj Λ X.left) ((ihom K).obj L) := by
  let P := boundedConstructible (condensedRingObj Λ X.left)
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : P.IsTriangulated := isTriangulated_boundedConstructible_ellAdic Λ X.left
  let C := Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
    (condensedRingObj Λ X.left)
  have : Abelian.HasFunctorialFlatResolution C := inferInstance
  have : HasColimitsOfShape ℤ C := inferInstance
  have : HasExactColimitsOfShape ℤ C := inferInstance
  have : ∀ M : C, PreservesColimitsOfShape ℤ ((curriedTensor C).obj M) :=
    fun M ↦ inferInstance
  have : ∀ M : C, PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj M) :=
    fun M ↦ inferInstance
  have : (HomotopyCategory.quasiIso C (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure :=
    inferInstance
  let Q : ObjectProperty _ := fun K ↦ P ((ihom K).obj L)
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e h ↦
    P.prop_of_iso ((internalHom.mapIso e.symm.op).app L) h⟩
  have : Q.ContainsZero := by
    refine ⟨0, isZero_zero _, P.prop_of_isZero ?_⟩
    apply (IsZero.iff_id_eq_zero _).2
    apply uncurry_injective
    exact ((tensorRight _).map_isZero (isZero_zero _)).eq_of_src _ _
  have : Q.IsTriangulatedClosed₂ := ⟨by
    intro T hT h₁ h₃
    obtain ⟨f, hf⟩ := exists_distinguished_ihom_pre T hT L
    exact ⟨_, P.ext_of_isTriangulatedClosed₂ _ hf h₃ h₁, ⟨Iso.refl _⟩⟩⟩
  have hsingle : ∀ (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)) (n : ℤ),
      IsConstructibleModuleObject (condensedRingObj Λ X.left) F →
      Q ((singleFunctor _ n).obj F) := by
    intro F n hF
    let A := (singleFunctor _ n).obj F
    let := (ihom.adjunction A).rightAdjointCommShift ℤ
    have : (ihom.adjunction A).CommShift ℤ :=
      (ihom.adjunction A).commShift_of_leftAdjoint ℤ
    have : (ihom A).IsTriangulated := (ihom.adjunction A).isTriangulated_rightAdjoint
    exact prop_of_boundedConstructibleModule (P.inverseImage (ihom A))
      (fun G hG ↦ boundedConstructible_hom_single Λ X n F G hF hG) hL
  let R : ObjectProperty _ := IsConstructibleModuleObject (condensedRingObj Λ X.left)
  have : R.IsClosedUnderIsomorphisms := ⟨fun e h ↦ constructible_of_iso _ e h⟩
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hK
  have : K.IsLE (a + (b - a + 1).toNat - 1) :=
    TStructure.t.isLE_of_le K b _ (by lia)
  exact prop_of_isGE_of_isLE_allSingles Q R hsingle (b - a + 1).toNat a K ha this
    (fun q _ _ ↦ hc q)
end CondensedRing
end AlgebraicGeometry.ProEtale
