/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.WeilTensorProduct
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses

/-! # Finite truncation windows for derived tensor

Source: Stacks Project, Cohomology on Sites, Tag 094H, first equality in the proof,
with the cutoffs depending on the opposite factor's upper cohomological bound
(blueprint: lem-weil-pbc-derived-tensor-truncation-window).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

section Generic

open CategoryTheory.Pretriangulated MonoidalCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A] [HasDerivedCategory.{w} A]

variable [∀ X Y : GradedObject ℤ A, GradedObject.HasTensor X Y]
  [∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  [∀ X Y Z W : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X Y Z W]

omit [Abelian.HasFunctorialFlatResolution A] [HasDerivedCategory.{w} A]
  [∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ X Y Z : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  [∀ X Y Z W : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X Y Z W] in
/-- The acyclic-complex definition implies the categorical K-flatness predicate. -/
private theorem kFlat_of_right_acyclic (P : HomotopyCategory A (.up ℤ))
    (hP : ∀ N : CochainComplex A ℤ, N.Acyclic →
      (CochainComplex.mapBifunctor N P.as (MonoidalCategory.curriedTensor A)).Acyclic) :
    (HomotopyCategory.quasiIso A (.up ℤ)).kFlat P := by
  rw [HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  have hN' :=
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic N.as).1 hN
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor N.as P.as (MonoidalCategory.curriedTensor A))).2
      (hP N.as hN')
  refine ⟨?_, hr⟩
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr

private theorem tensor_truncGE_left (K L : DerivedCategory A) (b i a : ℤ)
    [L.IsLE b] (ha : a ≤ i - b) :
    IsIso ((DerivedCategory.homologyFunctor A i).map
      (((DerivedCategory.TStructure.t.truncGEπ a).app K) ▷ L)) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := (t.triangleLEGE (a - 1) a (by omega)).obj K
  let F := tensorRight L
  have hT := F.map_distinguished T (t.triangleLEGE_distinguished (a - 1) a (by omega) K)
  have hbound : (F.mapTriangle.obj T).obj₁.IsLE (i - 1) := by
    change (((t.truncLE (a - 1)).obj K) ⊗ L).IsLE (i - 1)
    have h := DerivedCategory.isLE_tensor ((t.truncLE (a - 1)).obj K) L (a - 1) b
    exact t.isLE_of_le _ (a - 1 + b) (i - 1) (by omega)
  let H := DerivedCategory.homologyFunctor A 0
  have h₀ := DerivedCategory.isZero_of_isLE (F.mapTriangle.obj T).obj₁
    (i - 1) i (by omega)
  have h₁ := DerivedCategory.isZero_of_isLE (F.mapTriangle.obj T).obj₁
    (i - 1) (i + 1) (by omega)
  have : Mono ((H.shift i).map (F.mapTriangle.obj T).mor₂) :=
    (H.homologySequence_mono_shift_map_mor₂_iff _ hT i).2 (h₀.eq_of_src _ _)
  have : Epi ((H.shift i).map (F.mapTriangle.obj T).mor₂) :=
    (H.homologySequence_epi_shift_map_mor₂_iff _ hT i (i + 1) rfl).2
      (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((H.shift i).map (F.mapTriangle.obj T).mor₂)

private theorem tensor_truncGE_right (K L : DerivedCategory A) (b i a : ℤ)
    [K.IsLE b] (ha : a ≤ i - b) :
    IsIso ((DerivedCategory.homologyFunctor A i).map
      (K ◁ ((DerivedCategory.TStructure.t.truncGEπ a).app L))) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := (t.triangleLEGE (a - 1) a (by omega)).obj L
  let F := tensorLeft K
  have hT := F.map_distinguished T (t.triangleLEGE_distinguished (a - 1) a (by omega) L)
  have hbound : (F.mapTriangle.obj T).obj₁.IsLE (i - 1) := by
    change (K ⊗ ((t.truncLE (a - 1)).obj L)).IsLE (i - 1)
    have h := DerivedCategory.isLE_tensor K ((t.truncLE (a - 1)).obj L) b (a - 1)
    exact t.isLE_of_le _ (b + (a - 1)) (i - 1) (by omega)
  let H := DerivedCategory.homologyFunctor A 0
  have h₀ := DerivedCategory.isZero_of_isLE (F.mapTriangle.obj T).obj₁
    (i - 1) i (by omega)
  have h₁ := DerivedCategory.isZero_of_isLE (F.mapTriangle.obj T).obj₁
    (i - 1) (i + 1) (by omega)
  have : Mono ((H.shift i).map (F.mapTriangle.obj T).mor₂) :=
    (H.homologySequence_mono_shift_map_mor₂_iff _ hT i).2 (h₀.eq_of_src _ _)
  have : Epi ((H.shift i).map (F.mapTriangle.obj T).mor₂) :=
    (H.homologySequence_epi_shift_map_mor₂_iff _ hT i (i + 1) rfl).2
      (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((H.shift i).map (F.mapTriangle.obj T).mor₂)

end Generic

namespace SheafOfModules


-- Use the tensor and counit APIs without unfolding their universal-property choices.
attribute [local irreducible] wfSiteDerivedTensor DerivedMonoidal.bifunctor
  DerivedMonoidal.counit

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- A fixed cohomology degree of derived tensor depends only on the two indicated
finite good-truncation windows. The comparison is the bifunctor image of the canonical
maps, so `IsIso` asserts invertibility of that particular module-sheaf morphism.
Source: Stacks Project, Tag 094H, corrected finite-window reduction; Tags 0118 and 06YU
(blueprint: lem-weil-pbc-derived-tensor-truncation-window).

Proof:
1. Equip module sheaves with their closed symmetric monoidal structure and functorial
   flat resolutions. Tensor descent supplies the resolving-subcategory comparison.
   The quotient tensor comparison and localization universal property identify
   `wfSiteDerivedTensor` naturally with the source derived-category tensor.
2. For any upper-bounded L, tensor the canonical truncation triangle
   tau_{<=a-1} K -> K -> tau_{>=a} K with L. The generic source tensor bound
   `DerivedCategory.isLE_tensor` puts its first term in degrees at most a-1+bL.
   This is at most i-1, so its cohomology in degrees i and i+1 vanishes.
3. The long exact homology sequence makes the image of the canonical truncation
   map an isomorphism in degree i. Repeat in the other variable, using that
   tau_{>=a} K retains the upper bound bK. Compose the two canonical maps.
4. Naturality of the tensor comparison transfers this isomorphism to the specified
   bifunctor map. Standard good-truncation bounds give both finite windows, including
   empty intervals. No points or finiteness assumptions are used. -/
theorem isIso_derivedTensor_truncationWindow
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w, max u v, (max u v) + 1} (SheafOfModules.{max u v, v, u, max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))]
    (K L : DerivedCategory.{w, max u v, (max u v) + 1} (SheafOfModules.{max u v, v, u, max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)))
    (bK bL : ℤ)
    (hK : ∀ q : ℤ, bK < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hL : ∀ q : ℤ, bL < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj L))
    (i a c : ℤ) (ha : a ≤ i - bL) (hc : c ≤ i - bK) :
    IsIso ((DerivedCategory.homologyFunctor _ i).map
      ((wfSiteDerivedTensor J R).map
        (CategoryTheory.Prod.mkHom ((DerivedCategory.TStructure.t.truncGEπ a).app K)
          ((DerivedCategory.TStructure.t.truncGEπ c).app L)))) ∧
    (∀ q : ℤ, q < a ∨ bK < q → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj
        ((DerivedCategory.TStructure.t.truncGE a).obj K))) ∧
    (∀ q : ℤ, q < c ∨ bL < q → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj
        ((DerivedCategory.TStructure.t.truncGE c).obj L))) := by
  classical
  let A := SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensorPreadditive R
  let := (nonempty_monoidalClosed_independentCoefficients (R := R)).some
  let := hasFunctorialFlatResolution_kfi R
  have : IsGrothendieckAbelian.{max u v} A :=
    isGrothendieckAbelianOfUniverses.{u, v, max u v, 0} J _
  have : ∀ X Y : GradedObject ℤ A, GradedObject.HasTensor X Y := by infer_instance
  have : ∀ X Y Z : GradedObject ℤ A,
      GradedObject.HasGoodTensor₁₂Tensor X Y Z := by infer_instance
  have : ∀ X Y Z : GradedObject ℤ A,
      GradedObject.HasGoodTensorTensor₂₃ X Y Z := by infer_instance
  have : ∀ X Y Z W : GradedObject ℤ A,
      GradedObject.HasTensor₄ObjExt X Y Z W := by infer_instance
  let instComplex : MonoidalCategory (CochainComplex A ℤ) := inferInstance
  have : DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso A (.up ℤ)) := by infer_instance
  let instDerived : MonoidalCategory (DerivedCategory A) := inferInstance
  let Q := HomotopyCategory.quotient A (.up ℤ)
  let instQuotient : Q.Monoidal := inferInstance
  let h := wf_site_derived_tensor_descent.{u, v, w, 0, 0} J R
  let S := h.choose
  let B := h.choose_spec.2.2.1.choose
  let comparison := h.choose_spec.2.2.1.choose_spec.1.some
  let d := h.choose_spec.2.2.1.choose_spec.2.choose_spec.some
  let th := MonoidalCategory.tensor (HomotopyCategory A (.up ℤ))
  let ec : Functor.uncurry.obj
      ((MonoidalCategory.curriedTensor A).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) ≅ MonoidalCategory.tensor (CochainComplex A ℤ) :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      change (f.1 ▷ X.2) ≫ (Y.1 ◁ f.2) ≫ 𝟙 _ = 𝟙 _ ≫ (f.1 ⊗ₘ f.2)
      simpa only [Category.comp_id, Category.id_comp] using
        (MonoidalCategory.tensorHom_def f.1 f.2).symm)
  let ed : (Q.prod Q) ⋙ B ≅ (Q.prod Q) ⋙ th :=
    comparison ≪≫ Functor.isoWhiskerRight ec Q ≪≫ (Functor.Monoidal.μNatIso Q).symm
  let eB : B ≅ th := NatIso.ofComponents
    (fun X ↦ ed.app (X.1.as, X.2.as)) (by
      intro X Y f
      simpa only [Functor.comp_map, Functor.prod_map, Prod.mkHom, Prod.eta,
        Iso.app_hom, Q, HomotopyCategory.quotient_map_out]
        using ed.hom.naturality (Prod.mkHom f.1.out f.2.out))
  let Z := (S.ι ⋙ DerivedCategory.Qh).prod (S.ι ⋙ DerivedCategory.Qh)
  let μ : Z ⋙ MonoidalCategory.tensor (DerivedCategory A) ⟶
      (S.ι.prod S.ι) ⋙ th ⋙ DerivedCategory.Qh :=
    { app X := ((DerivedMonoidal.counit DerivedCategory.Qh
        (HomotopyCategory.quasiIso A (.up ℤ))).app X.1.obj).app X.2.obj
      naturality X Y f :=
        Functor.LaxMonoidal.μ_natural DerivedCategory.Qh f.1.hom f.2.hom }
  have hμ : IsIso μ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have hk := (h.choose_spec.1 X.1.obj).1 X.1.property |>.1
    have hcat := kFlat_of_right_acyclic X.1.obj hk
    exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_left DerivedCategory.Qh
      (HomotopyCategory.quasiIso A (.up ℤ)) X.1.obj X.2.obj hcat
  have d' : (S.ι.prod S.ι) ⋙ B ⋙ DerivedCategory.Qh ≅
      Z ⋙ wfSiteDerivedTensor J R := by
    unfold wfSiteDerivedTensor
    exact d
  let rep : Z ⋙ wfSiteDerivedTensor J R ≅
      Z ⋙ MonoidalCategory.tensor (DerivedCategory A) :=
    d'.symm ≪≫ Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (S.ι.prod S.ι) eB) DerivedCategory.Qh ≪≫ (asIso μ).symm
  let V := (HomotopyCategory.quasiIso A (.up ℤ)).inverseImage S.ι
  let E := h.choose_spec.2.1.choose
  have : E.IsEquivalence := h.choose_spec.2.1.choose_spec.1
  have hloc : (S.ι ⋙ DerivedCategory.Qh).IsLocalization V :=
    Functor.IsLocalization.of_equivalence_target V.Q V _ E.asEquivalence
      h.choose_spec.2.1.choose_spec.2.some
  let ff := Localization.fullyFaithfulWhiskeringLeft Z (V.prod V) (DerivedCategory A)
  let e := ff.preimageIso rep
  have hKb : K.IsLE bK := (DerivedCategory.isLE_iff K bK).2 hK
  have hLb : L.IsLE bL := (DerivedCategory.isLE_iff L bL).2 hL
  let t := DerivedCategory.TStructure.t (C := A)
  have hleft := tensor_truncGE_left K L bL i a ha
  have hright := tensor_truncGE_right ((t.truncGE a).obj K) L bK i c hc
  refine ⟨?_, ?_, ?_⟩
  · let f := Prod.mkHom ((t.truncGEπ a).app K) ((t.truncGEπ c).app L)
    have hstd : IsIso ((DerivedCategory.homologyFunctor A i).map
        ((MonoidalCategory.tensor (DerivedCategory A)).map f)) := by
      change IsIso ((DerivedCategory.homologyFunctor A i).map
        (((t.truncGEπ a).app K) ⊗ₘ ((t.truncGEπ c).app L)))
      rw [MonoidalCategory.tensorHom_def, Functor.map_comp]
      exact IsIso.comp_isIso' hleft hright
    exact (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor A i)) f).2 hstd
  · intro q hq
    rcases hq with hq | hq
    · exact DerivedCategory.isZero_of_isGE _ a q hq
    · exact DerivedCategory.isZero_of_isLE _ bK q hq
  · intro q hq
    rcases hq with hq | hq
    · exact DerivedCategory.isZero_of_isGE _ c q hq
    · exact DerivedCategory.isZero_of_isLE _ bL q hq

end SheafOfModules
