/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E7
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

import Sheaf.SixFunctors.IntegralExtHomContinuity
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-! Integral compactness: an intermediate argument from blueprint main-20261015,
sec-six-functors-basics/sk-prop-int-compactness/sk-prop-int-compactness-compact.proof.md. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open CoproductsFromFiniteFiltered DirectSum

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem preserves_coproduct_of_finite_subcoproducts
    {A D : Type*} [Category A] [Category D]
    (F : A ⥤ D) [HasFiniteCoproducts A] [PreservesFiniteCoproducts F]
    {S : Type*} (B : S → A) [HasCoproduct B]
    [HasColimitsOfShape (Finset (Discrete S)) A]
    [PreservesColimit (liftToFinsetObj (Discrete.functor B)) F] :
    PreservesColimit (Discrete.functor B) F := by
  classical
  let L := liftToFinsetObj (Discrete.functor B)
  let k := finiteSubcoproductsCocone B
  let hk := isColimitOfPreserves F (isColimitFiniteSubproductsCocone B)
  let hf (T : Finset (Discrete S)) :=
    isColimitOfPreserves F (coproductIsCoproduct (fun s : T ↦ B s.val.as))
  let t (d : Cocone (Discrete.functor B ⋙ F)) : Cocone (L ⋙ F) :=
    { pt := d.pt
      ι :=
        { app := fun T ↦ (hf T).desc
            { pt := d.pt, ι := Discrete.natTrans (fun s ↦ d.ι.app s.as.val) }
          naturality := by
            intro T U h
            apply (hf T).hom_ext
            rintro ⟨s⟩
            change F.map (Sigma.ι (fun j : T ↦ B j.val.as) s) ≫
              F.map (L.map h) ≫ _ = F.map (Sigma.ι (fun j : T ↦ B j.val.as) s) ≫
                _ ≫ 𝟙 _
            rw [Category.comp_id, ← Category.assoc, ← F.map_comp]
            have hs : Sigma.ι (fun j : T ↦ B j.val.as) s ≫ L.map h =
                Sigma.ι (fun j : U ↦ B j.val.as) ⟨s.val, h.down.down s.property⟩ := by
              simp [L, liftToFinsetObj]
            rw [hs]
            exact ((hf U).fac _ ⟨⟨s.val, h.down.down s.property⟩⟩).trans
              ((hf T).fac
                { pt := d.pt, ι := Discrete.natTrans (fun s ↦ d.ι.app s.as.val) }
                ⟨s⟩).symm } }
  apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct B)
  refine ⟨fun d ↦ hk.desc (t d), ?_, ?_⟩
  · intro d s
    let T : Finset (Discrete S) := {s}
    let j : T := ⟨s, by simp [T]⟩
    have h0 : Sigma.ι (fun j : T ↦ B j.val.as) j ≫ k.ι.app T =
        Sigma.ι B s.as := by
      simp [k, finiteSubcoproductsCocone, j]
    have hh := congrArg
      (fun f ↦ F.map (Sigma.ι (fun j : T ↦ B j.val.as) j) ≫ f)
      (hk.fac (t d) T)
    change F.map (Sigma.ι (fun j : T ↦ B j.val.as) j) ≫
      F.map (k.ι.app T) ≫ hk.desc (t d) =
      F.map (Sigma.ι (fun j : T ↦ B j.val.as) j) ≫ (t d).ι.app T at hh
    rw [← Category.assoc, ← F.map_comp, h0] at hh
    exact hh.trans ((hf T).fac
      { pt := d.pt, ι := Discrete.natTrans (fun s ↦ d.ι.app s.as.val) } ⟨j⟩)
  · intro d m hm
    apply hk.hom_ext
    intro T
    apply (hf T).hom_ext
    rintro ⟨s⟩
    change F.map (Sigma.ι (fun j : T ↦ B j.val.as) s) ≫
      F.map (k.ι.app T) ≫ m =
      F.map (Sigma.ι (fun j : T ↦ B j.val.as) s) ≫
        F.map (k.ι.app T) ≫ hk.desc (t d)
    have hfac : F.map (k.ι.app T) ≫ hk.desc (t d) = (t d).ι.app T :=
      hk.fac (t d) T
    rw [hfac, ← Category.assoc, ← F.map_comp]
    have h0 : Sigma.ι (fun j : T ↦ B j.val.as) s ≫ k.ι.app T =
        Sigma.ι B s.val.as := by
      simp [k, finiteSubcoproductsCocone]
    rw [h0]
    exact (hm s.val).trans ((hf T).fac
      { pt := d.pt, ι := Discrete.natTrans (fun s ↦ d.ι.app s.as.val) } ⟨s⟩).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem directSum_bijective_of_preserves
    {A : Type*} [Category A] {S : Type w}
    (B : S → A) (c : Cofan B) (hc : IsColimit c)
    (F : A ⥤ AddCommGrpCat.{w}) [PreservesColimit (Discrete.functor B) F] :
    Function.Bijective
      (@DirectSum.toAddMonoid S _ _ (Classical.decEq S) _ _
        (fun s ↦ AddCommGrpCat.Hom.hom (F.map (c.inj s)))) := by
  classical
  let d : Cocone (Discrete.functor B ⋙ F) :=
    { pt := AddCommGrpCat.of (⨁ s, F.obj (B s))
      ι := Discrete.natTrans (fun s ↦
        AddCommGrpCat.ofHom (DirectSum.of (fun s ↦ F.obj (B s)) s.as)) }
  let hd : IsColimit d :=
    { desc := fun t ↦ AddCommGrpCat.ofHom
        (DirectSum.toAddMonoid (fun s ↦ (t.ι.app ⟨s⟩).hom))
      fac := by
        intro t s
        ext x
        exact DirectSum.toAddMonoid_of (β := fun s ↦ ↥(F.obj (B s))) (γ := ↥t.pt)
          (fun s ↦ (t.ι.app ⟨s⟩).hom) s.as x
      uniq := by
        intro t m h
        apply AddCommGrpCat.hom_ext
        apply DirectSum.addHom_ext
        intro s x
        simpa [d] using congrArg (fun f ↦ f.hom x) (h ⟨s⟩) }
  let e := hd.coconePointUniqueUpToIso (isColimitOfPreserves F hc)
  exact ConcreteCategory.bijective_of_isIso e.hom



private theorem constant_model_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  have hfinite (Y : Scheme.{u})
      {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ Y M) :
      HasFiniteConstantLocalModel Λ Y N := by
    obtain ⟨𝒰, h𝒰⟩ := h
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (𝒰.f i)).mapIso e).symm ≪≫ eP⟩⟩
  have hstrat (Y : Scheme.{u})
      {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : M ≅ N) (h : IsFiniteConstantStratified Λ Y M) :
      IsFiniteConstantStratified Λ Y N := by
    obtain ⟨S, hS⟩ := h
    exact ⟨S, fun a ↦ hfinite (S.domain a)
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  unfold IsConstantModelConstructible at hM ⊢
  by_cases h : CompactSpace X ∧ QuasiSeparatedSpace X
  · rw [if_pos h] at hM ⊢
    exact hstrat X e hM
  · rw [if_neg h] at hM ⊢
    intro U hU
    exact hstrat U.toScheme ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)

private theorem coproduct_isGE
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [HasColimitsOfShape (Discrete I) A]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (K : I → DerivedCategory A) (a : ℤ)
    (hK : ∀ i, (K i).IsGE a) : (∐ K).IsGE a := by
  apply (DerivedCategory.isGE_iff (∐ K) a).2
  intro q hq
  exact (isColimitOfPreserves (DerivedCategory.homologyFunctor A q)
    (coproductIsCoproduct K)).isZero_pt
    (Functor.isZero _ fun i ↦ (DerivedCategory.isGE_iff (K i.as) a).1 (hK i.as) q hq)

private theorem truncGE_preservesCoproducts
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [HasColimitsOfShape (Discrete I) A]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (a : ℤ) :
    PreservesColimitsOfShape (Discrete I) ((DerivedCategory.TStructure.t (C := A)).truncGE a) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := t.truncGE a
  let π := t.truncGEπ a
  have hK (K : I → DerivedCategory A) : PreservesColimit (Discrete.functor K) T := by
    let L := fun i ↦ T.obj (K i)
    have : HasCoproduct K := inferInstance
    have : HasCoproduct L := inferInstance
    have : (∐ L).IsGE a := coproduct_isGE L a (fun i ↦ inferInstance)
    let f : ∐ K ⟶ ∐ L := Sigma.desc (fun i ↦ π.app (K i) ≫ Sigma.ι L i)
    let r : T.obj (∐ K) ⟶ ∐ L := t.descTruncGE f a
    let c := sigmaComparison T K
    have hc : IsIso c := by
      refine ⟨⟨r, ?_, ?_⟩⟩
      · apply Sigma.hom_ext
        intro i
        change Sigma.ι L i ≫ (c ≫ r) = Sigma.ι L i ≫ 𝟙 _
        rw [← Category.assoc, ι_comp_sigmaComparison]
        apply t.from_truncGE_obj_ext
        simp only [Category.comp_id]
        rw [← Category.assoc]
        change (π.app (K i) ≫ T.map (Sigma.ι K i)) ≫ r =
          π.app (K i) ≫ Sigma.ι L i
        rw [← π.naturality (Sigma.ι K i)]
        change (Sigma.ι K i ≫ (t.truncGEπ a).app (∐ K)) ≫ t.descTruncGE f a = _
        rw [Category.assoc, t.π_descTruncGE, Sigma.ι_desc]
      · apply t.from_truncGE_obj_ext
        dsimp only [r]
        rw [← Category.assoc, t.π_descTruncGE]
        apply Sigma.hom_ext
        intro i
        change Sigma.ι K i ≫ f ≫ c = Sigma.ι K i ≫ π.app (∐ K) ≫ 𝟙 _
        calc
          _ = π.app (K i) ≫ (Sigma.ι L i ≫ c) := by simp [f]
          _ = π.app (K i) ≫ T.map (Sigma.ι K i) := by
            rw [ι_comp_sigmaComparison]
          _ = _ := by simpa using (π.naturality (Sigma.ι K i)).symm
    exact PreservesCoproduct.of_iso_comparison T K
  let : ∀ K : I → DerivedCategory A, PreservesColimit (Discrete.functor K) T := hK
  exact preservesColimitsOfShape_of_discrete T

private theorem truncLE_preservesCoproducts
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {I : Type*} [HasColimitsOfShape (Discrete I) (DerivedCategory A)]
    [HasColimitsOfShape (Discrete I) A]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete I) (DerivedCategory.homologyFunctor A n)]
    (a : ℤ) :
    PreservesColimitsOfShape (Discrete I) ((DerivedCategory.TStructure.t (C := A)).truncLE a) := by
  let t := DerivedCategory.TStructure.t (C := A)
  let T := t.truncLE a
  let ι := t.truncLEι a
  have hK (K : I → DerivedCategory A) : PreservesColimit (Discrete.functor K) T := by
    let L := fun i ↦ T.obj (K i)
    have : HasCoproduct K := inferInstance
    have : HasCoproduct L := inferInstance
    have : (∐ L).IsLE a := by
      apply (DerivedCategory.isLE_iff (∐ L) a).2
      intro q hq
      exact (isColimitOfPreserves (DerivedCategory.homologyFunctor A q)
        (coproductIsCoproduct L)).isZero_pt
        (Functor.isZero _ fun i ↦ DerivedCategory.isZero_of_isLE (L i.as) a q hq)
    let f : ∐ L ⟶ ∐ K := Sigma.desc (fun i ↦ ι.app (K i) ≫ Sigma.ι K i)
    let c := sigmaComparison T K
    have hcf : c ≫ ι.app (∐ K) = f := by
      apply Sigma.hom_ext
      intro i
      rw [← Category.assoc, ι_comp_sigmaComparison]
      simpa only [f, Sigma.ι_desc, Functor.id_map] using ι.naturality (Sigma.ι K i)
    -- The canonical truncation triangle supplies the other half of the coproduct.
    -- Prove invertibility by testing cohomology, where truncation retains a degree or zero.
    have hc : IsIso c := by
      apply (DerivedCategory.isIso_iff A c).2
      intro n
      by_cases hn : n ≤ a
      · have hι : IsIso ((DerivedCategory.homologyFunctor A n).map (ι.app (∐ K))) :=
          DerivedCategory.isIso_homologyFunctor_map_truncLTι_app _ _ _ (by omega)
        have hi (i : I) : IsIso
            ((DerivedCategory.homologyFunctor A n).map (ι.app (K i))) :=
          DerivedCategory.isIso_homologyFunctor_map_truncLTι_app _ _ _ (by omega)
        have hf : IsIso ((DerivedCategory.homologyFunctor A n).map f) := by
          let H := DerivedCategory.homologyFunctor A n
          have heq : H.map f = inv (sigmaComparison H L) ≫
              Limits.Sigma.map (fun i ↦ H.map (ι.app (K i))) ≫ sigmaComparison H K := by
            apply (cancel_epi (sigmaComparison H L)).1
            apply Sigma.hom_ext
            intro i
            simp only [ι_comp_sigmaComparison_assoc, IsIso.hom_inv_id_assoc,
              Sigma.ι_map_assoc]
            rw [← H.map_comp, Sigma.ι_desc, H.map_comp]
            change H.map (ι.app (K i)) ≫ H.map (Sigma.ι K i) =
              H.map (ι.app (K i)) ≫ Sigma.ι (fun i ↦ H.obj (K i)) i ≫ sigmaComparison H K
            rw [ι_comp_sigmaComparison]
          rw [heq]
          infer_instance
        have heq : (DerivedCategory.homologyFunctor A n).map c ≫
            (DerivedCategory.homologyFunctor A n).map (ι.app (∐ K)) =
            (DerivedCategory.homologyFunctor A n).map f := by
          rw [← Functor.map_comp, hcf]
        have : IsIso ((DerivedCategory.homologyFunctor A n).map c ≫
            (DerivedCategory.homologyFunctor A n).map (ι.app (∐ K))) := by
          rw [heq]
          exact hf
        exact IsIso.of_isIso_comp_right
          ((DerivedCategory.homologyFunctor A n).map c)
          ((DerivedCategory.homologyFunctor A n).map (ι.app (∐ K)))
      · have hz₁ := DerivedCategory.isZero_of_isLE (∐ L) a n (by omega)
        have hz₂ := DerivedCategory.isZero_of_isLE (T.obj (∐ K)) a n (by omega)
        exact isIso_of_source_target_iso_zero _ hz₁.isoZero hz₂.isoZero
    exact PreservesCoproduct.of_iso_comparison T K
  let : ∀ K : I → DerivedCategory A, PreservesColimit (Discrete.functor K) T := hK
  exact preservesColimitsOfShape_of_discrete T


-- Step 1: use the identity cover and the zero finitely presented condensed module.
private lemma finiteConstantLocalModel_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨HasZeroObject.zero.choose, ?_, ⟨?_⟩⟩
  · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  · exact ((CondensedRing.upperStar Λ _).map_isZero hM).iso
      (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))

-- The one-stratum stratification works also when the scheme is empty.
private lemma finiteConstantStratified_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsFiniteConstantStratified Λ X M := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  exact ⟨S, fun a ↦ finiteConstantLocalModel_of_isZero Λ _ _
    ((CondensedRing.upperStar Λ (S.immersion a)).map_isZero hM)⟩

private lemma constantModelConstructible_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsConstantModelConstructible Λ X M := by
  classical
  unfold IsConstantModelConstructible
  split
  · exact finiteConstantStratified_of_isZero Λ X M hM
  · exact fun U _ ↦ finiteConstantStratified_of_isZero Λ _ _
      ((CondensedRing.upperStar Λ U.ι).map_isZero hM)



private theorem finite_partial_sums_bound
    {A : Type u} [Category.{v} A] [Abelian A] [HasColimitsOfSize.{v, v} A]
    {I : Type v} (K : I → CochainComplex A ℤ) (b : ℤ)
    (hK : ∀ i r, r < b → IsZero ((K i).X r)) :
    ∀ (T : Finset (Discrete I)) (r : ℤ), r < b →
      IsZero (((liftToFinsetObj (Discrete.functor K)).obj T).X r) := by
  intro T r hr
  let E := HomologicalComplex.eval A (.up ℤ) r
  have hc := isColimitOfPreserves E
    (coproductIsCoproduct (fun i : T ↦ K i.val.as))
  exact hc.isZero_pt ((Functor.isZero_iff _).mpr (fun i ↦ hK i.as.val.as r hr))

private theorem hom_coproduct_of_filtered_continuity
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [HasColimitsOfSize.{v, v} A]
    (C : DerivedCategory A)
    (hcont : ∀ (J : Type v) [SmallCategory J] [IsFiltered J]
      (D : J ⥤ CochainComplex A ℤ),
      (∃ b : ℤ, ∀ i r, r < b → IsZero ((D.obj i).X r)) →
      IsIso (colimit.desc _
        ((DerivedCategory.Q ⋙ preadditiveCoyoneda.obj (op C)).mapCocone
          (colimit.cocone D))))
    (I : Type v) (K : I → CochainComplex A ℤ) (b : ℤ)
    (hK : ∀ i r, r < b → IsZero ((K i).X r)) :
    PreservesColimit (Discrete.functor K)
      (DerivedCategory.Q ⋙ preadditiveCoyoneda.obj (op C)) := by
  let F := DerivedCategory.Q ⋙ preadditiveCoyoneda.obj (op C)
  let D := liftToFinsetObj (Discrete.functor K)
  have : IsIso (colimit.post D F) :=
    hcont _ D ⟨b, finite_partial_sums_bound K b hK⟩
  let : PreservesColimit D F := preservesColimit_of_isIso_post _ _
  exact preserves_coproduct_of_finite_subcoproducts F K

private theorem hom_preserves_bounded_coproduct
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [IsGrothendieckAbelian.{v} A]
    (C : DerivedCategory A)
    (hcont : ∀ (J : Type v) [SmallCategory J] [IsFiltered J]
      (D : J ⥤ CochainComplex A ℤ),
      (∃ b : ℤ, ∀ i r, r < b → IsZero ((D.obj i).X r)) →
      IsIso (colimit.desc _
        ((DerivedCategory.Q ⋙ preadditiveCoyoneda.obj (op C)).mapCocone
          (colimit.cocone D))))
    (I : Type v) (K : I → DerivedCategory A) (b : ℤ)
    (hK : ∀ i, (K i).IsGE b) :
    PreservesColimit (Discrete.functor K) (preadditiveCoyoneda.obj (op C)) := by
  classical
  let H := preadditiveCoyoneda.obj (op C)
  have : HasColimitsOfSize.{v, v} A := IsGrothendieckAbelian.hasColimits A
  have hrep (i : I) := @DerivedCategory.exists_iso_Q_obj_of_isGE A _ _ _ (K i) b (hK i)
  choose L hL e using hrep
  let (i : I) : (L i).IsStrictlyGE b := hL i
  have hQH : PreservesColimit (Discrete.functor L) (DerivedCategory.Q ⋙ H) :=
    hom_coproduct_of_filtered_continuity C hcont I L b
      (fun i r hr ↦ (L i).isZero_of_isStrictlyGE b r hr)
  let := hQH
  have hQ : PreservesColimit (Discrete.functor L) DerivedCategory.Q := by
    apply preservesColimit_of_preserves_colimit_cocone
      (HomologicalComplex.isColimitCoconeOfHasColimitEval (Discrete.functor L))
    exact (DerivedCategory.isColimit_mapCocone_grothendieckSum A I L).some
  let := hQ
  have hH : PreservesColimit (Discrete.functor L ⋙ DerivedCategory.Q) H := by
    apply preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves DerivedCategory.Q (coproductIsCoproduct L))
    exact isColimitOfPreserves (DerivedCategory.Q ⋙ H) (coproductIsCoproduct L)
  let := hH
  exact preservesColimit_of_iso_diagram (F := H) (K₁ := Discrete.functor L ⋙ DerivedCategory.Q)
    (Discrete.natIso (fun i ↦ (e i.as).some.symm))


open Classical in
private theorem window_coproduct_of_continuity
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [IsGrothendieckAbelian.{v} A]
    (C : DerivedCategory A)
    (hcont : ∀ (J : Type v) [SmallCategory J] [IsFiltered J]
      (D : J ⥤ CochainComplex A ℤ),
      (∃ b : ℤ, ∀ i r, r < b → IsZero ((D.obj i).X r)) →
      IsIso (colimit.desc _
        ((DerivedCategory.Q ⋙ preadditiveCoyoneda.obj (op C)).mapCocone
          (colimit.cocone D))))
    (a : ℕ) (I : Type v) (K : I → DerivedCategory A) (c : Cofan K)
    (hc : IsColimit c) :
    let W := DerivedCategory.TStructure.t.truncLE 0 ⋙
      DerivedCategory.TStructure.t.truncGE (-(a : ℤ)) ⋙
        preadditiveCoyoneda.obj (op C)
    Function.Bijective (DirectSum.toAddMonoid (fun i ↦ (W.map (c.inj i)).hom)) := by
  let U := DerivedCategory.TStructure.t.truncLE (C := DerivedCategory A) 0
  let V := DerivedCategory.TStructure.t.truncGE (C := DerivedCategory A) (-(a : ℤ))
  let Y := preadditiveCoyoneda.obj (op C)
  have : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{v}
  have : HasColimitsOfSize.{v, v} A := IsGrothendieckAbelian.hasColimits A
  have : HasCoproducts.{v} A := fun I ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete I)
  have : HasCoproducts.{v} (DerivedCategory A) := derived_hasCoproducts
  have : PreservesColimitsOfShape (Discrete I) U := truncLE_preservesCoproducts 0
  have : PreservesColimitsOfShape (Discrete I) V := truncGE_preservesCoproducts _
  let T := U ⋙ V
  let L := fun i ↦ T.obj (K i)
  have : PreservesColimit (Discrete.functor L) Y :=
    hom_preserves_bounded_coproduct C hcont I L (-(a : ℤ)) (fun i ↦ inferInstance)
  let cT : Cofan L := Cofan.mk (T.obj c.pt) (fun i ↦ T.map (c.inj i))
  have hcT : IsColimit cT :=
    (Cofan.isColimitMapCoconeEquiv T K c).1 (isColimitOfPreserves T hc)
  exact directSum_bijective_of_preserves L cT hcT Y


open Classical in
/-- The canonical coproduct comparison after placing every target in one finite window.
Source: blueprint main-20261015, sk-prop-int-compactness-compact.proof.md,
paragraph (3), steps 13 and the truncation/sum comparison of step 14
(blueprint: lem-integral-window-coproduct-comparison).

Proof: In the Grothendieck abelian category of internal module sheaves, derived sums
are termwise and commute with cohomology. Both canonical truncations therefore commute
with sums, compatibly with their coprojections. The windowed targets have cohomology
in the common interval [-a,0]. Represent them by complexes supported in that interval.
The filtered diagram of finite partial sums has common termwise lower bound -a, so
integral Ext continuity applies to the constructible source C in degree zero. Its
colimit is the termwise direct sum. Hom into finite biproducts is a finite direct sum;
taking the filtered colimit gives the direct sum of Hom groups. Every map here comes
from a coprojection, hence the resulting bijection is precisely the displayed map.
This only asserts continuity for the finite-window functor; it asserts neither
compactness nor the window reduction for arbitrary unbounded targets. Empty families
and a=0 are included in the finite-partial-sum argument. -/
theorem integralWindowCoproductComparison
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (C : ConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X)
    (a : ℕ) :
    let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
    let _H : ObjectProperty A := IsConstantModelConstructible
      (Profinite.padicIntegersRingObj ℓ E) X
    ∀ (I : Type (u + 1)) (K : I → DerivedCategory A) (c : Cofan K), IsColimit c →
      let W := DerivedCategory.TStructure.t.truncLE 0 ⋙
        DerivedCategory.TStructure.t.truncGE (-(a : ℤ)) ⋙
          preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj C.obj))
      Function.Bijective (DirectSum.toAddMonoid (fun i ↦ (W.map (c.inj i)).hom)) := by
  classical
  dsimp only
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)
  let S := (DerivedCategory.singleFunctor A 0).obj C.obj
  let Y := preadditiveCoyoneda.obj (op S)
  have : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1}
  have : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  have hCS : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X S := by
    refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
    intro n
    by_cases hn : n = 0
    · subst n
      exact constant_model_iso _ X
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app C.obj).symm C.property
    · apply constantModelConstructible_of_isZero
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact DerivedCategory.isZero_of_isGE S 0 n hn
      · exact DerivedCategory.isZero_of_isLE S 0 n hn
  have hchar : ringChar k = p := ringChar.eq k p
  have : NeZero p := ⟨by omega⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos k p
  have : Fact (ringChar k).Prime := ⟨by simpa [hchar] using Fact.out (p := p.Prime)⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by simpa [hchar] using hpℓ⟩
  have hcont (J : Type (u + 1)) [SmallCategory J] [IsFiltered J]
      (D : J ⥤ CochainComplex A ℤ)
      (hb : ∃ b : ℤ, ∀ i r, r < b → IsZero ((D.obj i).X r)) :
      IsIso (colimit.desc _ ((DerivedCategory.Q ⋙ Y).mapCocone (colimit.cocone D))) := by
    obtain ⟨b, hb⟩ := hb
    let Z : Over (Spec (.of k)) := Over.mk (X ↘ Spec (.of k))
    let : LocallyOfFiniteType Z.hom :=
      show LocallyOfFiniteType (X ↘ Spec (.of k)) from inferInstance
    let : QuasiCompact Z.hom := show QuasiCompact (X ↘ Spec (.of k)) from inferInstance
    let : IsSeparated Z.hom := show IsSeparated (X ↘ Spec (.of k)) from inferInstance
    have hc := CondensedRing.integralExtHomContinuous (X := Z)
      S hCS D b hb 0
    let G := DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory A) (0 : ℤ) ⋙ Y
    have : IsIso (colimit.post D G) := hc
    have : PreservesColimit D G := preservesColimit_of_isIso_post G D
    have : PreservesColimit D (DerivedCategory.Q ⋙ Y) :=
      preservesColimit_of_natIso D
        (Functor.isoWhiskerLeft DerivedCategory.Q
          (Functor.isoWhiskerRight (shiftFunctorZero (DerivedCategory A) ℤ) Y))
    change IsIso (colimit.post D (DerivedCategory.Q ⋙ Y))
    infer_instance
  exact window_coproduct_of_continuity S hcont a

end AlgebraicGeometry.ProEtale
