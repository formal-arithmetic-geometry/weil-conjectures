/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SupportCohomologyTrianglePullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import Mathlib.CategoryTheory.Linear.FunctorCategory
import WeilConjectures.CategoryTheory.Sites.Point.Linear
import WeilConjectures.AlgebraicGeometry.FiniteEtaleUnitStalkInclusion

/-!
# Test
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite DerivedCategory

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

namespace Functor

variable {P : C ⥤ C} [P.Additive]

/-- The morphism of cochain complexes `P(K) ⟶ K` induced by a natural transformation
`τ : P ⟶ 𝟭 C`, natural in `K`. -/
noncomputable def mapHomologicalComplexToId (τ : P ⟶ 𝟭 C) :
    P.mapHomologicalComplex (ComplexShape.up ℤ) ⟶ 𝟭 _ where
  app K :=
    { f m := τ.app (K.X m)
      comm' i j _ := (τ.naturality (K.d i j)).symm }
  naturality K L φ := by
    ext m
    exact τ.naturality (φ.f m)

@[simp]
lemma mapHomologicalComplexToId_app_f (τ : P ⟶ 𝟭 C) (K : CochainComplex C ℤ) (m : ℤ) :
    ((mapHomologicalComplexToId τ).app K).f m = τ.app (K.X m) :=
  rfl

variable [HasDerivedCategory C] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

variable (P) in
/-- The natural transformation `D(P) ⟶ 𝟭` induced by a natural transformation
`τ : P ⟶ 𝟭 C` from an exact functor `P` to the identity. -/
noncomputable def mapDerivedCategoryToId (τ : P ⟶ 𝟭 C) : P.mapDerivedCategory ⟶ 𝟭 _ :=
  Localization.liftNatTrans Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q) Q P.mapDerivedCategory (𝟭 _)
    (whiskerRight (mapHomologicalComplexToId τ) Q ≫ Q.leftUnitor.hom)

lemma mapDerivedCategoryFactors_inv_app_comp_mapDerivedCategoryToId_app (τ : P ⟶ 𝟭 C)
    (K : CochainComplex C ℤ) :
    P.mapDerivedCategoryFactors.inv.app K ≫ (mapDerivedCategoryToId P τ).app (Q.obj K) =
      Q.map ((mapHomologicalComplexToId τ).app K) := by
  have hP : Localization.Lifting.iso Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (P.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q)
      P.mapDerivedCategory = P.mapDerivedCategoryFactors := rfl
  simp [mapDerivedCategoryToId, Localization.liftNatTrans_app, hP]

variable [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C] {F : C ⥤ D} [F.Additive]

/-- If `α : F ⟶ P ⋙ F` followed by `F(τ)` is multiplication by an integer `n`, then so is the
pullback map `RF ⟶ RF ∘ D(P)` followed by `RF(D(τ))`. -/
lemma rightDerivedPullback_app_comp_map_mapDerivedCategoryToId_app (α : F ⟶ P ⋙ F)
    (τ : P ⟶ 𝟭 C) (n : ℤ) (h : α ≫ whiskerRight τ F = n • 𝟙 F)
    (M : DerivedCategory C) :
    (rightDerivedPullback P α).app M ≫
        F.rightDerivedFunctor.map ((mapDerivedCategoryToId P τ).app M) = n • 𝟙 _ := by
  have := rightDerivedFunctor_hom_ext
    (rightDerivedPullback P α ≫ whiskerRight (mapDerivedCategoryToId P τ) _)
    (n • 𝟙 F.rightDerivedFunctor) (fun K ↦ by
      have hK : (NatTrans.mapHomologicalComplex α _).app K ≫
          (F.mapHomologicalComplex _).map ((mapHomologicalComplexToId τ).app K) =
            n • 𝟙 _ := by
        ext m
        simp only [HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f]
        exact congr_app h (K.X m)
      simp only [NatTrans.comp_app, whiskerRight_app, NatTrans.app_zsmul, NatTrans.id_app]
      rw [rightDerivedFunctorUnitQ_rightDerivedPullback_app'_assoc, ← Functor.map_comp,
        mapDerivedCategoryFactors_inv_app_comp_mapDerivedCategoryToId_app]
      erw [← rightDerivedFunctorUnitQ_naturality F ((mapHomologicalComplexToId τ).app K)]
      erw [← Q.map_comp_assoc, hK]
      simp)
  simpa using congr_app this M

end Functor

namespace Sheaf

/-- On a site with a terminal object `T`, the identification of the global sections with the
sections over `T` is the restriction map. -/
lemma ΓNatIsoSheafSections_hom_app_eq_ΓRes {C : Type*} [Category C]
    (J : GrothendieckTopology C) (A : Type*) [Category A]
    [HasWeakSheafify J A] [HasTerminal C] {T : C} (hT : IsTerminal T) (F : Sheaf J A) :
    (Sheaf.ΓNatIsoSheafSections J A hT).hom.app F = F.ΓRes (op T) := by
  simp only [Sheaf.ΓNatIsoSheafSections, Sheaf.ΓRes, Sheaf.coneΓ, Sheaf.ΓHomEquiv,
    Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app]
  erw [Equiv.symm_trans_apply, Equiv.symm_symm, Adjunction.homEquiv_counit,
    Adjunction.homEquiv_unit]
  simp [constantSheafAdj, Adjunction.comp_unit_app]
  rfl

end Sheaf

end CategoryTheory

namespace AlgebraicGeometry.Etale

open Scheme

section GlobalSections

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X X' : Scheme.{u}} (e : X' ⟶ X)

/-- The pullback of global sections `Γ(X, F) ⟶ Γ(X', e^* F)`, followed by the identification
`Γ(X', e^* F) ≅ Γ(X, e_* e^* F)`, is the map induced on global sections by the unit
`F ⟶ e_* e^* F`. -/
@[reassoc]
lemma ΓPullback_app_comp_lowerStarCompGlobalSectionsIso_inv_app
    (F : Sheaf X.smallEtaleTopology A) :
    (ΓPullback A e).app F ≫ (lowerStarCompGlobalSectionsIso A e).inv.app ((e)^*[A].obj F) =
      (Sheaf.Γ _ A).map ((upperStarLowerStarAdjunction A e).unit.app F) := by
  have := isIso_terminal_hom X
  rw [← cancel_mono ((lowerStarCompGlobalSectionsIso A e).hom.app _), assoc, Iso.inv_hom_id_app,
    ← cancel_mono ((Sheaf.ΓNatIsoSheafSections _ A terminalIsTerminal).hom.app
    ((e)^*[A].obj F))]
  have h := ΓPullback_app_comp_ΓRes A e (V := ⊤_ X.Etale) (W := ⊤_ X'.Etale)
    ((⊤_ X'.Etale).hom ≫ e ≫ inv (⊤_ X.Etale).hom) (by simp) F
  erw [comp_id]
  rw [Sheaf.ΓNatIsoSheafSections_hom_app_eq_ΓRes, h]
  simp only [lowerStarCompGlobalSectionsIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, assoc]
  rw [← Sheaf.ΓNatIsoSheafSections_hom_app_eq_ΓRes _ _ terminalIsTerminal ((e)^*[A].obj F),
    Iso.inv_hom_id_app]
  erw [(Sheaf.ΓNatIsoSheafSections _ A terminalIsTerminal).hom.naturality_assoc]
  rw [Sheaf.ΓNatIsoSheafSections_hom_app_eq_ΓRes, sectionsPullback_app]
  congr 1
  simp only [Category.comp_id]
  congr 1
  let P := PreservesTerminal.iso e.Etale
  have h₃ : (lowerStarCompSheafSectionsTerminalIso A e).hom.app ((e)^*[A].obj F) =
      ((e)^*[A].obj F).obj.map P.inv.op := rfl
  rw [h₃]
  congr 2
  exact (cancel_mono P.hom).1 (terminal.hom_ext _ _)

end GlobalSections

section Trace

private theorem unit_stalk_component
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (t : f.GeometricFiber s) :
    (Scheme.pointSmallEtale s).sheafFiber.map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G) ≫
      stalkRestrict (ModuleCat.{u + 1} R) f s t ((f)^*[ModuleCat.{u + 1} R].obj G) =
    eqToHom (by rw [t.2]; rfl) ≫
      ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t.1).app G).inv := by
  obtain ⟨t, rfl⟩ := t
  simp only [eqToHom_refl, Category.id_comp]
  erw [stalkRestrict_eq_counit]
  have hn := (upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t).inv.naturality
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G)
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  erw [Adjunction.left_triangle_components]
  simp

private theorem trace_stalk_component
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (t : f.GeometricFiber s) :
    sheafFiberToLowerStar (ModuleCat.{u + 1} R) f t ((f)^*[ModuleCat.{u + 1} R].obj G) ≫
      (Scheme.pointSmallEtale s).sheafFiber.map
        ((lowerStarUpperStarAdjunctionOfIsFinite (ModuleCat.{u + 1} R) f).counit.app G) =
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t.1).app G).hom ≫
      eqToHom (by rw [t.2]; rfl) := by
  obtain ⟨t, rfl⟩ := t
  erw [← finiteEtaleUnit_stalk_inclusion R f
    ((f)^*[ModuleCat.{u + 1} R].obj G) (t ≫ f) ⟨t, rfl⟩]
  simp only [eqToHom_refl, Category.comp_id]
  have hn := (upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t).hom.naturality
    ((lowerStarUpperStarAdjunctionOfIsFinite (ModuleCat.{u + 1} R) f).counit.app G)
  dsimp only [Functor.comp_map] at hn
  erw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp,
    Adjunction.right_triangle_components]
  simp

/-- **The finite étale trace after pullback is multiplication by the degree.** For a finite
étale `f` all of whose geometric fibres have `d` points, the unit `G ⟶ f_* f^* G` followed by the
trace `f_* f^* G ⟶ G`, the counit of `f_* ⊣ f^*`, is multiplication by `d`. -/
theorem unit_app_comp_lowerStarUpperStarAdjunctionOfIsFinite_counit_app
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (d : ℕ)
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nat.card (f.GeometricFiber s) = d) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G ≫
      (lowerStarUpperStarAdjunctionOfIsFinite (ModuleCat.{u + 1} R) f).counit.app G =
        (d : R) • 𝟙 G := by
  classical
  let A := ModuleCat.{u + 1} R
  let H := (f)^*[A].obj G
  let η := (upperStarLowerStarAdjunction A f).unit.app G
  let tr := (lowerStarUpperStarAdjunctionOfIsFinite A f).counit.app G
  apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro x
  let s := X.algClosurePoint x
  let Φ := (Scheme.pointSmallEtale s).sheafFiber (A := A)
  let : Fintype (f.GeometricFiber s) := Fintype.ofFinite _
  let ρ := fun t : f.GeometricFiber s ↦ stalkRestrict A f s t H
  let j := fun t : f.GeometricFiber s ↦ sheafFiberToLowerStar A f t H
  have htotal : ∑ t, ρ t ≫ j t = 𝟙 (Φ.obj ((f)_*[A].obj H)) := by
    apply (cancel_mono (Limits.Pi.lift ρ)).mp
    apply Limits.Pi.hom_ext
    intro t
    simp only [Category.assoc, Limits.Pi.lift_π]
    erw [Preadditive.sum_comp, Category.id_comp]
    simp only [Category.assoc]
    change ∑ a, ρ a ≫ (j a ≫ ρ t) = ρ t
    erw [Finset.sum_eq_single t]
    · simp [ρ, j]
    · intro a ha hat
      erw [sheafFiberToLowerStar_stalkRestrict_of_ne A f hat H, Limits.comp_zero]
    · intro ht
      exact (ht (Finset.mem_univ t)).elim
  simp only [CategoryTheory.Functor.map_comp,
    GrothendieckTopology.Point.sheafFiber_map_smul]
  change Φ.map η ≫ Φ.map tr = (d : R) • Φ.map (𝟙 G)
  erw [Φ.map_id]
  calc
    Φ.map η ≫ Φ.map tr = Φ.map η ≫ (∑ t, ρ t ≫ j t) ≫ Φ.map tr := by
      erw [htotal, Category.id_comp]
    _ = ∑ t, (Φ.map η ≫ ρ t) ≫ (j t ≫ Φ.map tr) := by
      erw [Preadditive.sum_comp, Preadditive.comp_sum]
      simp only [Category.assoc]
    _ = ∑ _t : f.GeometricFiber s, 𝟙 (Φ.obj G) := by
      apply Finset.sum_congr rfl
      intro t ht
      erw [unit_stalk_component R f G s t, trace_stalk_component R f G s t]
      simp
    _ = (d : R) • 𝟙 _ := by
      erw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
        hdeg _ s, ← Nat.cast_smul_eq_nsmul R]
end Trace

section DerivedTrace

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {Λ : Type (u + 1)} [CommRing Λ] {Y Y' : Scheme.{u}} (π : Y' ⟶ Y) [IsFinite π]
  [Etale π] (d : ℕ)

/-- **The finite étale trace on derived global sections** (blueprint
`det-tf-restriction-zero-trace-descent`): for a finite étale `π : Y' ⟶ Y` all of whose
geometric fibres have `d` points, the pullback `RΓ(Y, M) ⟶ RΓ(Y', π^* M)` of derived global
sections admits a trace `RΓ(Y', π^* M) ⟶ RΓ(Y, M)` whose composite with it is multiplication by
`d`. -/
theorem exists_rightDerivedPullback_app_comp_eq_smul
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Nat.card (π.GeometricFiber s) = d)
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ t, (Functor.rightDerivedPullback (π)^*[ModuleCat.{u + 1} Λ]
        (ΓPullback (ModuleCat.{u + 1} Λ) π)).app M ≫ t = (d : ℤ) • 𝟙 _ := by
  let A := ModuleCat.{u + 1} Λ
  have : PreservesLimitsOfSize.{0, 0} (π)_*[A] :=
    (upperStarLowerStarAdjunction A π).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (π)_*[A] := PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _
  have : PreservesColimitsOfSize.{0, 0} (π)_*[A] :=
    (lowerStarUpperStarAdjunctionOfIsFinite A π).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (π)_*[A] :=
    PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _
  let τ := (lowerStarUpperStarAdjunctionOfIsFinite A π).counit
  let α := (lowerStarCompGlobalSectionsIso A π).inv
  have hτ : (ΓPullback A π ≫ Functor.whiskerLeft _ α) ≫
      Functor.whiskerRight τ (Sheaf.Γ _ A) = (d : ℤ) • 𝟙 _ := by
    refine NatTrans.ext (funext fun G ↦ ?_)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, assoc, α,
      ΓPullback_app_comp_lowerStarCompGlobalSectionsIso_inv_app_assoc, ← Functor.map_comp,
      τ]
    rw [unit_app_comp_lowerStarUpperStarAdjunctionOfIsFinite_counit_app Λ π G d hdeg,
      Nat.cast_smul_eq_nsmul, Functor.map_nsmul, CategoryTheory.Functor.map_id,
      NatTrans.app_zsmul, NatTrans.id_app, natCast_zsmul]
  have hcomp := Functor.rightDerivedPullback_comp (π)^*[A] (π)_*[A] ((π)^*[A] ⋙ (π)_*[A])
    (Iso.refl _) (ΓPullback A π) α (ΓPullback A π ≫ Functor.whiskerLeft _ α) (by simp) M
  refine ⟨(Functor.rightDerivedPullback (π)_*[A] α).app _ ≫
    (Sheaf.Γ _ A).rightDerivedFunctor.map ((Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).inv.app M ≫
        (Functor.mapDerivedCategoryToId _ τ).app M), ?_⟩
  rw [← assoc, ← hcomp, assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
  exact Functor.rightDerivedPullback_app_comp_map_mapDerivedCategoryToId_app _ τ d hτ M

/-- The bounded below version of
`AlgebraicGeometry.Etale.exists_rightDerivedPullback_app_comp_eq_smul`. -/
theorem exists_rightDerivedPullback_app_obj_comp_eq_smul
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Nat.card (π.GeometricFiber s) = d)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ t : (Sheaf.Γ Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj
        ((Functor.mapDerivedCategoryPlus (π)^*[ModuleCat.{u + 1} Λ]).obj M).obj ⟶
          (Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.obj M.obj,
      (Functor.rightDerivedPullback (π)^*[ModuleCat.{u + 1} Λ]
        (ΓPullback (ModuleCat.{u + 1} Λ) π)).app M.obj ≫ t = (d : ℤ) • 𝟙 _ :=
  exists_rightDerivedPullback_app_comp_eq_smul π d hdeg M.obj

/-- The finite étale trace on the middle term of the morphism of localization triangles
`AlgebraicGeometry.Etale.sectionsWithSupportTrianglePullback`: the pullback
`RΓ(Y, M) ⟶ RΓ(Y', π^* M)` composed with the trace is multiplication by the degree `d`. -/
theorem exists_sectionsWithSupportTrianglePullback_app_hom₂_comp_eq_smul
    {Z Z' : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (i' : Z' ⟶ Y')
    [IsClosedImmersion i'] (h : i'.openComplement ≤ π ⁻¹ᵁ i.openComplement)
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Nat.card (π.GeometricFiber s) = d)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ∃ t, ((sectionsWithSupportTrianglePullback (ModuleCat.{u + 1} Λ) π i i' h).app M).hom₂ ≫
      t = (d : ℤ) • 𝟙 _ :=
  exists_rightDerivedPullback_app_obj_comp_eq_smul π d hdeg M

end DerivedTrace

section Pair

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X X' Z Z' : Scheme.{u}} (e : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
  (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : i'.openComplement ≤ e ⁻¹ᵁ i.openComplement)

/-- The middle component of the morphism of localization triangles
`AlgebraicGeometry.Etale.sectionsWithSupportTrianglePullback` is the pullback
`RΓ(X, K) ⟶ RΓ(X', e^* K)` of derived global sections. -/
lemma sectionsWithSupportTrianglePullback_app_hom₂
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    ((sectionsWithSupportTrianglePullback A e i i' h).app K).hom₂ =
      (Functor.rightDerivedPullback (e)^*[A] (ΓPullback A e)).app K.obj :=
  rfl

end Pair

end AlgebraicGeometry.Etale
