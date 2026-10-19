/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeStalkTransition
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.AlgebraicGeometry.OpenInjectiveCoefficientLowerComparison

/-! # Open injective Leray edge comparison

Source: Stacks Project, Tags 0F07 and 0734.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

private theorem mono_rightDerived_map_of_lower_isIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] {K L : DerivedCategory.Plus C} (α : K ⟶ L)
    (q : ℤ) (hq : 1 ≤ q) [K.IsLE 0]
    (hα : ∀ n < q, IsIso ((DerivedCategory.Plus.homologyFunctor C n).map α)) :
    Mono ((DerivedCategory.Plus.homologyFunctor D q).map (R+(F).map α)) := by
  obtain ⟨M, b, c, hT⟩ := distinguished_cocone_triangle α
  let T := Triangle.mk α b c
  have hM : M.IsGE q := by
    apply (M.isGE_ι_obj_iff q).mp
    apply (DerivedCategory.isGE_iff _ q).mpr
    intro n hn
    have := hα n hn
    have hn1α : Mono ((DerivedCategory.Plus.homologyFunctor C (n + 1)).map α) := by
      by_cases h : n + 1 < q
      · have := hα (n + 1) h
        infer_instance
      · have hz := DerivedCategory.Plus.isZero_homology_of_isLE K 0 (n + 1) (by lia)
        exact hz.mono _
    exact ((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_exact₃
      T hT n (n + 1) rfl).isZero_X₂
      (((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff
        T hT n).mp (by
          change Epi ((DerivedCategory.Plus.homologyFunctor C n).map α)
          infer_instance))
      (((DerivedCategory.Plus.homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff
        T hT n (n + 1) rfl).mp hn1α)
  have hRT := R+(F).map_distinguished T hT
  have hz := F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
    M q (q := q - 1) (by lia)
  exact ((DerivedCategory.Plus.homologyFunctor D 0).homologySequence_mono_shift_map_mor₁_iff
    (R+(F).mapTriangle.obj T) hRT (q - 1) q (by lia)).mpr (hz.eq_of_src _ _)

universe u
namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

private theorem lower_transition_factor
    {X Y W : Scheme.{u}} (h : Y ⟶ X) (a : W ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    let : (((a)_*[ModuleCat.{u + 1} Λ])).PreservesInjectiveObjects :=
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a)
    lowerStarPlusTransition Λ a h (a ≫ h) rfl K =
      R+((h)_*[ModuleCat.{u + 1} Λ]).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).derivedPlus.unit.app K) ≫
      (Functor.rightDerivedFunctorPlusCompIso' ((a)_*[ModuleCat.{u + 1} Λ])
        ((h)_*[ModuleCat.{u + 1} Λ])
        (lowerStarComp (ModuleCat.{u + 1} Λ) a h)).hom.app
          (D+((a)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  let : (((a)_*[ModuleCat.{u + 1} Λ])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a)
  let adj := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).derivedPlus
  let adjA := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).derivedPlus
  let C := Functor.rightDerivedFunctorPlusCompIso' ((a)_*[ModuleCat.{u + 1} Λ])
    ((h)_*[ModuleCat.{u + 1} Λ]) (lowerStarComp (ModuleCat.{u + 1} Λ) a h)
  have hn := C.hom.naturality
    (D+((a)^*[ModuleCat.{u + 1} Λ]).map (adj.counit.app K))
  have hu := adjA.unit.naturality (adj.counit.app K)
  simp only [Functor.comp_map, Functor.id_map] at hn hu
  unfold lowerStarPlusTransition
  rw [derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus,
    derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus,
    eqToIso_refl, Iso.refl_trans, Functor.map_comp, ← Category.assoc]
  rw [show upperStarPlusComp (ModuleCat.{u + 1} Λ) a h =
      upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a h from rfl]
  rw [derivedPlus_unit_comp_upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a h]
  change (adj.unit.app (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
    R+((h)_*[ModuleCat.{u + 1} Λ]).map
      (adjA.unit.app (D+((h)^*[ModuleCat.{u + 1} Λ]).obj
        (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K))) ≫
        C.hom.app (D+((a)^*[ModuleCat.{u + 1} Λ]).obj
          (D+((h)^*[ModuleCat.{u + 1} Λ]).obj
            (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)))) ≫
      R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).map
        (D+((a)^*[ModuleCat.{u + 1} Λ]).map (adj.counit.app K)) =
      R+((h)_*[ModuleCat.{u + 1} Λ]).map (adjA.unit.app K) ≫ C.hom.app _
  simp only [Category.assoc]
  erw [← hn]
  rw [← Functor.map_comp_assoc]
  erw [← hu]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc, adj.right_triangle_components]
  exact Category.id_comp _

/-- The open coefficient counit induces a monic degree-q Leray edge map.
Source: Stacks Project, Tags 0F07 and 0734.
(blueprint: lem-sbc-open-injective-leray-edge).

Proof: Let K = e^*((j_*J)[0]) and let α be the derived unit for a followed by
the pullback comparison and the single of the coefficient counit. The lower-degree
comparison identifies H^n(α) with base change for n < q, so these maps are isomorphisms.
K is concentrated in degree zero. The long exact sequence of its cone triangle gives
H^n(cone α) = 0 for n < q: use the isomorphism in degree n, and either the isomorphism
in degree n+1 or the vanishing of H^(n+1)(K) when n+1 ≥ q. Derived h_* preserves this
lower bound. Its long exact sequence therefore makes H^q(Rh_*(α)) monic.
The composition law for the derived adjunction units identifies the displayed transition
and coefficient counit with this map followed by the derived pushforward composition
isomorphism. Taking homology preserves that isomorphism and hence monicity.
-/
theorem baseChangeTargetTransition_counit_mono
    {X Y T V W : Scheme.{u}} (h : Y ⟶ X) (e : Y ⟶ T) (j : V ⟶ T)
    (eV : W ⟶ V) (a : W ⟶ Y) (h' : W ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (wa : a ≫ e = eV ≫ j) (wh : a ≫ h = h')
    (sq : IsPullback eV a j e) (q : ℤ) (hq : 1 ≤ q)
    (hprev : ∀ n < q, BaseChangeProperty Λ e n)
    (J : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] :
    Mono (baseChangeTargetTransition Λ e h q j a eV h' wa wh
      (((j)_*[ModuleCat.{u + 1} Λ]).obj J) ≫
      (baseChangeTargetFunctor Λ eV h' q).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app J)) := by
  subst h'
  let : (((a)_*[ModuleCat.{u + 1} Λ])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a)
  let G := ((j)_*[ModuleCat.{u + 1} Λ]).obj J
  let K := D+((e)^*[ModuleCat.{u + 1} Λ]).obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
  let σ := (upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G) ≫
    eqToHom (by rw [wa]) ≫
    (upperStarPlusComp (ModuleCat.{u + 1} Λ) eV j).hom.app _ ≫
    D+((eV)^*[ModuleCat.{u + 1} Λ]).map
      ((((j)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app G ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app J))
  let α : K ⟶ R+((a)_*[ModuleCat.{u + 1} Λ]).obj
      (D+((eV)^*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj J)) :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).derivedPlus.unit.app K ≫
    R+((a)_*[ModuleCat.{u + 1} Λ]).map σ
  have hK : K.IsLE 0 := by
    exact Functor.IsTExact.isLE_obj DerivedCategory.Plus.TStructure.t
      DerivedCategory.Plus.TStructure.t D+((e)^*[ModuleCat.{u + 1} Λ]) _ 0
  let : K.IsLE 0 := hK
  have hm := mono_rightDerived_map_of_lower_isIso ((h)_*[ModuleCat.{u + 1} Λ])
    α q hq (fun n hn ↦ open_injective_coefficient_lower_comparison Λ e j eV a
      wa sq n (hprev n hn) J)
  let : Mono ((DerivedCategory.Plus.homologyFunctor _ q).map
    (R+((h)_*[ModuleCat.{u + 1} Λ]).map α)) := hm
  let C := Functor.rightDerivedFunctorPlusCompIso' ((a)_*[ModuleCat.{u + 1} Λ])
    ((h)_*[ModuleCat.{u + 1} Λ]) (lowerStarComp (ModuleCat.{u + 1} Λ) a h)
  have hE : baseChangeTargetTransition Λ e h q j a eV (a ≫ h) wa rfl G ≫
      (baseChangeTargetFunctor Λ eV (a ≫ h) q).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app J) =
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h)_*[ModuleCat.{u + 1} Λ]).map α ≫ C.hom.app _) := by
    unfold baseChangeTargetTransition baseChangeTargetFunctor
    simp only [Functor.comp_map, ← Functor.map_comp, Category.assoc]
    rw [lower_transition_factor]
    have hn := C.hom.naturality σ
    simp only [Functor.comp_map] at hn
    change (DerivedCategory.Plus.homologyFunctor _ q).map
      ((R+((h)_*[ModuleCat.{u + 1} Λ]).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).derivedPlus.unit.app K) ≫
          C.hom.app _) ≫ R+((a ≫ h)_*[ModuleCat.{u + 1} Λ]).map σ) = _
    congr 1
    simp only [Category.assoc]
    erw [← hn]
    rw [← Functor.map_comp_assoc]
    rfl
  rw [hE, Functor.map_comp]
  infer_instance

end AlgebraicGeometry.Etale
