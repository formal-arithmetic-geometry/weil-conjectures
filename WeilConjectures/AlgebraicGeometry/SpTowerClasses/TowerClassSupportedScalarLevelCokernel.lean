/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassSupportedScalarLevelIso
/-! # The level-`n` integral quotient as a cokernel

A basis of the finite coefficient ring presents the underlying sheaf of the constant ring
sheaf as the cokernel of multiplication by `l ^ (n + 1)` on copies of the constant integers.
-/


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Cokernels transport along isomorphisms of source and target. -/
theorem cokernel_of_isos {C : Type*} [Category C] [Preadditive C] {X X' Y Y' : C}
    (f : X ⟶ X) (f' : X' ⟶ X') (α : X' ≅ X) (hf : f' ≫ α.hom = α.hom ≫ f)
    (π : X ⟶ Y) (hπ : f ≫ π = 0) (h : IsColimit (CokernelCofork.ofπ π hπ)) (ι : Y ≅ Y') :
    ∃ hz : f' ≫ α.hom ≫ π ≫ ι.hom = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ hz)) := by
  have hz : f' ≫ α.hom ≫ π ≫ ι.hom = 0 := by
    rw [← Category.assoc, hf, Category.assoc, ← Category.assoc f, hπ]
    simp
  have hd {W : C} (e : X' ⟶ W) (he : f' ≫ e = 0) : f ≫ α.inv ≫ e = 0 := by
    have : f ≫ α.inv = α.inv ≫ f' := by
      rw [Iso.eq_inv_comp, ← Category.assoc, ← hf, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    rw [← Category.assoc, this, Category.assoc, he, comp_zero]
  refine ⟨hz, ⟨CokernelCofork.IsColimit.ofπ _ _
    (fun e he ↦ ι.inv ≫ h.desc (CokernelCofork.ofπ (α.inv ≫ e) (hd e he))) ?_ ?_⟩⟩
  · intro W e he
    have := h.fac (CokernelCofork.ofπ (α.inv ≫ e) (hd e he)) WalkingParallelPair.one
    simp only [Cofork.ofπ_pt, CokernelCofork.ofπ, Cofork.ofπ_ι_app] at this
    simp [this]
  · intro W e he m hm
    rw [Iso.eq_inv_comp]
    apply Cofork.IsColimit.hom_ext h
    have := h.fac (CokernelCofork.ofπ (α.inv ≫ e) (hd e he)) WalkingParallelPair.one
    simp only [Cofork.ofπ_pt, CokernelCofork.ofπ, Cofork.ofπ_ι_app] at this
    rw [Cofork.π_ofπ, this, ← hm]
    simp

theorem ι_biproductIsoPi_hom_apply {d : ℕ} (f : Fin d → AddCommGrpCat.{u + 1}) (i : Fin d)
    (x : f i) : (biproduct.ι f i ≫ (AddCommGrpCat.biproductIsoPi f).hom) x = Pi.single i x := by
  funext j
  have h := ConcreteCategory.congr_hom
    (AddCommGrpCat.biproductIsoPi_inv_comp_π f j) ((biproduct.ι f i ≫
      (AddCommGrpCat.biproductIsoPi f).hom) x)
  simp only [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply] at h
  rw [ConcreteCategory.comp_apply]
  refine (h.symm.trans ?_)
  rw [← ConcreteCategory.comp_apply, biproduct.ι_π]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Restriction in the level-`n` coefficient module is restriction of constant-ring
sections. -/
theorem coefficientEvaluation_map (T : Scheme.{u}) (n : ℕ) {U V : T.ProEtᵒᵖ} (f : U ⟶ V)
    (x : (sheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))))).obj U) :
    ((finiteForget l E T n).obj
        ((SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T)))).obj.map f x =
      (sheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))))).map f x := by
  change (WeilConjectures.SemilinearSections.ringPresheaf (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)).map
        ((Prod.sectR n T.ProEt).map f.unop).op _ = _
  simp only [WeilConjectures.SemilinearSections.ringPresheaf, Functor.comp_obj,
    prodOpEquiv_functor_obj, Functor.uncurry_obj_obj, ObjectProperty.ι_obj, Prod.sectR_map,
    Functor.comp_map, prodOpEquiv_functor_map, Quiver.Hom.unop_op, Quiver.Hom.op_unop,
    Functor.uncurry_obj_map, ObjectProperty.ι_map, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]
  erw [op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Constant sections of the finite coefficient ring, as an additive presheaf map into the
underlying sheaf of the constant ring sheaf. -/
def constantUnderlyingPresheaf (T : Scheme.{u}) (n : ℕ) :
    (Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))) ⟶
      ((finiteForget l E T n).obj
        ((SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T)))).obj where
  app U := AddCommGrpCat.ofHom ((toSheafify (Scheme.ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))))).app U).hom.toAddMonoidHom
  naturality U V f := by
    ext a
    have h := ConcreteCategory.congr_hom ((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))))).naturality f) a
    exact h.trans (coefficientEvaluation_map l E T n f _).symm

/-- The constant abelian sheaf of the finite coefficient ring maps to the underlying
sheaf of the constant ring sheaf, by constant sections. -/
def constantUnderlying (T : Scheme.{u}) (n : ℕ) :
    (constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))) ⟶
      (finiteForget l E T n).obj
        ((SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T))) :=
  ⟨sheafifyLift (Scheme.ProEt.topology T) (constantUnderlyingPresheaf l E T n)
    ((finiteForget l E T n).obj
      ((SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T)))).property⟩

theorem constantUnderlying_isIso (T : Scheme.{u}) (n : ℕ) :
    IsIso (constantUnderlying l E T n) := by
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff,
    ← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
  let P := (Functor.const T.ProEtᵒᵖ).obj
    (AddCommGrpCat.of (ULift.{u + 1} (SpTowerShriek.R l E n)))
  have h : toSheafify (Scheme.ProEt.topology T) P ≫
      ((sheafToPresheaf _ _).map (constantUnderlying l E T n)) =
        constantUnderlyingPresheaf l E T n :=
    toSheafify_sheafifyLift _ _ _
  rw [← Presheaf.comp_isLocallyInjective_iff (Scheme.ProEt.topology T)
      (toSheafify (Scheme.ProEt.topology T) P),
    ← Presheaf.comp_isLocallySurjective_iff (Scheme.ProEt.topology T)
      (toSheafify (Scheme.ProEt.topology T) P), h]
  constructor
  · exact ⟨fun x y hxy ↦ Presheaf.equalizerSieve_mem (Scheme.ProEt.topology T)
      (toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))))) x y hxy⟩
  · refine ⟨fun {U} x ↦ (Scheme.ProEt.topology T).superset_covering ?_
      (Presheaf.imageSieve_mem (Scheme.ProEt.topology T)
        (toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))))) (U := op U) x)⟩
    rintro V g ⟨t, ht⟩
    exact ⟨t, ht.trans (coefficientEvaluation_map l E T n g.op x).symm⟩

/-- Multiplication of an integer by a basis vector. -/
def basisGenerator (n : ℕ) (b : SpTowerShriek.R l E n) :
    AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ AddCommGrpCat.of (ULift.{u + 1} (SpTowerShriek.R l E n)) :=
  AddCommGrpCat.ofHom
    { toFun := fun k ↦ ULift.up (k.down • b)
      map_zero' := by simp; rfl
      map_add' := fun x y ↦ by
        apply ULift.ext
        simp [add_smul] }

theorem basisGenerator_desc_cokernel (n d : ℕ)
    (e : letI := coefficientZModAlgebra l E n
      Module.Basis (Fin d) (ZMod (l ^ (n + 1))) (SpTowerShriek.R l E n)) :
    ∃ hz : (l ^ (n + 1) • 𝟙 (⨁ fun _ : Fin d ↦ AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
        biproduct.desc (fun i ↦ basisGenerator l E n (e i)) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ hz)) := by
  obtain ⟨hz, ⟨h⟩⟩ := basisCombination_cokernel l E n d e
  have hψ : biproduct.desc (fun i ↦ basisGenerator l E n (e i)) =
      (AddCommGrpCat.biproductIsoPi fun _ : Fin d ↦ AddCommGrpCat.of (ULift.{u + 1} ℤ)).hom ≫
        AddCommGrpCat.ofHom (basisCombination l E n d e) := by
    apply biproduct.hom_ext'
    intro i
    rw [biproduct.ι_desc, ← Category.assoc]
    ext k
    rw [ConcreteCategory.comp_apply, ι_biproductIsoPi_hom_apply]
    change k.down • e i = ∑ j, ((Pi.single i k : Fin d → ULift.{u + 1} ℤ) j).down • e j
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  have key : ∀ (π : (⨁ fun _ : Fin d ↦ AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      AddCommGrpCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))),
      π = (AddCommGrpCat.biproductIsoPi fun _ : Fin d ↦ AddCommGrpCat.of (ULift.{u + 1} ℤ)).hom ≫
        AddCommGrpCat.ofHom (basisCombination l E n d e) ≫ (Iso.refl _).hom →
      ∃ hz : (l ^ (n + 1) • 𝟙 _) ≫ π = 0, Nonempty (IsColimit (CokernelCofork.ofπ π hz)) := by
    rintro _ rfl
    refine cokernel_of_isos _ _ _ ?_ _ hz h _
    simp
  exact key _ (by rw [hψ, Iso.refl_hom, Category.comp_id])

theorem sheaf_eqToHom_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (h : R = S) (U : Cᵒᵖ) (x : R.obj.obj U) :
    (eqToHom h).hom.app U x = cast (by subst h; rfl) x := by
  subst h
  rfl

theorem coefficientEvaluation_smul (T : Scheme.{u}) (n : ℕ) (U : T.ProEtᵒᵖ)
    (c x : (SpTowerShriek.B l E T n).obj.obj U) :
    DistribSMul.toAddMonoidHom
        (((SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T))).val.obj U)
        (show (WeilConjectures.SemilinearSections.ring (Scheme.ProEt.topology T)
          (SpTowerShriek.B l E T n)).obj.obj U from c) x = c * x := by
  change (show (SpTowerShriek.B l E T n).obj.obj U from
    (eqToHom (WeilConjectures.SemilinearSections.evaluation_ring
    (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) n).symm).hom.app
      U c) * x = c * x
  rw [sheaf_eqToHom_apply, cast_eq]

/-- The constant abelian sheaf functor carries a basis generator to the finite quotient
followed by multiplication by the constant basis section. -/
theorem constantSheaf_basisGenerator (T : Scheme.{u}) (n : ℕ) (b : SpTowerShriek.R l E n) :
    (constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}).map
        (basisGenerator l E n b) ≫ constantUnderlying l E T n =
      finiteQuotient l E T n ≫ levelSmul l E T n b (coefficient T (Arings l E T)) := by
  let J := Scheme.ProEt.topology T
  let P := (Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have hL : toSheafify J P ≫ ((constantSheaf J AddCommGrpCat.{u + 1}).map
      (basisGenerator l E n b) ≫ constantUnderlying l E T n).hom =
      (Functor.const T.ProEtᵒᵖ).map (basisGenerator l E n b) ≫
        constantUnderlyingPresheaf l E T n := by
    change toSheafify J P ≫ sheafifyMap J ((Functor.const T.ProEtᵒᵖ).map
      (basisGenerator l E n b)) ≫ sheafifyLift J (constantUnderlyingPresheaf l E T n) _ = _
    rw [sheafifyMap_sheafifyLift, toSheafify_sheafifyLift]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ ((finiteForget l E T n).obj
    ((SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T)))).property
  rw [hL]
  ext U k
  have hq := eq_of_heq ((finiteQuotient_existsUnique l E T n).exists.choose_spec U k)
  dsimp [levelSmul, sectionSmul, constantUnderlyingPresheaf, basisGenerator]
  erw [coefficientEvaluation_smul, hq]
  have hk : (ULift.up (k.down • b) : ULift.{u + 1} (SpTowerShriek.R l E n)) =
      k.down • ULift.up b := rfl
  rw [hk, map_zsmul]
  let c : (SpTowerShriek.B l E T n).obj.obj U := constSection l E T n b U
  exact (zsmul_eq_mul c k.down).trans (mul_comm _ _)

theorem levelQuotient_cokernel (T : Scheme.{u}) (n d : ℕ)
    (e : letI := coefficientZModAlgebra l E n
      Module.Basis (Fin d) (ZMod (l ^ (n + 1))) (SpTowerShriek.R l E n)) :
    ∃ hz : (l ^ (n + 1) • 𝟙 (⨁ fun _ : Fin d ↦ (abEvaluation T n).obj (integers T))) ≫
        biproduct.desc (fun i : Fin d ↦ finiteQuotient l E T n ≫
          levelSmul l E T n (e i) (coefficient T (Arings l E T))) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ _ hz)) := by
  let K := constantSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}
  let hT : IsTerminal (Scheme.ProEt.mk (𝟙 T)) := MorphismProperty.Over.mkIdTerminal _ T
  have : PreservesColimitsOfSize.{0, 0} K := (constantSheafAdj (Scheme.ProEt.topology T)
    AddCommGrpCat.{u + 1} hT).leftAdjoint_preservesColimits
  have : K.Additive := inferInstance
  have := constantUnderlying_isIso l E T n
  obtain ⟨hz, ⟨h⟩⟩ := basisGenerator_desc_cokernel l E n d e
  have hK := isColimitCoforkMapOfIsColimit' K hz h
  have key : ∀ (π : (⨁ fun _ : Fin d ↦ (abEvaluation T n).obj (integers T)) ⟶
      (finiteForget l E T n).obj ((SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T)))),
      π = (K.mapBiproduct fun _ : Fin d ↦ AddCommGrpCat.of (ULift.{u + 1} ℤ)).symm.hom ≫
        K.map (biproduct.desc (fun i ↦ basisGenerator l E n (e i))) ≫
          (asIso (constantUnderlying l E T n)).hom →
      ∃ hz : (l ^ (n + 1) • 𝟙 _) ≫ π = 0, Nonempty (IsColimit (CokernelCofork.ofπ π hz)) := by
    rintro _ rfl
    refine cokernel_of_isos _ _ _ ?_ _ _ hK _
    simp
  refine key _ ?_
  rw [Iso.symm_hom, asIso_hom, ← Category.assoc, biproduct.mapBiproduct_inv_map_desc]
  apply biproduct.hom_ext'
  intro i
  rw [biproduct.ι_desc, biproduct.ι_desc_assoc, constantSheaf_basisGenerator]

end AlgebraicGeometry.ProEtale.SpTowerClasses
