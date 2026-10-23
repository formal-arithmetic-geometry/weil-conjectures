/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeTowerSheaf
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedLatticeFrame
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntAbSheafPowLocal

/-!
# The tower of an integral cocycle is constant over the cover

Let `f : V ⟶ Y` be weakly étale and `γ` a continuous integral cocycle on `V ×_Y V`
(`AlgebraicGeometry.IsIntegralCocycle`). Over an object `U ⟶ V` of the small pro-étale site of
`V`, which factors through `f`, the twisted sections of the reductions of `γ` are the locally
constant functions `U → (ℤ_ℓ ⧸ ℓᵏ)ᴺ` (`AlgebraicGeometry.frameEval`,
`AlgebraicGeometry.frameExt`). Hence the restriction to `V` of the pro-étale tower of `γ` is the
constant tower `(ℤ/ℓᵏ)_V^N` (`AlgebraicGeometry.frameTowerIso`), compatibly with the reductions.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Matrix

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry

open Scheme ProEtale

variable {l : ℕ} [Fact l.Prime] {Y V : Scheme.{u}} (f : V ⟶ Y) [hf : WeaklyEtale f] {N : ℕ}
  (γ : ↥(pullback f f) → GL (Fin N) ℤ_[l])

/-- The restriction to `V` of the pro-étale tower of an integral cocycle, as abelian sheaves. -/
noncomputable abbrev frameTower : ℕᵒᵖ ⥤ Sheaf (ProEt.topology V) Ab.{u + 1} :=
  proEtIntegralCocycleTower γ ⋙
    sheafCompose (ProEt.topology Y) (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) Ab) ⋙
      ProEtale.localizationRestriction Ab.{u + 1} f hf

variable (l) in
/-- The additive identification `ℤ_ℓ ⧸ ℓᵏ ≃ ℤ/ℓᵏ`. -/
noncomputable abbrev towerEquiv (k : ℕ) :
    ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k ≃+ ZMod (l ^ k) :=
  ULift.padicIntQuotientSpanPowAddEquiv.{u + 1} l k

variable (l) in
/-- The identification `ℤ_ℓ ⧸ ℓᵏ ≃ ℤ/ℓᵏ` is compatible with the reductions. -/
lemma towerEquiv_towerFactor {k k' : ℕ} (h : k' ≤ k)
    (x : ULift.{u + 1} ℤ_[l] ⧸ towerIdeal.{u} l k) :
    towerEquiv l k' (towerFactor.{u} l h x) =
      ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ k')) (towerEquiv l k x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have e₁ : towerFactor.{u} l h (Ideal.Quotient.mk _ a) = towerReduce l k' a.down := rfl
  have e₂ : (Ideal.Quotient.mk (towerIdeal.{u} l k) a) = towerReduce l k a.down := rfl
  rw [e₁, e₂, padicIntQuotientSpanPowAddEquiv_towerReduce,
    padicIntQuotientSpanPowAddEquiv_towerReduce, ZMod.castHom_apply, PadicInt.cast_toZModPow]

section Maps

variable {f γ}

/-- The `i`-th coordinate, modulo `ℓᵏ`, of a twisted section over `U ⟶ V`, restricted along the
section of `V ×_Y U ⟶ U`. -/
noncomputable def frameCoord (k : ℕ) (i : Fin N) (U : V.ProEt)
    (σ : twistedSubmodule f (levelCocycleInt γ k) (U.hom ≫ f)) : ↥U.left → ZMod (l ^ k) :=
  fun u ↦ towerEquiv l k (frameEval f U.hom rfl σ.1 u i)

lemma isLocallyConstant_frameCoord (k : ℕ) (i : Fin N) (U : V.ProEt)
    (σ : twistedSubmodule f (levelCocycleInt γ k) (U.hom ≫ f)) :
    IsLocallyConstant (frameCoord k i U σ) :=
  (((mem_twistedSubmodule f _).1 σ.2).1.comp_continuous
    (frameSection f U.hom rfl).base.hom.continuous).comp fun v ↦ towerEquiv l k (v i)

/-- The `i`-th coordinate of the restriction to `V` of the pro-étale tower, modulo `ℓᵏ`. -/
noncomputable def frameEvalHom (k : ℕ) (i : Fin N) :
    (frameTower f γ).obj (op k) ⟶ (zmodPowAbSheafDiagram V l).obj (op k) :=
  (fullyFaithfulSheafToPresheaf _ _).preimage
    { app U := AddCommGrpCat.ofHom
        { toFun σ := ULift.up ⟨frameCoord k i U.unop σ,
            (isLocallyConstant_frameCoord k i U.unop σ).continuous⟩
          map_zero' := ULift.ext _ _ (ContinuousMap.ext fun _ ↦ map_zero (towerEquiv l k))
          map_add' σ τ := ULift.ext _ _ (ContinuousMap.ext fun _ ↦ map_add (towerEquiv l k) _ _) }
      naturality U U' g := by
        ext σ
        refine ULift.ext _ _ (ContinuousMap.ext fun u ↦ ?_)
        have := congrFun (frameEval_comp_eq (f := f) U.unop.hom rfl g.unop.left
          (by rw [Category.assoc]) (a' := U'.unop.hom) rfl (MorphismProperty.Over.w g.unop)
          σ.1) u
        exact congrArg (fun v ↦ towerEquiv l k (v i)) this }

lemma frameEvalHom_hom_app_apply (k : ℕ) (i : Fin N) (U : V.ProEtᵒᵖ)
    (σ : twistedSubmodule f (levelCocycleInt γ k) (U.unop.hom ≫ f)) :
    ((frameEvalHom k i).hom.app U σ).down = ⟨frameCoord k i U.unop σ,
      (isLocallyConstant_frameCoord k i U.unop σ).continuous⟩ :=
  rfl

variable (hγ : IsIntegralCocycle f γ)

/-- The twisted section `(v, u) ↦ γ(v, u) eᵢ x(u)` extending `x eᵢ`, for a function `x` on
`U ⟶ V` with values in `ℤ/ℓᵏ`. -/
noncomputable def frameExtSection (k : ℕ) (i : Fin N) (U : V.ProEt) (x : C(U.left, ZMod (l ^ k))) :
    twistedSubmodule f (levelCocycleInt γ k) (U.hom ≫ f) :=
  ⟨frameExt f U.hom rfl (fun z ↦ levelCocycleInt γ k z)
      (fun u ↦ Pi.single i ((towerEquiv l k).symm (x u))),
    (mem_twistedSubmodule f _).2 (isTwistedSection_frameExt U.hom rfl
      (hγ.isDescentCocycle_int k) (((IsLocallyConstant.iff_continuous x).2 x.continuous).comp
        fun a ↦ Pi.single i ((towerEquiv l k).symm a)))⟩

include hγ in
/-- The extension of the `i`-th coordinate functions modulo `ℓᵏ` to twisted sections. -/
noncomputable def frameExtHom (k : ℕ) (i : Fin N) :
    (zmodPowAbSheafDiagram V l).obj (op k) ⟶ (frameTower f γ).obj (op k) :=
  (fullyFaithfulSheafToPresheaf _ _).preimage
    { app U := AddCommGrpCat.ofHom
        { toFun x := frameExtSection hγ k i U.unop x.down
          map_zero' := Subtype.ext (by
            change frameExt f _ _ _ _ = 0
            convert frameExt_zero (f := f) U.unop.hom rfl (levelCocycleInt γ k) using 2
            funext u
            simp)
          map_add' x y := Subtype.ext (by
            change frameExt f _ _ _ _ = frameExt f _ _ _ _ + frameExt f _ _ _ _
            rw [← frameExt_add]
            congr 1
            funext u
            simp [Pi.single_add]) }
      naturality U U' g := by
        ext x
        refine Subtype.ext ?_
        exact frameExt_comp_eq (f := f) U.unop.hom rfl g.unop.left (by rw [Category.assoc])
          (a' := U'.unop.hom) rfl (MorphismProperty.Over.w g.unop) _ }

lemma frameExtHom_hom_app_apply (k : ℕ) (i : Fin N) (U : V.ProEtᵒᵖ)
    (x : ULift.{u + 1} C(U.unop.left, ZMod (l ^ k))) :
    (frameExtHom hγ k i).hom.app U x = frameExtSection hγ k i U.unop x.down :=
  rfl


lemma frameEvalHom_frameExtHom (k : ℕ) (i j : Fin N) :
    frameExtHom hγ k i ≫ frameEvalHom k j =
      if i = j then 𝟙 _ else 0 := by
  ext U x
  refine ULift.ext _ _ (ContinuousMap.ext fun u ↦ ?_)
  have h := congrFun (frameEval_frameExt (f := f) U.unop.hom rfl (hγ.isDescentCocycle_int k)
    (fun u ↦ Pi.single i ((towerEquiv l k).symm (x.down u)))) u
  change towerEquiv l k (frameEval f U.unop.hom rfl (frameExt f U.unop.hom rfl _ _) u j) = _
  rw [h]
  split_ifs with hij
  · subst hij
    simp only [Pi.single_eq_same, AddEquiv.apply_symm_apply]
    rfl
  · rw [Pi.single_eq_of_ne (Ne.symm hij), map_zero]
    rfl

lemma sum_frameEvalHom_frameExtHom (k : ℕ) :
    ∑ i, frameEvalHom k i ≫ frameExtHom hγ k i = 𝟙 ((frameTower f γ).obj (op k)) := by
  ext U σ
  have hσ := (mem_twistedSubmodule f _).1 σ.2
  refine Subtype.ext ?_
  change (∑ i, frameExtSection hγ k i U.unop
    (frameEvalHom k i |>.hom.app U σ).down).1 = σ.1
  rw [Submodule.coe_sum]
  change ∑ i, frameExt f U.unop.hom rfl (fun z ↦ levelCocycleInt γ k z)
    (fun u ↦ Pi.single i ((towerEquiv l k).symm (frameCoord k i U.unop σ u))) = σ.1
  have hsum (s : Finset (Fin N)) : ∑ i ∈ s, frameExt f U.unop.hom rfl
      (fun z ↦ levelCocycleInt γ k z)
        (fun u ↦ Pi.single i ((towerEquiv l k).symm (frameCoord k i U.unop σ u))) =
      frameExt f U.unop.hom rfl (fun z ↦ levelCocycleInt γ k z)
        (∑ i ∈ s, fun u ↦ Pi.single i ((towerEquiv l k).symm (frameCoord k i U.unop σ u))) := by
    induction s using Finset.induction_on with
    | empty => simp [frameExt_zero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, frameExt_add]
  rw [hsum]
  have : (∑ i, fun u ↦ Pi.single i ((towerEquiv l k).symm (frameCoord k i U.unop σ u))) =
      frameEval f U.unop.hom rfl σ.1 := by
    funext u j
    simp only [Finset.sum_apply, frameCoord, AddEquiv.symm_apply_apply, Pi.single_apply,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [this, frameExt_frameEval _ _ hσ]

/-- The restriction to `V` of the pro-étale tower, at level `k`, as a direct sum of copies of
the constant sheaf `(ℤ/ℓᵏ)_V`. -/
noncomputable def frameBicone (k : ℕ) :
    Bicone fun _ : Fin N ↦ (zmodPowAbSheafDiagram V l).obj (op k) where
  pt := (frameTower f γ).obj (op k)
  π i := frameEvalHom k i
  ι i := frameExtHom hγ k i
  ι_π i j := by
    rw [frameEvalHom_frameExtHom]
    split_ifs <;> rfl

/-- **The restriction to `V` of the pro-étale tower is constant**, at each level. -/
noncomputable def frameTowerObjIso (k : ℕ) :
    (frameTower f γ).obj (op k) ≅ (zmodPowAbSheafDiagramPow V l N).obj (op k) :=
  biproduct.uniqueUpToIso _ ((frameBicone hγ k).isBilimitOfTotal (sum_frameEvalHom_frameExtHom hγ k))

lemma frameEvalHom_naturality {k k' : ℕ} (h : k' ≤ k) (i : Fin N) :
    (frameTower f γ).map (homOfLE h).op ≫ frameEvalHom k' i =
      frameEvalHom k i ≫ (zmodPowAbSheafDiagram V l).map (homOfLE h).op := by
  ext U σ
  refine ULift.ext _ _ (ContinuousMap.ext fun u ↦ ?_)
  exact towerEquiv_towerFactor l h _

/-- **The restriction to `V` of the pro-étale tower is the constant tower `(ℤ/ℓᵏ)_V^N`.** -/
noncomputable def frameTowerIso : frameTower f γ ≅ zmodPowAbSheafDiagramPow V l N :=
  NatIso.ofComponents (fun k ↦ frameTowerObjIso hγ k.unop) fun {k k'} h ↦ by
    refine biproduct.hom_ext _ _ fun j ↦ ?_
    simp only [frameTowerObjIso, biproduct.uniqueUpToIso_hom, Category.assoc,
      Functor.biproductPow_map, biproduct.lift_π, biproduct.map_π, biproduct.lift_π_assoc]
    exact frameEvalHom_naturality (leOfHom h.unop) j

/-- **The limit of the restriction to `V` of the pro-étale tower is `ℤ_ℓ,V^N`.** -/
noncomputable def frameLimitIso :
    limit (frameTower f γ) ≅ ⨁ fun _ : Fin N ↦ padicIntAbSheaf V l :=
  lim.mapIso (frameTowerIso hγ) ≪≫ limitZmodPowAbSheafDiagramPowIso V l N

end Maps

end AlgebraicGeometry
