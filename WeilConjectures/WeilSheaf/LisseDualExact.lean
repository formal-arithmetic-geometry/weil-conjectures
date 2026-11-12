/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor
public import WeilConjectures.WeilSheaf.Bidual
public import WeilConjectures.WeilSheaf.IhomLisse.UpperStarDual
public import WeilConjectures.WeilSheaf.LisseDuality
public import WeilConjectures.WeilSheaf.LisseFiltration
public import WeilConjectures.WeilSheaf.LisseLocus

/-!
# Exactness of duals and tensor products of lisse Weil sheaves

The internal hom `𝓗om(-, N)` of sheaves of `ℚ̄_ℓ,X`-modules turns cokernels into kernels
(`AlgebraicGeometry.ProEtale.exact_ihomMap_app`), by transposition. For lisse sheaves the dual
`𝓗om(-, ℚ̄_ℓ)` also turns monomorphisms into epimorphisms
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.epi_ihomMap_app_of_mono`): the cokernel `C` of
`E^∨ ⟶ B^∨`, for `B ⊆ E`, is lisse with `C^∨ ⊆ B^∨∨ ≅ B` killed by `B ⊆ E ≅ E^∨∨`, so `C ≅ C^∨∨`
vanishes. Hence on lisse Weil sheaves:

* the dual is exact (`AlgebraicGeometry.WeilSheaf.exact_dualMap`,
  `AlgebraicGeometry.WeilSheaf.epi_dualMap`, `AlgebraicGeometry.WeilSheaf.mono_dualMap`);
* the tensor product `F ⊗ G = [F^∨, G]` is exact in the lisse variable `F`
  (`AlgebraicGeometry.WeilSheaf.exact_tensorHom_id`) and in the variable `G`
  (`AlgebraicGeometry.WeilSheaf.tensorLeft`, which preserves finite limits and colimits);
* the tensor product commutes with pullback
  (`AlgebraicGeometry.WeilSheaf.upperStarTensorObjIso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

attribute [local instance] Sheaf.symmetricCategory

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}

/-- The internal hom out of the zero morphism is zero. -/
lemma ihomMap_zero_app {M M' : AdicSheaf l Y} (N : AdicSheaf l Y) :
    (Mod.ihomMap (0 : M ⟶ M')).app N = 0 := by
  rw [← Mod.ihomMapAddHom_apply, map_zero, NatTrans.app_zero]

/-- The internal hom out of a zero sheaf vanishes: a morphism into `𝓗om(Z, N)` is determined by
its transpose, a morphism out of `Z`. -/
lemma isZero_ihom_obj_of_isZero {Z : AdicSheaf l Y} (hZ : IsZero Z) (N : AdicSheaf l Y) :
    IsZero ((AdicSheaf.ihom Z).obj N) := by
  rw [IsZero.iff_id_eq_zero, ← Mod.transpose_eq_zero_iff]
  exact hZ.eq_of_src _ _

/-- **`𝓗om(-, N)` turns cokernels into kernels.** If `A ⟶ B ⟶ C ⟶ 0` is exact, then
`0 ⟶ 𝓗om(C, N) ⟶ 𝓗om(B, N) ⟶ 𝓗om(A, N)` is exact: a morphism `P ⟶ 𝓗om(B, N)` killed by
`A ⟶ B` transposes to a morphism `B ⟶ 𝓗om(P, N)` killed by `A ⟶ B`, which factors through
the cokernel `C`. -/
theorem exact_ihomMap_app {S : ShortComplex (AdicSheaf l Y)} (hS : S.Exact) [hg : Epi S.g]
    (N : AdicSheaf l Y) :
    (ShortComplex.mk ((Mod.ihomMap S.g).app N) ((Mod.ihomMap S.f).app N) (by
      rw [← NatTrans.comp_app, ← Mod.ihomMap_comp, S.zero, ihomMap_zero_app])).Exact := by
  refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι' _ _ fun {P} v hv ↦ ?_)
  have h0 : S.f ≫ Mod.transpose v = 0 := by
    rw [← Mod.transpose_comp_ihomMap, hv, Mod.transpose_zero]
  let t := hS.gIsCokernel.desc (CokernelCofork.ofπ (Mod.transpose v) h0)
  have ht : S.g ≫ t = Mod.transpose v := Cofork.IsColimit.π_desc hS.gIsCokernel
  refine ⟨Mod.transpose t, ?_⟩
  rw [← Mod.transpose_comp, ht, Mod.transpose_transpose]

/-- **The dual of a monomorphism of lisse sheaves is an epimorphism.** For lisse `B` and `E`
and a monomorphism `i : B ⟶ E`, the restriction `𝓗om(E, ℚ̄_ℓ) ⟶ 𝓗om(B, ℚ̄_ℓ)` is an
epimorphism: its cokernel `C` is lisse, and its dual `C^∨` is the kernel of
`B^∨∨ ⟶ E^∨∨`, which is `i` up to the biduality isomorphisms, hence vanishes; so does
`C ≅ C^∨∨`. -/
theorem IsAdicLisseSheaf.epi_ihomMap_app_of_mono [IsLocallyNoetherian Y] {B E : AdicSheaf l Y}
    (hB : IsAdicLisseSheaf B) (hE : IsAdicLisseSheaf E) (i : B ⟶ E) [Mono i] :
    Epi ((Mod.ihomMap i).app (AdicSheaf.unit l Y)) := by
  set d := (Mod.ihomMap i).app (AdicSheaf.unit l Y)
  have hc := isAdicLisseSheaf_adicConstantSheaf (l := l) Y
  have hC : IsAdicLisseSheaf (cokernel d) := ((hE.ihom hc).kernel_cokernel (hB.ihom hc) d).2
  have := hB.isIso_bidual
  have := hE.isIso_bidual
  have := hC.isIso_bidual
  have hS := exact_ihomMap_app (ShortComplex.exact_cokernel d) (AdicSheaf.unit l Y)
  have hmono : Mono ((Mod.ihomMap d).app (AdicSheaf.unit l Y)) := by
    have h := Mod.bidual_naturality i (AdicSheaf.unit l Y)
    rw [← IsIso.inv_comp_eq] at h
    rw [← h]
    infer_instance
  have hzero : IsZero ((AdicSheaf.ihom (cokernel d)).obj (AdicSheaf.unit l Y)) :=
    IsZero.of_mono_eq_zero _ (hS.mono_g_iff.1 hmono)
  refine Preadditive.epi_of_isZero_cokernel d
    ((isZero_ihom_obj_of_isZero hzero (AdicSheaf.unit l Y)).of_iso
      (asIso (Mod.bidual (cokernel d) (AdicSheaf.unit l Y))))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The underlying `ℓ`-adic sheaf functor is faithful. -/
instance : (carrierFunctor k₀ l X).Faithful where
  map_injective h := ObjectProperty.hom_ext _ (Endofunctor.IsoAlgebra.hom_ext h)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The underlying morphism of `ℓ`-adic sheaves of the dual of a morphism of lisse Weil
sheaves. -/
lemma carrierFunctor_map_dualMap {F G : WeilSheaf k₀ l X} (f : F ⟶ G) (hF : F.IsLisse)
    (hG : G.IsLisse) :
    (carrierFunctor k₀ l X).map (dualMap f hF hG) =
      (Mod.ihomMap ((carrierFunctor k₀ l X).map f)).app
        (ProEtale.AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  rfl

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The dual of the zero morphism is zero. -/
lemma dualMap_zero {F G : WeilSheaf k₀ l X} (hF : F.IsLisse) (hG : G.IsLisse) :
    dualMap (0 : F ⟶ G) hF hG = 0 :=
  (carrierFunctor k₀ l X).map_injective (by
    rw [carrierFunctor_map_dualMap, Functor.map_zero, Functor.map_zero,
      ProEtale.ihomMap_zero_app])

/-- **The dual is exact on lisse Weil sheaves.** If `A ⟶ B ⟶ C ⟶ 0` is an exact sequence of
lisse Weil sheaves, then `0 ⟶ C^∨ ⟶ B^∨ ⟶ A^∨` is exact. -/
theorem exact_dualMap {S : ShortComplex (WeilSheaf k₀ l X)} (hS : S.Exact) [Epi S.g]
    (h₁ : S.X₁.IsLisse) (h₂ : S.X₂.IsLisse) (h₃ : S.X₃.IsLisse) :
    (ShortComplex.mk (dualMap S.g h₂ h₃) (dualMap S.f h₁ h₂)
      (by rw [← dualMap_comp, S.zero, dualMap_zero])).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (carrierFunctor k₀ l X)]
  exact ProEtale.exact_ihomMap_app (hS.map (carrierFunctor k₀ l X)) _
    (hg := (carrierFunctor k₀ l X).map_epi S.g)

/-- The dual of a monomorphism of lisse Weil sheaves is an epimorphism. -/
theorem epi_dualMap {F G : WeilSheaf k₀ l X} (f : F ⟶ G) [Mono f] (hF : F.IsLisse)
    (hG : G.IsLisse) : Epi (dualMap f hF hG) := by
  have : IsLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
  have : Mono ((carrierFunctor k₀ l X).map f) := (carrierFunctor k₀ l X).map_mono f
  refine (carrierFunctor k₀ l X).epi_of_epi_map ?_
  rw [carrierFunctor_map_dualMap]
  exact ProEtale.IsAdicLisseSheaf.epi_ihomMap_app_of_mono hF hG _

/-- The dual of an epimorphism of lisse Weil sheaves is a monomorphism. -/
theorem mono_dualMap {F G : WeilSheaf k₀ l X} (f : F ⟶ G) [Epi f] (hF : F.IsLisse)
    (hG : G.IsLisse) : Mono (dualMap f hF hG) := by
  have : Epi ((carrierFunctor k₀ l X).map f) := (carrierFunctor k₀ l X).map_epi f
  refine (carrierFunctor k₀ l X).mono_of_mono_map ?_
  rw [carrierFunctor_map_dualMap]
  infer_instance

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The underlying morphism of `ℓ`-adic sheaves of `f ⊗ 𝟙 : F ⊗ G ⟶ F' ⊗ G`, for a morphism
`f : F ⟶ F'` of lisse Weil sheaves: the map `[F^∨, G] ⟶ [F'^∨, G]` induced by `f^∨`. -/
lemma carrierFunctor_map_tensorHom_id {F F' : WeilSheaf k₀ l X} (f : F ⟶ F') (G : WeilSheaf k₀ l X)
    (hF : F.IsLisse) (hF' : F'.IsLisse) :
    (carrierFunctor k₀ l X).map (tensorHom f (𝟙 G) hF hF') =
      (Mod.ihomMap ((carrierFunctor k₀ l X).map (dualMap f hF hF'))).app G.obj.carrier := by
  have h : (𝟙 G : G ⟶ G).hom.hom.f = 𝟙 _ := rfl
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Endofunctor.IsoAlgebra.forget_obj, tensorHom,
    Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.homMk_hom,
    Endofunctor.IsoAlgebra.forget_map, Endofunctor.IsoAlgebra.comp_hom_f,
    ProEtaleWeilSheaf.ihomMapRight_hom_f, h, CategoryTheory.Functor.map_id,
    ProEtaleWeilSheaf.ihomMapLeft_hom_f]
  exact Category.id_comp _

/-- **The tensor product is exact in the lisse variable.** If `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is a short
exact sequence of lisse Weil sheaves, then `A ⊗ G ⟶ B ⊗ G ⟶ C ⊗ G` is exact for every Weil
sheaf `G`: it is `[A^∨, G] ⟶ [B^∨, G] ⟶ [C^∨, G]`, and `C^∨ ⟶ B^∨ ⟶ A^∨ ⟶ 0` is exact. -/
theorem exact_tensorHom_id {S : ShortComplex (WeilSheaf k₀ l X)} (hS : S.Exact) [Mono S.f]
    [Epi S.g] (h₁ : S.X₁.IsLisse) (h₂ : S.X₂.IsLisse) (h₃ : S.X₃.IsLisse) (G : WeilSheaf k₀ l X) :
    (ShortComplex.mk (tensorHom S.f (𝟙 G) h₁ h₂) (tensorHom S.g (𝟙 G) h₂ h₃)
      ((carrierFunctor k₀ l X).map_injective (by
        rw [Functor.map_comp, carrierFunctor_map_tensorHom_id, carrierFunctor_map_tensorHom_id,
          ← NatTrans.comp_app, ← Mod.ihomMap_comp, ← Functor.map_comp, ← dualMap_comp, S.zero,
          dualMap_zero, Functor.map_zero, Functor.map_zero,
          ProEtale.ihomMap_zero_app]))).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (carrierFunctor k₀ l X)]
  have hD := exact_dualMap hS h₁ h₂ h₃
  have := epi_dualMap S.f h₁ h₂
  have h := ProEtale.exact_ihomMap_app (hD.map (carrierFunctor k₀ l X)) G.obj.carrier
    (hg := (carrierFunctor k₀ l X).map_epi (dualMap S.f h₁ h₂))
  refine (ShortComplex.exact_iff_of_iso ?_).1 h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
      exact carrierFunctor_map_tensorHom_id S.f G h₁ h₂)
    (by
      rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
      exact carrierFunctor_map_tensorHom_id S.g G h₂ h₃)

/-- The tensor product `G ↦ F ⊗ G = [F^∨, G]` with a lisse Weil sheaf `F`, as a functor. -/
noncomputable def tensorLeft (F : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l X :=
  ObjectProperty.lift _
    ((objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.ihomFunctor k₀ l X (F.dual hF).obj)
    fun G ↦ (F.tensorObj G hF).property

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The functor `tensorLeft F hF` is `G ↦ F ⊗ G` on objects. -/
lemma tensorLeft_obj (F : WeilSheaf k₀ l X) (hF : F.IsLisse) (G : WeilSheaf k₀ l X) :
    (tensorLeft F hF).obj G = F.tensorObj G hF :=
  rfl

instance (F : WeilSheaf k₀ l X) (hF : F.IsLisse) : PreservesFiniteLimits (tensorLeft F hF) := by
  have : ReflectsLimitsOfSize.{0, 0} (objectProperty k₀ l X).ι := inferInstance
  have : PreservesFiniteLimits (tensorLeft F hF ⋙ (objectProperty k₀ l X).ι) :=
    preservesFiniteLimits_of_natIso (ObjectProperty.liftCompιIso _ _ _).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (objectProperty k₀ l X).ι

instance (F : WeilSheaf k₀ l X) (hF : F.IsLisse) : PreservesFiniteColimits (tensorLeft F hF) := by
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (F.dual hF).obj hF.dual
  have : ReflectsColimitsOfSize.{0, 0} (objectProperty k₀ l X).ι := inferInstance
  have : PreservesFiniteColimits (tensorLeft F hF ⋙ (objectProperty k₀ l X).ι) :=
    preservesFiniteColimits_of_natIso (ObjectProperty.liftCompιIso _ _ _).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ (objectProperty k₀ l X).ι

instance (F : WeilSheaf k₀ l X) (hF : F.IsLisse) : (tensorLeft F hF).Additive :=
  Functor.additive_of_preserves_binary_products _

end AlgebraicGeometry.WeilSheaf

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The underlying pro-étale Weil sheaf of a tensor product. -/
lemma tensorObj_obj {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] (F G : WeilSheaf k₀ l X)
    (hF : F.IsLisse) :
    (F.tensorObj G hF).obj = ProEtaleWeilSheaf.ihom k₀ l X (F.dual hF).obj G.obj :=
  rfl

/-- The pullback of a tensor product with a lisse Weil sheaf is the tensor product of the
pullbacks: `φ^*(F ⊗ G) ≅ φ^*F ⊗ φ^*G`. -/
noncomputable def upperStarTensorObjIso {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] (F G : WeilSheaf k₀ l Y) (hF : F.IsLisse) :
    (WeilSheaf.upperStar φ).obj (F.tensorObj G hF) ≅
      ((WeilSheaf.upperStar φ).obj F).tensorObj ((WeilSheaf.upperStar φ).obj G)
        (hF.upperStar φ) :=
  ObjectProperty.isoMk _
    (eqToIso (by rw [WeilSheaf.upperStar_obj_obj, tensorObj_obj, Functor.comp_obj,
        ProEtaleWeilSheaf.ihomFunctor_obj]) ≪≫
      (ProEtaleWeilSheaf.ihomFunctorDualCompUpperStarIso φ F hF).app G.obj ≪≫
      eqToIso (by rw [Functor.comp_obj, ProEtaleWeilSheaf.ihomFunctor_obj, tensorObj_obj,
        WeilSheaf.upperStar_obj_obj]))

end AlgebraicGeometry.WeilSheaf
