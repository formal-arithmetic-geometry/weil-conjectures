/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Tensor

/-!
# Stalks of tensor products of Weil sheaves

The tensor product `F ⊗ G` of a lisse Weil sheaf `F` with a Weil sheaf `G` is the internal hom
`[F^∨, G]` (`AlgebraicGeometry.WeilSheaf.tensorObj`). Its stalk at a geometric point is
`Hom(F^∨_s, G_s)`, with the Frobenius `f ↦ F_G ∘ f ∘ F_{F^∨}⁻¹`: the pairing of stalks
`[F^∨, G]_s × F^∨_s → G_s` induced by the evaluation is perfect since `F^∨` is lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing_of_lisse`), and it is
compatible with the Frobenius since the evaluation is compatible with the Weil structures
(`AlgebraicGeometry.ProEtaleWeilSheaf.ihom_evaluation_str`).

## Main declarations

- `FrobeniusModule.linearHom`: the Frobenius module `Hom_K(M, N)`.
- `AlgebraicGeometry.WeilSheaf.stalkAtTensorObjEquiv`: the stalk of `F ⊗ G` at a geometric point
  is `Hom(F^∨_s, G_s)`.
- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_tensorObj`: the same at a closed point.
-/

@[expose] public section

universe u v t

open CategoryTheory MonoidalCategory Endofunctor Limits

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- The Frobenius module `Hom_K(M, N)` with the Frobenius `f ↦ F_N ∘ f ∘ F_M⁻¹`. -/
noncomputable def linearHom (M : FrobeniusModule.{u, v} K) (N : FrobeniusModule.{t, v} K) :
    FrobeniusModule.{max u t, v} K where
  carrier := M.carrier →ₗ[K] N.carrier
  frobenius := M.frobenius.arrowCongr N.frobenius

/-- The Frobenius of `Hom_K(M, N)` sends `f` to `F_N ∘ f ∘ F_M⁻¹`. -/
lemma linearHom_frobenius_apply (M : FrobeniusModule.{u, v} K) (N : FrobeniusModule.{t, v} K)
    (f : M.carrier →ₗ[K] N.carrier) :
    (M.linearHom N).frobenius f =
      N.frobenius.toLinearMap ∘ₗ f ∘ₗ M.frobenius.symm.toLinearMap :=
  rfl

/-- A line on which the Frobenius acts by the scalar `μ` has `μ ≠ 0`. -/
lemma ne_zero_of_frobeniusEnd_eq_smul {M : FrobeniusModule.{u, v} K}
    (hM : Module.finrank K M.carrier = 1) {μ : K} (hμ : M.frobeniusEnd = μ • LinearMap.id) :
    μ ≠ 0 := by
  rintro rfl
  have hb := (Module.finBasisOfFinrankEq K M.carrier hM).ne_zero 0
  rw [← M.frobenius.map_ne_zero_iff] at hb
  exact hb ((LinearMap.congr_fun hμ _).trans (by rw [zero_smul, LinearMap.zero_apply]))

/-- On a line on which the Frobenius acts by the scalar `μ`, the inverse Frobenius acts by
`μ⁻¹`. -/
lemma frobenius_symm_apply_of_finrank_eq_one {M : FrobeniusModule.{u, v} K}
    (hM : Module.finrank K M.carrier = 1) {μ : K} (hμ : M.frobeniusEnd = μ • LinearMap.id)
    (x : M.carrier) : M.frobenius.symm x = μ⁻¹ • x := by
  have hF (y : M.carrier) : M.frobenius y = μ • y := LinearMap.congr_fun hμ y
  refine M.frobenius.injective ?_
  rw [LinearEquiv.apply_symm_apply, map_smul, hF, smul_smul,
    inv_mul_cancel₀ (ne_zero_of_frobeniusEnd_eq_smul hM hμ), one_smul]

/-- If the Frobenius of a line `M` is multiplication by `μ`, then `Hom_K(M, N)` is `N` with the
Frobenius rescaled by `μ⁻¹`, through the evaluation at a basis vector of `M`. -/
noncomputable def linearHomEquivRescale {M N : FrobeniusModule.{u, v} K}
    (hM : Module.finrank K M.carrier = 1) {μ : K} (hμ : M.frobeniusEnd = μ • LinearMap.id) :
    (M.linearHom N).Equiv (N.rescale μ⁻¹) where
  toLinearEquiv := ((Module.finBasisOfFinrankEq K M.carrier hM).constr K).symm ≪≫ₗ
    LinearEquiv.funUnique (Fin 1) K N.carrier
  map_frobenius (f : M.carrier →ₗ[K] N.carrier) := by
    refine Eq.trans ?_ (frobeniusEnd_rescale_apply (M := N)
      (inv_ne_zero (ne_zero_of_frobeniusEnd_eq_smul hM hμ)) _).symm
    calc _ = N.frobenius (f (M.frobenius.symm (Module.finBasisOfFinrankEq K M.carrier hM 0))) :=
          rfl
      _ = μ⁻¹ • N.frobenius (f (Module.finBasisOfFinrankEq K M.carrier hM 0)) := by
          rw [frobenius_symm_apply_of_finrank_eq_one hM hμ, map_smul, map_smul]

end FrobeniusModule

namespace AlgebraicGeometry.ProEtale

open Functor.LaxMonoidal

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K]

/-- **The stalk of an internal hom out of a lisse sheaf.** For `F` lisse, any sheaf `N` and a
geometric point `s`, the pairing `𝓗om(F, N)_s → Hom(F_s, N_s)` induced by the evaluation is
bijective. -/
theorem IsAdicLisseSheaf.bijective_evaluationPairing_of_lisse {Z : Scheme.{u}}
    {F : AdicSheaf l Z} (hF : IsAdicLisseSheaf F) (N : AdicSheaf l Z) (s : Spec (.of K) ⟶ Z) :
    Function.Bijective (Mod.evaluationPairing (stalkFunctor l s) F N) := by
  obtain ⟨R, hR, h⟩ := hF
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hR' : _ ∈ Scheme.precoverage (@WeaklyEtale : MorphismProperty Scheme.{u}) _ :=
    (show Scheme.proetalePrecoverage ≤ Scheme.precoverage @WeaklyEtale from inf_le_right) _ hR
  rw [Scheme.ofArrows_mem_precoverage_iff (@WeaklyEtale : MorphismProperty Scheme.{u})] at hR'
  obtain ⟨i, v, hv⟩ := hR'.1 (s.base (IsLocalRing.closedPoint K))
  have : WeaklyEtale (f i) := hR'.2 i
  obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback (f := f i) (g := s)
    v (IsLocalRing.closedPoint K) hv
  have : WeaklyEtale (pullback.snd (f i) s) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @WeaklyEtale)
      (IsPullback.of_hasPullback (f i) s) ‹_›
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale (pullback.snd (f i) s) p
  have hs : (σ ≫ pullback.fst (f i) s) ≫ f i = s := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  rw [← hs, bijective_evaluationPairing_comp_iff]
  obtain ⟨n, ⟨e⟩⟩ := h (f i) (.mk i)
  have : IsIso (ε (stalkFunctor l (σ ≫ pullback.fst (f i) s)) ≫
      (stalkFunctor l (σ ≫ pullback.fst (f i) s)).map
        (MonObj.one (X := adicConstantSheaf l (V i)))) :=
    isIso_unitSection (l := l) (σ ≫ pullback.fst (f i) s)
  exact Mod.bijective_evaluationPairing_of_iso_biproduct _ e _

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilCoefficients

variable {l : ℕ} [Fact l.Prime] {M N L : WeilCoefficients.{u} l}

/-- A pairing `M × N → L` of modules over `ULift ℚ̄_ℓ`, as a `ℚ̄_ℓ`-linear map from `M` to the
`ℚ̄_ℓ`-linear maps `N → L`. -/
noncomputable def homLinearMap
    (p : M →ₗ[ULift.{u + 1} (PadicAlgCl l)] N →ₗ[ULift (PadicAlgCl l)] L) :
    (toModuleCat l).obj M →ₗ[PadicAlgCl l]
      ((toModuleCat l).obj N →ₗ[PadicAlgCl l] (toModuleCat l).obj L) where
  toFun (m : M) :=
    { toFun (n : N) := p m n
      map_add' (n n' : N) := map_add (p m) n n'
      map_smul' c (n : N) := map_smul (p m) (ULift.up c : ULift (PadicAlgCl l)) n }
  map_add' (m m' : M) := by
    ext (n : N)
    change p (m + m') n = p m n + p m' n
    rw [map_add, LinearMap.add_apply]
  map_smul' c (m : M) := by
    ext (n : N)
    change p ((ULift.up c : ULift (PadicAlgCl l)) • m) n =
      (ULift.up c : ULift (PadicAlgCl l)) • p m n
    rw [map_smul, LinearMap.smul_apply]

lemma homLinearMap_apply (p : M →ₗ[ULift.{u + 1} (PadicAlgCl l)] N →ₗ[ULift (PadicAlgCl l)] L)
    (m : M) (n : N) : homLinearMap p m n = p m n :=
  rfl

/-- A bijective pairing `M → Hom(N, L)` of modules over `ULift ℚ̄_ℓ` stays bijective as a map to
the `ℚ̄_ℓ`-linear maps. -/
lemma bijective_homLinearMap
    {p : M →ₗ[ULift.{u + 1} (PadicAlgCl l)] N →ₗ[ULift (PadicAlgCl l)] L}
    (hp : Function.Bijective p) : Function.Bijective (homLinearMap p) := by
  refine ⟨fun (m : M) (m' : M) h ↦ hp.1 (LinearMap.ext fun (n : N) ↦ ?_), fun φ ↦ ?_⟩
  · exact LinearMap.congr_fun h n
  · let ψ : N →ₗ[ULift.{u + 1} (PadicAlgCl l)] L :=
      { toFun (n : N) := φ n
        map_add' n n' := φ.map_add n n'
        map_smul' c n := φ.map_smul c.down n }
    obtain ⟨m, hm⟩ := hp.2 ψ
    exact ⟨m, LinearMap.ext fun (n : N) ↦ LinearMap.congr_fun hm n⟩

end AlgebraicGeometry.WeilCoefficients

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

open Functor.LaxMonoidal ProEtale

omit [Fact (ringChar k₀ ≠ l)] in
/-- The evaluation `[A, B] ⊗ A ⟶ B` is compatible with the Weil structures. -/
theorem ProEtaleWeilSheaf.ihom_evaluation_str (A B : ProEtaleWeilSheaf k₀ l X) :
    ((ProEtaleWeilSheaf.ihom k₀ l X A B).str.hom.hom ⊗ₘ A.str.hom.hom) ≫
        Mod.evaluation A.carrier B.carrier =
      μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l]
          ((ProEtale.AdicSheaf.ihom A.carrier).obj B.carrier).X A.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map
          (Mod.evaluation A.carrier B.carrier) ≫
        B.str.hom.hom := by
  have : (Mod.mapModComap (G := ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[
      WeilCoefficients.{u} l]) (adicConstantSheafToLowerStar l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)).IsEquivalence :=
    isEquivalence_adicLowerStar l _
  have h := Mod.μ_comp_map_evaluation (adicConstantSheafToLowerStar l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) A.carrier B.carrier
  have hstr : (ProEtaleWeilSheaf.ihom k₀ l X A B).str.hom.hom =
      ((adicLowerStarCompIhomIso l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv
        A.carrier).inv.app B.carrier).hom ≫
      ((Mod.ihomMap A.str.inv).app _).hom ≫
      ((ProEtale.AdicSheaf.ihom A.carrier).map B.str.hom).hom := rfl
  have hφ : A.str.hom.hom ≫ A.str.inv.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom']
  rw [hstr, tensorHom_def', comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  rw [Mod.evaluation_naturality A.carrier B.str.hom, Mod.evaluation_ihomMap_assoc A.str.inv]
  erw [← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hφ,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  erw [reassoc_of% h]
  rfl

namespace WeilSheaf

section TensorStalk

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s)

/-- The pairing `(F ⊗ G)_s × (F^∨)_s → G_s` of stalks induced by the evaluation
`[F^∨, G] ⊗ F^∨ ⟶ G` intertwines the Frobenius of the stalks. -/
lemma evaluationPairing_stalkAt_tensorObj_frobenius {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (G : WeilSheaf k₀ l X) (d : ((F.tensorObj G hF).stalkAt s m hs).carrier)
    (x : ((F.dual hF).stalkAt s m hs).carrier) :
    Mod.evaluationPairing (stalkFunctor l s) (F.dual hF).obj.carrier G.obj.carrier
        (((F.tensorObj G hF).stalkAt s m hs).frobenius d)
        (((F.dual hF).stalkAt s m hs).frobenius x) =
      (G.stalkAt s m hs).frobenius
        (Mod.evaluationPairing (stalkFunctor l s) (F.dual hF).obj.carrier G.obj.carrier d x) := by
  have h := stalkPairing_frobenius s m hs _ _ _ _
    (frobeniusPowIso_tensor (F.tensorObj G hF) (F.dual hF) G _
      (ProEtaleWeilSheaf.ihom_evaluation_str (F.dual hF).obj G.obj) m)
  rw [stalkAt_frobenius_eq_stalkFrobeniusIso, stalkAt_frobenius_eq_stalkFrobeniusIso,
    stalkAt_frobenius_eq_stalkFrobeniusIso, Mod.evaluationPairing_apply,
    Mod.evaluationPairing_apply]
  exact ModuleCat.tmul_eq_of_tensorHom_comp h d x

/-- The `ℚ̄_ℓ`-linear isomorphism `(F ⊗ G)_s ≅ Hom((F^∨)_s, G_s)` induced by the evaluation
`[F^∨, G] ⊗ F^∨ ⟶ G`; it is bijective since `F^∨` is lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing_of_lisse`). -/
noncomputable def stalkAtTensorObjLinearEquiv {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (G : WeilSheaf k₀ l X) :
    ((F.tensorObj G hF).stalkAt s m hs).carrier ≃ₗ[PadicAlgCl l]
      (((F.dual hF).stalkAt s m hs).carrier →ₗ[PadicAlgCl l] (G.stalkAt s m hs).carrier) :=
  LinearEquiv.ofBijective
    (WeilCoefficients.homLinearMap
      (Mod.evaluationPairing (stalkFunctor l s) (F.dual hF).obj.carrier G.obj.carrier))
    (WeilCoefficients.bijective_homLinearMap
      (IsAdicLisseSheaf.bijective_evaluationPairing_of_lisse hF.dual _ s))

lemma stalkAtTensorObjLinearEquiv_apply {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (G : WeilSheaf k₀ l X) (d : ((F.tensorObj G hF).stalkAt s m hs).carrier)
    (x : ((F.dual hF).stalkAt s m hs).carrier) :
    stalkAtTensorObjLinearEquiv s m hs hF G d x =
      Mod.evaluationPairing (stalkFunctor l s) (F.dual hF).obj.carrier G.obj.carrier d x :=
  rfl

/-- The isomorphism `(F ⊗ G)_s ≅ Hom((F^∨)_s, G_s)` intertwines the Frobenius of `(F ⊗ G)_s`
with `f ↦ F_G ∘ f ∘ F_{F^∨}⁻¹`. -/
lemma stalkAtTensorObjLinearEquiv_frobenius {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (G : WeilSheaf k₀ l X) (d : ((F.tensorObj G hF).stalkAt s m hs).carrier) :
    stalkAtTensorObjLinearEquiv s m hs hF G (((F.tensorObj G hF).stalkAt s m hs).frobenius d) =
      (G.stalkAt s m hs).frobenius.toLinearMap ∘ₗ stalkAtTensorObjLinearEquiv s m hs hF G d ∘ₗ
        ((F.dual hF).stalkAt s m hs).frobenius.symm.toLinearMap := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := ((F.dual hF).stalkAt s m hs).frobenius.surjective x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, stalkAtTensorObjLinearEquiv_apply,
    stalkAtTensorObjLinearEquiv_apply]
  exact evaluationPairing_stalkAt_tensorObj_frobenius s m hs hF G d y

/-- The isomorphism `(F ⊗ G)_s ≅ Hom((F^∨)_s, G_s)` intertwines the Frobenius of `(F ⊗ G)_s`
with that of the Frobenius module `Hom((F^∨)_s, G_s)`. -/
lemma stalkAtTensorObjLinearEquiv_map_frobenius {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (G : WeilSheaf k₀ l X) (d : ((F.tensorObj G hF).stalkAt s m hs).carrier) :
    stalkAtTensorObjLinearEquiv s m hs hF G (((F.tensorObj G hF).stalkAt s m hs).frobenius d) =
      (((F.dual hF).stalkAt s m hs).linearHom (G.stalkAt s m hs)).frobenius
        (stalkAtTensorObjLinearEquiv s m hs hF G d) := by
  rw [FrobeniusModule.linearHom_frobenius_apply]
  exact stalkAtTensorObjLinearEquiv_frobenius s m hs hF G d

/-- The stalk of the tensor product `F ⊗ G = [F^∨, G]` at a geometric point is
`Hom(F^∨_s, G_s)` with the Frobenius `f ↦ F_G ∘ f ∘ F_{F^∨}⁻¹`: the pairing of stalks induced by
the evaluation is perfect
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing_of_lisse`) and
compatible with the Frobenius
(`AlgebraicGeometry.WeilSheaf.evaluationPairing_stalkAt_tensorObj_frobenius`). -/
noncomputable def stalkAtTensorObjEquiv {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (G : WeilSheaf k₀ l X) :
    ((F.tensorObj G hF).stalkAt s m hs).Equiv
      (((F.dual hF).stalkAt s m hs).linearHom (G.stalkAt s m hs)) where
  toLinearEquiv := stalkAtTensorObjLinearEquiv s m hs hF G
  map_frobenius := stalkAtTensorObjLinearEquiv_map_frobenius s m hs hF G

end TensorStalk

/-- The stalk of the tensor product `F ⊗ G` of a lisse Weil sheaf `F` and a Weil sheaf `G` at a
closed point `x` is `Hom((F^∨)_x, G_x)`, with the Frobenius `f ↦ F_G ∘ f ∘ F_{F^∨}⁻¹`. -/
theorem nonempty_equiv_stalk_tensorObj {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (G : WeilSheaf k₀ l X) (x : X.finitePoints) :
    Nonempty (((F.tensorObj G hF).stalk x).Equiv (((F.dual hF).stalk x).linearHom (G.stalk x))) :=
  ⟨stalkAtTensorObjEquiv _ _ _ hF G⟩

end WeilSheaf

end AlgebraicGeometry
