/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TraceFunction
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Hom
public import WeilConjectures.WeilSheaf.Tensor

/-!
# The stalks of the tensor product of a lisse Weil sheaf with a Weil sheaf

For a lisse Weil sheaf `F` and a Weil sheaf `G`, the tensor product `F ⊗ G` is the internal hom
`[F^∨, G]` (`AlgebraicGeometry.WeilSheaf.tensorObj`). At a geometric point `s` the evaluation
`[F^∨, G] ⊗ F^∨ ⟶ G` induces an isomorphism `(F ⊗ G)_s ≅ Hom((F^∨)_s, G_s)`, since `F^∨` is lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing_ihom`), under which the
Frobenius of the stalk becomes `φ ↦ F_G ∘ φ ∘ F_{F^∨}⁻¹`. Its trace is `tr F_G · tr F_F`, since
`F_{F^∨}⁻¹` is the transpose of `F_F`. Hence the traces of the powers of the local Frobenius of
`F ⊗ G` are the products of those of `F` and `G`.

## Main results

- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing_ihom`: the stalk of the
  internal hom out of a lisse sheaf is the space of linear maps of the stalks.
- `AlgebraicGeometry.WeilSheaf.ihom_evaluation_str`: the evaluation `[A, B] ⊗ A ⟶ B` is
  compatible with the Weil structures.
- `AlgebraicGeometry.WeilSheaf.trace_stalkAt_tensorObj_frobeniusEnd_pow`: the trace of the
  `k`-th power of the Frobenius on a stalk of `F ⊗ G` is the product of those of `F` and `G`.
- `AlgebraicGeometry.WeilSheaf.trace_stalk_tensorObj_frobeniusEnd_pow`: the same at the closed
  points.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Limits

namespace AlgebraicGeometry

namespace ProEtale

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K]

/-- **The stalk of the internal hom out of a lisse sheaf.** For `F` lisse, any `N` and a
geometric point `s`, the pairing `𝓗om(F, N)_s → Hom(F_s, N_s)` induced by the evaluation is
bijective: after pulling back to a member of a pro-étale cover trivialising `F` through which `s`
factors, `F` is free of finite rank. -/
theorem IsAdicLisseSheaf.bijective_evaluationPairing_ihom {Z : Scheme.{u}} {F : AdicSheaf l Z}
    (hF : IsAdicLisseSheaf F) (N : AdicSheaf l Z) (s : Spec (.of K) ⟶ Z) :
    Function.Bijective (Mod.evaluationPairing (ProEtale.stalkFunctor l s) F N) := by
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

end ProEtale

namespace WeilCoefficients

variable {l : ℕ} [Fact l.Prime] {M N L : WeilCoefficients.{u} l}

/-- A pairing `M × N → L` of modules over `ULift ℚ̄_ℓ`, as a `ℚ̄_ℓ`-linear map from `M` to the
`ℚ̄_ℓ`-linear maps `N → L`. -/
noncomputable def homLinearMap
    (p : M →ₗ[ULift.{u + 1} (PadicAlgCl l)] N →ₗ[ULift (PadicAlgCl l)] L) :
    (toModuleCat l).obj M →ₗ[PadicAlgCl l]
      ((toModuleCat l).obj N →ₗ[PadicAlgCl l] (toModuleCat l).obj L) where
  toFun (m : M) :=
    { toFun (n : N) := (p m n : L)
      map_add' (n n' : N) := map_add (p m) n n'
      map_smul' c (n : N) := map_smul (p m) (ULift.up c : ULift (PadicAlgCl l)) n }
  map_add' (m m' : M) := by
    ext (n : N)
    exact LinearMap.congr_fun (map_add p m m') n
  map_smul' c (m : M) := by
    ext (n : N)
    exact LinearMap.congr_fun (map_smul p (ULift.up c : ULift (PadicAlgCl l)) m) n

lemma homLinearMap_apply (p : M →ₗ[ULift.{u + 1} (PadicAlgCl l)] N →ₗ[ULift (PadicAlgCl l)] L)
    (m : M) (n : N) : homLinearMap p m n = p m n :=
  rfl

lemma bijective_homLinearMap
    {p : M →ₗ[ULift.{u + 1} (PadicAlgCl l)] N →ₗ[ULift (PadicAlgCl l)] L}
    (hp : Function.Bijective p) : Function.Bijective (homLinearMap p) := by
  refine ⟨fun (m : M) (m' : M) h ↦ hp.1 (LinearMap.ext fun (n : N) ↦ LinearMap.congr_fun h n),
    fun φ ↦ ?_⟩
  let ψ : N →ₗ[ULift.{u + 1} (PadicAlgCl l)] L :=
    { toFun (n : N) := (φ n : L)
      map_add' n n' := φ.map_add n n'
      map_smul' c n := φ.map_smul c.down n }
  obtain ⟨m, hm⟩ := hp.2 ψ
  exact ⟨m, LinearMap.ext fun (n : N) ↦ LinearMap.congr_fun hm n⟩

end WeilCoefficients

namespace WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The evaluation `[A, B] ⊗ A ⟶ B` is compatible with the Weil structures. -/
theorem ihom_evaluation_str (A B : WeilSheaf k₀ l X) :
    ((ProEtaleWeilSheaf.ihom k₀ l X A.obj B.obj).str.hom.hom ⊗ₘ A.obj.str.hom.hom) ≫
        Mod.evaluation A.obj.carrier B.obj.carrier =
      μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l]
          (ProEtaleWeilSheaf.ihom k₀ l X A.obj B.obj).carrier.X A.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map
          (Mod.evaluation A.obj.carrier B.obj.carrier) ≫
        B.obj.str.hom.hom := by
  have : (Mod.mapModComap (G := ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[
      WeilCoefficients.{u} l]) (adicConstantSheafToLowerStar l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)).IsEquivalence :=
    isEquivalence_adicLowerStar l _
  have h := Mod.μ_comp_map_evaluation (adicConstantSheafToLowerStar l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) A.obj.carrier B.obj.carrier
  have hstr : (ProEtaleWeilSheaf.ihom k₀ l X A.obj B.obj).str.hom.hom =
      ((adicLowerStarCompIhomIso l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv
        A.obj.carrier).inv.app B.obj.carrier).hom ≫
      ((Mod.ihomMap A.obj.str.inv).app _).hom ≫
      ((ProEtale.AdicSheaf.ihom A.obj.carrier).map B.obj.str.hom).hom := rfl
  have hφ : A.obj.str.hom.hom ≫ A.obj.str.inv.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom']
  rw [hstr, tensorHom_def', comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  rw [Mod.evaluation_naturality A.obj.carrier B.obj.str.hom,
    Mod.evaluation_ihomMap_assoc A.obj.str.inv]
  erw [← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hφ,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  erw [reassoc_of% h]
  rfl

section StalkAt

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s)

/-- The pairing `(F ⊗ G)_s × (F^∨)_s → G_s` induced by the evaluation intertwines the Frobenius
of the stalks. -/
lemma evaluationPairing_stalkAt_tensorObj_frobenius (F G : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (d : ((F.tensorObj G hF).stalkAt s m hs).carrier) (x : ((F.dual hF).stalkAt s m hs).carrier) :
    Mod.evaluationPairing (ProEtale.stalkFunctor l s) (F.dual hF).obj.carrier G.obj.carrier
        (((F.tensorObj G hF).stalkAt s m hs).frobenius d)
        (((F.dual hF).stalkAt s m hs).frobenius x) =
      (G.stalkAt s m hs).frobenius
        (Mod.evaluationPairing (ProEtale.stalkFunctor l s) (F.dual hF).obj.carrier G.obj.carrier
          d x) := by
  have h := stalkPairing_frobenius s m hs _ _ _ _
    (frobeniusPowIso_tensor (F.tensorObj G hF) (F.dual hF) G _
      (ihom_evaluation_str (F.dual hF) G) m)
  rw [stalkAt_frobenius_eq_stalkFrobeniusIso, stalkAt_frobenius_eq_stalkFrobeniusIso,
    stalkAt_frobenius_eq_stalkFrobeniusIso, Mod.evaluationPairing_apply,
    Mod.evaluationPairing_apply]
  exact ModuleCat.tmul_eq_of_tensorHom_comp h d x

/-- The stalk `(F ⊗ G)_s` is the space of linear maps `(F^∨)_s → G_s`. -/
noncomputable def stalkAtTensorObjEquiv (F G : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    ((F.tensorObj G hF).stalkAt s m hs).carrier ≃ₗ[PadicAlgCl l]
      (((F.dual hF).stalkAt s m hs).carrier →ₗ[PadicAlgCl l] (G.stalkAt s m hs).carrier) :=
  LinearEquiv.ofBijective
    (WeilCoefficients.homLinearMap
      (Mod.evaluationPairing (ProEtale.stalkFunctor l s) (F.dual hF).obj.carrier G.obj.carrier))
    (WeilCoefficients.bijective_homLinearMap
      (hF.dual.bijective_evaluationPairing_ihom G.obj.carrier s))

lemma stalkAtTensorObjEquiv_apply (F G : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (d : ((F.tensorObj G hF).stalkAt s m hs).carrier) (x : ((F.dual hF).stalkAt s m hs).carrier) :
    stalkAtTensorObjEquiv s m hs F G hF d x =
      Mod.evaluationPairing (ProEtale.stalkFunctor l s) (F.dual hF).obj.carrier G.obj.carrier d x :=
  rfl

/-- Under `(F ⊗ G)_s ≅ Hom((F^∨)_s, G_s)` the Frobenius of `(F ⊗ G)_s` is
`φ ↦ F_G ∘ φ ∘ F_{F^∨}⁻¹`. -/
lemma stalkAtTensorObjEquiv_frobenius (F G : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (d : ((F.tensorObj G hF).stalkAt s m hs).carrier) :
    stalkAtTensorObjEquiv s m hs F G hF (((F.tensorObj G hF).stalkAt s m hs).frobenius d) =
      (G.stalkAt s m hs).frobeniusEnd ∘ₗ stalkAtTensorObjEquiv s m hs F G hF d ∘ₗ
        ((F.dual hF).stalkAt s m hs).frobenius.symm.toLinearMap := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := ((F.dual hF).stalkAt s m hs).frobenius.surjective x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, stalkAtTensorObjEquiv_apply, stalkAtTensorObjEquiv_apply,
    FrobeniusModule.frobeniusEnd, LinearEquiv.coe_coe]
  exact evaluationPairing_stalkAt_tensorObj_frobenius s m hs F G hF d y

/-- The trace of the `k`-th power of the Frobenius on the stalk of `F ⊗ G` at `s` is the product
of the traces on the stalks of `G` and `F`. -/
theorem trace_stalkAt_tensorObj_frobeniusEnd_pow (F G : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (k : ℕ) :
    LinearMap.trace (PadicAlgCl l) _ (((F.tensorObj G hF).stalkAt s m hs).frobeniusEnd ^ k) =
      LinearMap.trace (PadicAlgCl l) _ ((G.stalkAt s m hs).frobeniusEnd ^ k) *
        LinearMap.trace (PadicAlgCl l) _ ((F.stalkAt s m hs).frobeniusEnd ^ k) := by
  rw [FrobeniusModule.trace_frobeniusEnd_pow_eq_mul_of_linearEquiv _ _ _
    (stalkAtTensorObjEquiv s m hs F G hF) (stalkAtTensorObjEquiv_frobenius s m hs F G hF),
    ← (stalkAtDualEquiv s m hs F hF).trace_frobenius_symm_pow,
    FrobeniusModule.trace_dual_frobenius_symm_pow]

end StalkAt

/-- At a closed point `x`, the trace of the `k`-th power of the local Frobenius of `F ⊗ G` is
the product of those of `G` and `F`. -/
theorem trace_stalk_tensorObj_frobeniusEnd_pow (F G : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (x : X.finitePoints) (k : ℕ) :
    LinearMap.trace (PadicAlgCl l) _ (((F.tensorObj G hF).stalk x).frobeniusEnd ^ k) =
      LinearMap.trace (PadicAlgCl l) _ ((G.stalk x).frobeniusEnd ^ k) *
        LinearMap.trace (PadicAlgCl l) _ ((F.stalk x).frobeniusEnd ^ k) :=
  trace_stalkAt_tensorObj_frobeniusEnd_pow _ _ _ F G hF k

/-- The trace function of `F ⊗ G` is the product of the trace functions of `G` and `F`. -/
theorem traceFunction_tensorObj (F G : WeilSheaf k₀ l X) (hF : F.IsLisse) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    (F.tensorObj G hF).traceFunction n y = G.traceFunction n y * F.traceFunction n y := by
  rw [traceFunction_eq_trace, traceFunction_eq_trace, traceFunction_eq_trace,
    trace_stalk_tensorObj_frobeniusEnd_pow]

/-- The tensor product of two lisse Weil sheaves is lisse. -/
theorem IsLisse.tensorObj {F G : WeilSheaf k₀ l X} (hF : F.IsLisse) (hG : G.IsLisse) :
    (F.tensorObj G hF).IsLisse :=
  ProEtale.IsAdicLisseSheaf.ihom hF.dual hG

/-- The tensor product of lisse `F` punctually `ι`-pure of weight `w₁` with `G` punctually `ι`-pure
of weight `w₂` is punctually `ι`-pure of weight `w₁ + w₂`: the local eigenvalues of `F ⊗ G` are
products of local eigenvalues of `F` and `G`. -/
theorem IsPunctuallyPureOfWeight.tensorObj {ι : PadicAlgCl l →+* ℂ} {F G : WeilSheaf k₀ l X}
    (hF : F.IsLisse) {w₁ w₂ : ℝ} (h₁ : F.IsPunctuallyPureOfWeight ι w₁)
    (h₂ : G.IsPunctuallyPureOfWeight ι w₂) :
    (F.tensorObj G hF).IsPunctuallyPureOfWeight ι (w₁ + w₂) := by
  intro x
  have hA : ((F.dual hF).stalk x).IsPureOfWeight ι
      ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) (-w₁) :=
    (h₁ x).dual.of_equiv (stalkAtDualEquiv _ _ _ F hF)
  have h := FrobeniusModule.IsPureOfWeight.of_linearEquiv_hom (pow_pos Nat.card_pos _)
    (stalkAtTensorObjEquiv _ _ _ F G hF) (stalkAtTensorObjEquiv_frobenius _ _ _ F G hF) hA (h₂ x)
  rwa [sub_neg_eq_add, add_comm] at h

end WeilSheaf

end AlgebraicGeometry
