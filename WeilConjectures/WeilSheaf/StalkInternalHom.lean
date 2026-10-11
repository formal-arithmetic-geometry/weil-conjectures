/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Trace
public import WeilConjectures.WeilSheaf.Dual

/-!
# Stalks of the internal hom out of a lisse Weil sheaf

For a lisse Weil sheaf `D` and a Weil sheaf `F`, the internal hom `[D, F]` is a Weil sheaf
(`AlgebraicGeometry.WeilSheaf.ihom`). At a geometric point `s`, the evaluation induces a
pairing `[D, F]_s × D_s → F_s` which is perfect (`D` being lisse,
`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing_ihom`) and compatible
with the Frobenius of the stalks
(`AlgebraicGeometry.WeilSheaf.ihomEvaluationPairing_stalkAt_frobenius`). Hence the Frobenius
of `[D, F]_s = Hom(D_s, F_s)` is `f ↦ F ∘ f ∘ F⁻¹`, and its trace is `tr(F | F_s) tr(F⁻¹ | D_s)`
(`AlgebraicGeometry.WeilSheaf.trace_frobeniusEnd_stalkAt_ihom`). For `D = G^∨` the dual of a
lisse Weil sheaf, `[G^∨, F]` is the tensor product `G ⊗ F`, and the trace function is
multiplicative: `t_{[G^∨, F]} = t_G t_F`
(`AlgebraicGeometry.WeilSheaf.traceFunction_ihom_dual`).

## Blueprint

These are the stalk computations behind "the trace of a tensor product is the product of the
traces" in the proof of the Fourier trace formula (sketch blueprint
`sk-thm-fourier-trace-formula`).
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Limits

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- Isomorphic Frobenius modules have the same trace of the inverse Frobenius. -/
theorem Equiv.trace_frobenius_symm {M N : FrobeniusModule.{u, v} K} (e : M.Equiv N) :
    LinearMap.trace K _ N.frobenius.symm.toLinearMap =
      LinearMap.trace K _ M.frobenius.symm.toLinearMap := by
  have h : N.frobenius.symm.toLinearMap =
      e.toLinearEquiv.conj M.frobenius.symm.toLinearMap := by
    refine LinearMap.ext fun x ↦ (LinearEquiv.symm_apply_eq _).2 ?_
    rw [LinearEquiv.conj_apply_apply, ← e.map_frobenius]
    simp
  rw [h, LinearMap.trace_conj']

/-- The inverse of the Frobenius of the dual `M^∨` is the transpose of the Frobenius of `M`, so
their traces agree. -/
theorem trace_dual_frobenius_symm (M : FrobeniusModule.{u, v} K) :
    LinearMap.trace K _ M.dual.frobenius.symm.toLinearMap =
      LinearMap.trace K _ M.frobeniusEnd := by
  rw [← LinearMap.trace_transpose' M.frobeniusEnd]
  congr 1

/-- If a perfect pairing `p : V × M → N` of Frobenius modules is compatible with the Frobenius,
then `tr(F | V) = tr(F | N) tr(F⁻¹ | M)` (`LinearMap.trace_eq_mul_of_bijective`). -/
theorem trace_frobeniusEnd_eq_mul_of_bijective {V M N : FrobeniusModule.{u, v} K}
    (p : V.carrier →ₗ[K] M.carrier →ₗ[K] N.carrier) (hp : Function.Bijective p)
    (h : ∀ v m, p (V.frobeniusEnd v) (M.frobenius m) = N.frobeniusEnd (p v m)) :
    LinearMap.trace K _ V.frobeniusEnd =
      LinearMap.trace K _ N.frobeniusEnd * LinearMap.trace K _ M.frobenius.symm.toLinearMap :=
  LinearMap.trace_eq_mul_of_bijective p hp _ _ _ h

end FrobeniusModule

namespace AlgebraicGeometry

namespace ProEtale

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K]

/-- **The stalk of the internal hom out of a lisse sheaf.** For `F` lisse, any sheaf `N` and a
geometric point `s`, the pairing `𝓗om(F, N)_s → Hom(F_s, N_s)` induced by the evaluation is
bijective: as for `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing`, the
point lifts to a member of a cover trivialising `F`, reducing the claim to a free sheaf. -/
theorem IsAdicLisseSheaf.bijective_evaluationPairing_ihom {Z : Scheme.{u}} {F : AdicSheaf l Z}
    (hF : IsAdicLisseSheaf F) (N : AdicSheaf l Z) (s : Spec (.of K) ⟶ Z) :
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

end ProEtale

namespace WeilCoefficients

variable {l : ℕ} [Fact l.Prime] {M N L : WeilCoefficients.{u} l}

/-- A bilinear map of modules over `ULift ℚ̄_ℓ`, as a `ℚ̄_ℓ`-bilinear map of the underlying
`ℚ̄_ℓ`-vector spaces. -/
noncomputable def bilinearMap
    (p : M →ₗ[ULift.{u + 1} (PadicAlgCl l)] N →ₗ[ULift (PadicAlgCl l)] L) :
    (toModuleCat l).obj M →ₗ[PadicAlgCl l] (toModuleCat l).obj N →ₗ[PadicAlgCl l]
      (toModuleCat l).obj L where
  toFun (m : M) :=
    { toFun (n : N) := (p m n : L)
      map_add' (n n' : N) := (p m).map_add n n'
      map_smul' c (n : N) := (p m).map_smul (ULift.up c) n }
  map_add' (m m' : M) := LinearMap.ext fun (n : N) ↦ LinearMap.congr_fun (p.map_add m m') n
  map_smul' c (m : M) :=
    LinearMap.ext fun (n : N) ↦ LinearMap.congr_fun (p.map_smul (ULift.up c) m) n

/-- The bilinear map `bilinearMap p` is computed by `p`. -/
lemma bilinearMap_apply (p : M →ₗ[ULift.{u + 1} (PadicAlgCl l)] N →ₗ[ULift (PadicAlgCl l)] L)
    (m : M) (n : N) : bilinearMap p m n = p m n :=
  rfl

/-- The `ℚ̄_ℓ`-bilinear map underlying a perfect pairing is perfect. -/
lemma bijective_bilinearMap
    {p : M →ₗ[ULift.{u + 1} (PadicAlgCl l)] N →ₗ[ULift (PadicAlgCl l)] L}
    (hp : Function.Bijective p) : Function.Bijective (bilinearMap p) := by
  refine ⟨fun (m : M) (m' : M) h ↦ hp.1 (LinearMap.ext fun (n : N) ↦ LinearMap.congr_fun h n),
    fun φ ↦ ?_⟩
  obtain ⟨m, hm⟩ := hp.2
    { toFun (n : N) := (φ n : L)
      map_add' (n n' : N) := φ.map_add n n'
      map_smul' c (n : N) := φ.map_smul c.down n }
  exact ⟨m, LinearMap.ext fun (n : N) ↦ LinearMap.congr_fun hm n⟩

end WeilCoefficients

namespace WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The internal hom `[D, F]` of Weil sheaves out of a lisse Weil sheaf `D`: the internal hom of
the underlying pro-étale Weil sheaves, which is constructible
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.ihom_of_isAdicLisseSheaf`). -/
noncomputable def ihom (D : WeilSheaf k₀ l X) (hD : D.IsLisse) (F : WeilSheaf k₀ l X) :
    WeilSheaf k₀ l X where
  obj := ProEtaleWeilSheaf.ihom k₀ l X D.obj F.obj
  property := IsAdicConstructibleSheaf.ihom_of_isAdicLisseSheaf hD F.property

/-- The evaluation `[D, F] ⊗ D ⟶ F` is compatible with the Weil structures. -/
theorem ihom_evaluation_str (D : WeilSheaf k₀ l X) (hD : D.IsLisse) (F : WeilSheaf k₀ l X) :
    ((D.ihom hD F).obj.str.hom.hom ⊗ₘ D.obj.str.hom.hom) ≫
        Mod.evaluation D.obj.carrier F.obj.carrier =
      μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l]
          (D.ihom hD F).obj.carrier.X D.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map
          (Mod.evaluation D.obj.carrier F.obj.carrier) ≫
        F.obj.str.hom.hom := by
  have : (Mod.mapModComap (G := ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[
      WeilCoefficients.{u} l]) (adicConstantSheafToLowerStar l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)).IsEquivalence :=
    isEquivalence_adicLowerStar l _
  have h := Mod.μ_comp_map_evaluation (adicConstantSheafToLowerStar l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) D.obj.carrier F.obj.carrier
  have hstr : (D.ihom hD F).obj.str.hom.hom =
      ((adicLowerStarCompIhomIso l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv
        D.obj.carrier).inv.app F.obj.carrier).hom ≫
      ((Mod.ihomMap D.obj.str.inv).app _).hom ≫
      ((ProEtale.AdicSheaf.ihom D.obj.carrier).map F.obj.str.hom).hom := rfl
  have hφ : D.obj.str.hom.hom ≫ D.obj.str.inv.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom']
  rw [hstr, tensorHom_def', comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  rw [Mod.evaluation_naturality D.obj.carrier F.obj.str.hom,
    Mod.evaluation_ihomMap_assoc D.obj.str.inv]
  erw [← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hφ,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  erw [reassoc_of% h]
  rfl

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s)

/-- The pairing `[D, F]_s × D_s → F_s` of stalks induced by the evaluation is compatible with
the Frobenius of the stalks. -/
lemma ihomEvaluationPairing_stalkAt_frobenius (D : WeilSheaf k₀ l X) (hD : D.IsLisse)
    (F : WeilSheaf k₀ l X) (v : ((D.ihom hD F).stalkAt s m hs).carrier)
    (x : (D.stalkAt s m hs).carrier) :
    Mod.evaluationPairing (stalkFunctor l s) D.obj.carrier F.obj.carrier
        (((D.ihom hD F).stalkAt s m hs).frobenius v) ((D.stalkAt s m hs).frobenius x) =
      (F.stalkAt s m hs).frobenius
        (Mod.evaluationPairing (stalkFunctor l s) D.obj.carrier F.obj.carrier v x) := by
  have h := stalkPairing_frobenius s m hs _ _ _ _
    (frobeniusPowIso_tensor (D.ihom hD F) D F _ (ihom_evaluation_str D hD F) m)
  rw [stalkAt_frobenius_eq_stalkFrobeniusIso, stalkAt_frobenius_eq_stalkFrobeniusIso,
    stalkAt_frobenius_eq_stalkFrobeniusIso, Mod.evaluationPairing_apply,
    Mod.evaluationPairing_apply]
  exact ModuleCat.tmul_eq_of_tensorHom_comp h v x

/-- The `ℚ̄_ℓ`-bilinear pairing `[D, F]_s × D_s → F_s` of stalks induced by the evaluation. -/
noncomputable def stalkAtIhomPairing (D : WeilSheaf k₀ l X) (hD : D.IsLisse)
    (F : WeilSheaf k₀ l X) :
    ((D.ihom hD F).stalkAt s m hs).carrier →ₗ[PadicAlgCl l]
      (D.stalkAt s m hs).carrier →ₗ[PadicAlgCl l] (F.stalkAt s m hs).carrier :=
  WeilCoefficients.bilinearMap
    (Mod.evaluationPairing (stalkFunctor l s) D.obj.carrier F.obj.carrier)

/-- The pairing `[D, F]_s × D_s → F_s` of stalks is perfect. -/
theorem bijective_stalkAtIhomPairing (D : WeilSheaf k₀ l X) (hD : D.IsLisse)
    (F : WeilSheaf k₀ l X) : Function.Bijective (stalkAtIhomPairing s m hs D hD F) :=
  WeilCoefficients.bijective_bilinearMap
    (IsAdicLisseSheaf.bijective_evaluationPairing_ihom hD _ s)

/-- The pairing of stalks is the pairing induced by the evaluation. -/
lemma stalkAtIhomPairing_apply (D : WeilSheaf k₀ l X) (hD : D.IsLisse)
    (F : WeilSheaf k₀ l X) (v : ((D.ihom hD F).stalkAt s m hs).carrier)
    (x : (D.stalkAt s m hs).carrier) :
    stalkAtIhomPairing s m hs D hD F v x =
      Mod.evaluationPairing (stalkFunctor l s) D.obj.carrier F.obj.carrier v x :=
  rfl

/-- The pairing `[D, F]_s × D_s → F_s` of stalks is compatible with the Frobenius. -/
theorem stalkAtIhomPairing_frobenius (D : WeilSheaf k₀ l X) (hD : D.IsLisse)
    (F : WeilSheaf k₀ l X) (v : ((D.ihom hD F).stalkAt s m hs).carrier)
    (x : (D.stalkAt s m hs).carrier) :
    stalkAtIhomPairing s m hs D hD F (((D.ihom hD F).stalkAt s m hs).frobeniusEnd v)
        ((D.stalkAt s m hs).frobenius x) =
      (F.stalkAt s m hs).frobeniusEnd (stalkAtIhomPairing s m hs D hD F v x) := by
  rw [FrobeniusModule.frobeniusEnd, FrobeniusModule.frobeniusEnd, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, stalkAtIhomPairing_apply, stalkAtIhomPairing_apply]
  exact ihomEvaluationPairing_stalkAt_frobenius s m hs D hD F v x

set_option maxHeartbeats 400000 in
-- The kernel needs more time to check the instantiation of the Frobenius compatibility.
/-- The trace of the Frobenius on the stalk of the internal hom `[D, F]` out of a lisse Weil
sheaf: `tr(F | [D, F]_s) = tr(F | F_s) tr(F⁻¹ | D_s)`, the stalk being `Hom(D_s, F_s)` with the
Frobenius `f ↦ F ∘ f ∘ F⁻¹`. -/
theorem trace_frobeniusEnd_stalkAt_ihom (D : WeilSheaf k₀ l X) (hD : D.IsLisse)
    (F : WeilSheaf k₀ l X) :
    LinearMap.trace (PadicAlgCl l) _ ((D.ihom hD F).stalkAt s m hs).frobeniusEnd =
      LinearMap.trace (PadicAlgCl l) _ (F.stalkAt s m hs).frobeniusEnd *
        LinearMap.trace (PadicAlgCl l) _ (D.stalkAt s m hs).frobenius.symm.toLinearMap :=
  FrobeniusModule.trace_frobeniusEnd_eq_mul_of_bijective _
    (bijective_stalkAtIhomPairing s m hs D hD F) (stalkAtIhomPairing_frobenius s m hs D hD F)

/-- The trace of the Frobenius on the stalk of `[G^∨, F] = G ⊗ F`, for a lisse Weil sheaf `G`,
is the product of the traces on the stalks of `G` and `F`. -/
theorem trace_frobeniusEnd_stalkAt_ihom_dual (G : WeilSheaf k₀ l X) (hG : G.IsLisse)
    (F : WeilSheaf k₀ l X) :
    LinearMap.trace (PadicAlgCl l) _ (((G.dual hG).ihom hG.dual F).stalkAt s m hs).frobeniusEnd =
      LinearMap.trace (PadicAlgCl l) _ (G.stalkAt s m hs).frobeniusEnd *
        LinearMap.trace (PadicAlgCl l) _ (F.stalkAt s m hs).frobeniusEnd := by
  rw [trace_frobeniusEnd_stalkAt_ihom, ← (stalkAtDualEquiv s m hs G hG).trace_frobenius_symm,
    FrobeniusModule.trace_dual_frobenius_symm, mul_comm]

/-- **The trace function is multiplicative under the tensor product with a lisse Weil sheaf.**
For a lisse Weil sheaf `G`, the trace function of `[G^∨, F] = G ⊗ F` is `t_G t_F`. -/
theorem traceFunction_ihom_dual (G : WeilSheaf k₀ l X) (hG : G.IsLisse) (F : WeilSheaf k₀ l X)
    (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    ((G.dual hG).ihom hG.dual F).traceFunction n x = G.traceFunction n x * F.traceFunction n x :=
  trace_frobeniusEnd_stalkAt_ihom_dual _ n _ G hG F

end WeilSheaf

end AlgebraicGeometry
