/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.Tensor
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Tensor

/-!
# Stalks of tensor products of Weil sheaves

Let `L` be a lisse `ℓ`-adic sheaf and `G` any `ℓ`-adic sheaf. At a geometric point `s`, the
evaluation `𝓗om(L, G) ⊗ L ⟶ G` induces a bijection `𝓗om(L, G)_s ≅ Hom(L_s, G_s)`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing_ihom`): this
generalises the computation of the stalks of the dual `𝓗om(L, ℚ̄_ℓ)`.

For Weil sheaves the evaluation is compatible with the Weil structures
(`AlgebraicGeometry.ProEtaleWeilSheaf.ihom_evaluation_str`), so the bijection intertwines the
local Frobenius of `𝓗om(L, G)` with the conjugation `X ↦ F_G ∘ X ∘ F_L⁻¹`. Applied to the tensor
product `F ⊗ G = 𝓗om(F^∨, G)` of a lisse Weil sheaf `F` with a Weil sheaf `G`, together with
`(F^∨)_s ≅ (F_s)^∨`, this identifies the stalk of `F ⊗ G` with `F_s ⊗ G_s` and its local
Frobenius with the tensor product of the local Frobenii.

## Main declarations

- `AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing_ihom`:
  `𝓗om(L, G)_s ≅ Hom(L_s, G_s)` for `L` lisse.
- `AlgebraicGeometry.WeilSheaf.stalkAtTensorObjHomEquiv`: `(F ⊗ G)_s ≅ Hom((F^∨)_s, G_s)`.
- `AlgebraicGeometry.WeilSheaf.stalkAtTensorObjEquiv`: `(F ⊗ G)_s ≅ F_s ⊗ G_s`.
- `AlgebraicGeometry.WeilSheaf.stalkTensorObjEquiv`: the same at a closed point.
- `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.tensorObj`,
  `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.tensorObj`: weights add under tensor
  products; `AlgebraicGeometry.WeilSheaf.hasEigenvalue_stalk_tensorObj` and
  `AlgebraicGeometry.WeilSheaf.exists_of_hasEigenvalue_stalk_tensorObj`: the eigenvalues of the
  local Frobenius of `F ⊗ G` are the products of those of `F` and `G`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Limits Endofunctor

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {K : Type u} [Field K] [IsAlgClosed K]

/-- **The stalk of the internal hom out of a lisse sheaf.** For `F` lisse, any `N` and a
geometric point `s`, the pairing `𝓗om(F, N)_s → Hom(F_s, N_s)` induced by the evaluation is
bijective. -/
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

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilCoefficients

variable {l : ℕ} [Fact l.Prime]

/-- `FrobeniusModule.Equiv.ofBilinear` for Frobenius modules over `ℚ̄_ℓ`: a perfect
Frobenius-invariant pairing `P × A → C` identifies `P` with `Hom(A, C)`.

Implementation note: the type of `p` is elaborated here with the instances of `ℚ̄_ℓ` itself, as in
the statements about stalks of Weil sheaves; applying the general
`FrobeniusModule.Equiv.ofBilinear` directly to stalks makes the kernel compare the two
elaborations of these instances in the presence of the stalks, which is very expensive. -/
noncomputable def frobeniusEquivOfBilinear {P A C : FrobeniusModule.{u + 1, 0} (PadicAlgCl l)}
    (p : P.carrier →ₗ[PadicAlgCl l] A.carrier →ₗ[PadicAlgCl l] C.carrier)
    (hp : Function.Bijective p)
    (h : ∀ x y, p (P.frobenius x) (A.frobenius y) = C.frobenius (p x y)) : P.Equiv (A.hom C) :=
  FrobeniusModule.Equiv.ofBilinear p hp h

end AlgebraicGeometry.WeilCoefficients

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

open ProEtale

omit [Fact (ringChar k₀ ≠ l)] in
/-- The evaluation `[A, B] ⊗ A ⟶ B` is compatible with the Weil structures of `A`, `B` and of
the internal hom `[A, B]` (`AlgebraicGeometry.ProEtaleWeilSheaf.ihom`). -/
theorem ProEtaleWeilSheaf.ihom_evaluation_str (A B : ProEtaleWeilSheaf k₀ l X) :
    ((ProEtaleWeilSheaf.ihom k₀ l X A B).str.hom.hom ⊗ₘ A.str.hom.hom) ≫
        Mod.evaluation A.carrier B.carrier =
      μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l]
          ((ProEtaleWeilSheaf.ihom k₀ l X A B).carrier.X) A.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map
          (Mod.evaluation A.carrier B.carrier) ≫ B.str.hom.hom := by
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

section StalkAt

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s)

/-- The pairing `(F ⊗ G)_s × (F^∨)_s → G_s` of stalks induced by the evaluation
`[F^∨, G] ⊗ F^∨ ⟶ G` intertwines the Frobenius of the stalks. -/
lemma tensorObj_evaluationPairing_stalkAt_frobenius (F G : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (d : ((F.tensorObj G hF).stalkAt s m hs).carrier) (x : ((F.dual hF).stalkAt s m hs).carrier) :
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

/-- The pairing `(F ⊗ G)_s → Hom((F^∨)_s, G_s)` induced by the evaluation `[F^∨, G] ⊗ F^∨ ⟶ G`.
-/
noncomputable def tensorObjStalkAtPairing (F G : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    ((F.tensorObj G hF).stalkAt s m hs).carrier →ₗ[PadicAlgCl l]
      ((F.dual hF).stalkAt s m hs).carrier →ₗ[PadicAlgCl l] (G.stalkAt s m hs).carrier :=
  LinearMap.mk₂ (PadicAlgCl l)
    (fun d y ↦ Mod.evaluationPairing (stalkFunctor l s) (F.dual hF).obj.carrier G.obj.carrier d y)
    (fun d d' y ↦ LinearMap.congr_fun (map_add (Mod.evaluationPairing (stalkFunctor l s)
      (F.dual hF).obj.carrier G.obj.carrier) d d') y)
    (fun c d y ↦ LinearMap.congr_fun ((Mod.evaluationPairing (stalkFunctor l s)
      (F.dual hF).obj.carrier G.obj.carrier).map_smul (ULift.up c) d) y)
    (fun d y y' ↦ map_add (Mod.evaluationPairing (stalkFunctor l s)
      (F.dual hF).obj.carrier G.obj.carrier d) y y')
    (fun c d y ↦ (Mod.evaluationPairing (stalkFunctor l s)
      (F.dual hF).obj.carrier G.obj.carrier d).map_smul (ULift.up c) y)

lemma tensorObjStalkAtPairing_apply (F G : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (d : ((F.tensorObj G hF).stalkAt s m hs).carrier) (y : ((F.dual hF).stalkAt s m hs).carrier) :
    tensorObjStalkAtPairing s m hs F G hF d y =
      Mod.evaluationPairing (stalkFunctor l s) (F.dual hF).obj.carrier G.obj.carrier d y :=
  rfl

/-- The pairing `(F ⊗ G)_s → Hom((F^∨)_s, G_s)` is bijective
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing_ihom`). -/
theorem bijective_tensorObjStalkAtPairing (F G : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    Function.Bijective (tensorObjStalkAtPairing s m hs F G hF) := by
  have hb := hF.dual.bijective_evaluationPairing_ihom G.obj.carrier s
  refine ⟨fun d d' h ↦ hb.1 (LinearMap.ext fun y ↦ ?_), fun φ ↦ ?_⟩
  · have := LinearMap.congr_fun h y
    rwa [tensorObjStalkAtPairing_apply, tensorObjStalkAtPairing_apply] at this
  · obtain ⟨d, hd⟩ := hb.2
      { toFun y := φ y
        map_add' y y' := φ.map_add y y'
        map_smul' c y := φ.map_smul c.down y }
    refine ⟨d, LinearMap.ext fun y ↦ ?_⟩
    rw [tensorObjStalkAtPairing_apply, hd]
    rfl

/-- The pairing `(F ⊗ G)_s → Hom((F^∨)_s, G_s)` intertwines the Frobenius of the stalks. -/
lemma tensorObjStalkAtPairing_frobenius (F G : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (d : ((F.tensorObj G hF).stalkAt s m hs).carrier) (y : ((F.dual hF).stalkAt s m hs).carrier) :
    tensorObjStalkAtPairing s m hs F G hF
        (((F.tensorObj G hF).stalkAt s m hs).frobenius d)
        (((F.dual hF).stalkAt s m hs).frobenius y) =
      (G.stalkAt s m hs).frobenius (tensorObjStalkAtPairing s m hs F G hF d y) := by
  rw [tensorObjStalkAtPairing_apply, tensorObjStalkAtPairing_apply]
  exact tensorObj_evaluationPairing_stalkAt_frobenius s m hs F G hF d y

/-- The stalk of the tensor product `F ⊗ G = [F^∨, G]` of a lisse Weil sheaf `F` and a Weil
sheaf `G` at a geometric point is `Hom((F^∨)_s, G_s)`, with the Frobenius
`X ↦ F_G ∘ X ∘ F_{F^∨}⁻¹`: the pairing induced by the evaluation is perfect
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.bijective_evaluationPairing_ihom`) and compatible
with the Frobenius
(`AlgebraicGeometry.WeilSheaf.tensorObj_evaluationPairing_stalkAt_frobenius`). -/
noncomputable def stalkAtTensorObjHomEquiv (F G : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    ((F.tensorObj G hF).stalkAt s m hs).Equiv
      (((F.dual hF).stalkAt s m hs).hom (G.stalkAt s m hs)) :=
  WeilCoefficients.frobeniusEquivOfBilinear (tensorObjStalkAtPairing s m hs F G hF)
    (bijective_tensorObjStalkAtPairing s m hs F G hF)
    (tensorObjStalkAtPairing_frobenius s m hs F G hF)

/-- **The stalk of a tensor product is the tensor product of the stalks.** For a lisse Weil
sheaf `F` and a Weil sheaf `G`, the stalk of `F ⊗ G` at a geometric point is `F_s ⊗ G_s`, with
the tensor product of the Frobenii: it is `Hom((F^∨)_s, G_s)`
(`AlgebraicGeometry.WeilSheaf.stalkAtTensorObjHomEquiv`), `(F^∨)_s = (F_s)^∨`
(`AlgebraicGeometry.WeilSheaf.stalkAtDualEquiv`) and `Hom(V^∨, W) = V ⊗ W`
(`FrobeniusModule.homDualEquiv`). -/
noncomputable def stalkAtTensorObjEquiv (F G : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    ((F.tensorObj G hF).stalkAt s m hs).Equiv ((F.stalkAt s m hs).tensor (G.stalkAt s m hs)) :=
  (stalkAtTensorObjHomEquiv s m hs F G hF).tensorOfHomDual (stalkAtDualEquiv s m hs F hF)

/-- The stalks of the constant Weil sheaf `ℚ̄_ℓ` are nonzero: they are generated by the unit
section (`AlgebraicGeometry.ProEtale.isIso_unitSection`). -/
theorem nontrivial_stalkAt_adicConstant :
    Nontrivial ((adicConstant k₀ l X).stalkAt s m hs).carrier := by
  have : Nontrivial (𝟙_ (WeilCoefficients.{u} l)) :=
    inferInstanceAs (Nontrivial (ULift.{u + 1} (PadicAlgCl l)))
  exact @Equiv.nontrivial ((adicConstant k₀ l X).stalkAt s m hs).carrier _
    (asIso (ProEtale.unitSection l s)).toLinearEquiv.symm.toEquiv this

/-- The only eigenvalue of the local Frobenius of the constant Weil sheaf `ℚ̄_ℓ` is `1`. -/
theorem hasEigenvalue_stalkAt_adicConstant_iff {α : PadicAlgCl l} :
    ((adicConstant k₀ l X).stalkAt s m hs).frobeniusEnd.HasEigenvalue α ↔ α = 1 := by
  have hF : ((adicConstant k₀ l X).stalkAt s m hs).frobeniusEnd = 1 := by
    rw [FrobeniusModule.frobeniusEnd, adicConstant_stalkAt_frobenius]
    rfl
  rw [hF]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
    have h0 : (1 - α) • x = 0 := by
      rw [sub_smul, one_smul, ← hx.1, Module.End.one_apply, sub_self]
    exact (sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hx.2)).symm
  · rintro rfl
    have := nontrivial_stalkAt_adicConstant (k₀ := k₀) (l := l) s m hs
    obtain ⟨x, hx⟩ := exists_ne (0 : ((adicConstant k₀ l X).stalkAt s m hs).carrier)
    exact Module.End.hasEigenvalue_of_hasEigenvector (x := x)
      (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 (by simp), hx⟩)

end StalkAt

/-- The stalk of `F ⊗ G` at a closed point `x` is `F_x̄ ⊗ G_x̄`, with the local Frobenius
`F_x ⊗ G_x` (`FrobeniusModule.frobeniusEnd_tensor`). -/
noncomputable def stalkTensorObjEquiv (F G : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (x : X.finitePoints) :
    ((F.tensorObj G hF).stalk x).Equiv ((F.stalk x).tensor (G.stalk x)) :=
  stalkAtTensorObjEquiv _ _ _ F G hF

/-- If `a` is an eigenvalue of the local Frobenius of `F` at `x` and `b` one of `G`, then `a b`
is an eigenvalue of the local Frobenius of `F ⊗ G` at `x`. -/
theorem hasEigenvalue_stalk_tensorObj {F G : WeilSheaf k₀ l X} (hF : F.IsLisse)
    {x : X.finitePoints} {a b : PadicAlgCl l} (ha : (F.stalk x).frobeniusEnd.HasEigenvalue a)
    (hb : (G.stalk x).frobeniusEnd.HasEigenvalue b) :
    ((F.tensorObj G hF).stalk x).frobeniusEnd.HasEigenvalue (a * b) :=
  FrobeniusModule.hasEigenvalue_of_surjective
    (stalkTensorObjEquiv F G hF x).toLinearEquiv.toLinearMap
    (stalkTensorObjEquiv F G hF x).map_frobenius
    (stalkTensorObjEquiv F G hF x).toLinearEquiv.surjective
    (FrobeniusModule.hasEigenvalue_tensor_mul ha hb)

/-- Every eigenvalue of the local Frobenius of `F ⊗ G` at `x` is a product `a b` of an
eigenvalue `a` of that of `F` and an eigenvalue `b` of that of `G`. -/
theorem exists_of_hasEigenvalue_stalk_tensorObj {F G : WeilSheaf k₀ l X} (hF : F.IsLisse)
    {x : X.finitePoints} {μ : PadicAlgCl l}
    (h : ((F.tensorObj G hF).stalk x).frobeniusEnd.HasEigenvalue μ) :
    ∃ a b, (F.stalk x).frobeniusEnd.HasEigenvalue a ∧ (G.stalk x).frobeniusEnd.HasEigenvalue b ∧
      μ = a * b :=
  FrobeniusModule.exists_of_hasEigenvalue_tensor ((stalkTensorObjEquiv F G hF x).hasEigenvalue h)

/-- The residue cardinality `q_x` at a closed point is positive. -/
lemma residueCard_pos (x : X.finitePoints) :
    0 < (X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 :=
  pow_pos Nat.card_pos _

/-- Weights add under tensor products: if `F` (lisse) has weights at most `w` and `G` weights at
most `w'`, then `F ⊗ G` has weights at most `w + w'`. -/
theorem HasWeightsAtMost.tensorObj {ι : PadicAlgCl l →+* ℂ} {F G : WeilSheaf k₀ l X}
    (hF : F.IsLisse) {w w' : ℝ} (hFw : F.HasWeightsAtMost ι w) (hGw : G.HasWeightsAtMost ι w') :
    (F.tensorObj G hF).HasWeightsAtMost ι (w + w') := fun x ↦
  FrobeniusModule.HasWeightsAtMost.of_equiv (stalkTensorObjEquiv F G hF x)
    ((hFw x).tensor (residueCard_pos x) (hGw x))

/-- The tensor product of a lisse Weil sheaf punctually pure of weight `w` and a Weil sheaf
punctually pure of weight `w'` is punctually pure of weight `w + w'`. -/
theorem IsPunctuallyPureOfWeight.tensorObj {ι : PadicAlgCl l →+* ℂ} {F G : WeilSheaf k₀ l X}
    (hF : F.IsLisse) {w w' : ℝ} (hFw : F.IsPunctuallyPureOfWeight ι w)
    (hGw : G.IsPunctuallyPureOfWeight ι w') :
    (F.tensorObj G hF).IsPunctuallyPureOfWeight ι (w + w') := fun x ↦
  FrobeniusModule.IsPureOfWeight.of_equiv (stalkTensorObjEquiv F G hF x)
    ((hFw x).tensor (residueCard_pos x) (hGw x))

end WeilSheaf

end AlgebraicGeometry
