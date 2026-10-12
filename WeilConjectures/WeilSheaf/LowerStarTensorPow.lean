/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.TensorPowSection
public import WeilConjectures.WeilSheaf.LowerStarPairing
public import WeilConjectures.WeilSheaf.TensorObjPairing
public import WeilConjectures.WeilSheaf.TensorPower

/-!
# Powers of eigenvalues on stalks of pushforwards of tensor powers

Let `φ : X ⟶ Y` be a morphism of `k₀`-schemes, `F` a lisse Weil sheaf on `X` and `s` a geometric
point of `Ȳ` fixed by a power of the Frobenius. If `α` is an eigenvalue of the local Frobenius
on the stalk `(φ_* F)_s`, then `α ^ k` is an eigenvalue of the local Frobenius on
`(φ_* (F^{⊗ k}))_s` (`AlgebraicGeometry.WeilSheaf.hasEigenvalue_stalkAt_lowerStar_tensorPow`).

Write `v` for an eigenvector. The pairings `F ⊗ F^{⊗ k} ⟶ F^{⊗ (k + 1)}`
(`CategoryTheory.Mod.toIhomDual`) are compatible with the Weil structures
(`AlgebraicGeometry.WeilSheaf.toIhomDual_str`), hence so are their pushforwards
`φ_* F ⊗ φ_* F^{⊗ k} ⟶ φ_* F^{⊗ (k + 1)}` (`AlgebraicGeometry.WeilSheaf.lowerStar_pairing_str`),
and the induced pairings of stalks intertwine the local Frobenius
(`AlgebraicGeometry.WeilSheaf.stalkAt_pairing_frobenius`). So `w₀ = 1`,
`w_{k + 1} = ⟨v, w_k⟩` is an eigenvector with eigenvalue `α ^ k` as soon as it is nonzero.

Nonvanishing: `v` is the germ of a section `σ` of `F` over `V ×_Ȳ X̄` for a pro-étale
neighbourhood `V` of `s` (`AlgebraicGeometry.ProEtale.exists_germ_eq`), and `w_k` is the germ of
the tensor power `σ^{⊗ k}` (`AlgebraicGeometry.WeilSheaf.tensorPowSection`). If `w_k = 0`, then
`σ^{⊗ k}` vanishes on a smaller neighbourhood
(`AlgebraicGeometry.ProEtale.exists_map_eq_zero_of_germ_eq_zero`), hence so does `σ`, `F` being
lisse (`AlgebraicGeometry.WeilSheaf.eq_zero_of_tensorPowSection_eq_zero`), and `v = 0`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Opposite

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section StalkFrobenius

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s)

/-- A pairing of underlying sheaves of Weil sheaves compatible with the Weil structures induces a
pairing of stalks compatible with the local Frobenius. -/
lemma stalkAt_pairing_frobenius (P Q R : WeilSheaf k₀ l X)
    (e : P.obj.carrier.X ⊗ Q.obj.carrier.X ⟶ R.obj.carrier.X)
    (h : (P.obj.str.hom.hom ⊗ₘ Q.obj.str.hom.hom) ≫ e =
      μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l]
          P.obj.carrier.X Q.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map e ≫
          R.obj.str.hom.hom)
    (p : (P.stalkAt s m hs).carrier) (q : (Q.stalkAt s m hs).carrier) :
    ((stalkSheafFunctor k₀ l X s).map e).hom ((μ (stalkSheafFunctor k₀ l X s) _ _).hom
        ((P.stalkAt s m hs).frobenius p ⊗ₜ (Q.stalkAt s m hs).frobenius q)) =
      (R.stalkAt s m hs).frobenius (((stalkSheafFunctor k₀ l X s).map e).hom
        ((μ (stalkSheafFunctor k₀ l X s) _ _).hom (p ⊗ₜ q))) := by
  have h' := stalkPairing_frobenius s m hs _ _ _ _ (frobeniusPowIso_tensor P Q R e h m)
  rw [stalkAt_frobenius_eq_stalkFrobeniusIso, stalkAt_frobenius_eq_stalkFrobeniusIso,
    stalkAt_frobenius_eq_stalkFrobeniusIso]
  exact ModuleCat.tmul_eq_of_tensorHom_comp h' p q

/-- A unit of the underlying sheaf of a Weil sheaf compatible with the Weil structure induces an
element of the stalk fixed by the local Frobenius. -/
lemma stalkAt_unit_frobenius (R : WeilSheaf k₀ l X) (η : 𝟙_ _ ⟶ R.obj.carrier.X)
    (h : ε ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l] ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map η ≫
        R.obj.str.hom.hom = η) :
    (R.stalkAt s m hs).frobenius (((stalkSheafFunctor k₀ l X s).map η).hom
        ((ε (stalkSheafFunctor k₀ l X s)).hom (1 : ULift.{u + 1} (PadicAlgCl l)))) =
      ((stalkSheafFunctor k₀ l X s).map η).hom
        ((ε (stalkSheafFunctor k₀ l X s)).hom (1 : ULift.{u + 1} (PadicAlgCl l))) := by
  have h' := stalkUnit_frobenius s m hs _ _ (frobeniusPowIso_unit R η h m)
  rw [stalkAt_frobenius_eq_stalkFrobeniusIso]
  exact congrArg (fun f ↦ f.hom (1 : ULift.{u + 1} (PadicAlgCl l))) h'

end StalkFrobenius

section TensorPowSection

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The tensor powers `σ^{⊗ 0} = 1`, `σ^{⊗ (k + 1)} = σ ⊗ σ^{⊗ k}` of a section `σ` of a lisse
Weil sheaf `F`, sections of the tensor powers `F^{⊗ k}`. -/
noncomputable def tensorPowSection (F : WeilSheaf k₀ l X) (hF : F.IsLisse)
    {W : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber.ProEt}
    (σ : ToType (F.obj.carrier.X.obj.obj (op W))) :
    (k : ℕ) → ToType ((F.tensorPow hF k).obj.carrier.X.obj.obj (op W))
  | 0 => adicUnitSection W
  | k + 1 => toIhomDualSection σ (tensorPowSection F hF σ k)

/-- Tensor powers of sections commute with restriction. -/
lemma map_tensorPowSection (F : WeilSheaf k₀ l X) (hF : F.IsLisse)
    {W W' : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber.ProEt} (f : W' ⟶ W)
    (σ : ToType (F.obj.carrier.X.obj.obj (op W))) :
    ∀ k : ℕ, (F.tensorPow hF k).obj.carrier.X.obj.map f.op (tensorPowSection F hF σ k) =
      tensorPowSection F hF (F.obj.carrier.X.obj.map f.op σ) k
  | 0 => map_adicUnitSection f
  | k + 1 => by
    refine (map_toIhomDualSection f σ (tensorPowSection F hF σ k)).trans ?_
    rw [map_tensorPowSection F hF f σ k]
    rfl

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- The germs of the tensor powers of a section of a lisse Weil sheaf with nonzero germ are
nonzero. -/
lemma germ_tensorPowSection_ne_zero (F : WeilSheaf k₀ l X) (hF : F.IsLisse)
    (s : Spec (.of K) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    {W : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber.ProEt}
    (t : Scheme.ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ s).obj W)
    (σ : ToType (F.obj.carrier.X.obj.obj (op W)))
    (hσ : germ (WeilCoefficients.{u} l) s F.obj.carrier.X t σ ≠ 0) :
    ∀ k : ℕ, germ (WeilCoefficients.{u} l) s (F.tensorPow hF k).obj.carrier.X t
      (tensorPowSection F hF σ k) ≠ 0
  | 0 => by
    have := germ_adicUnitSection (l := l) s t
    exact this ▸ unitSection_one_ne_zero s
  | k + 1 => hF.germ_toIhomDualSection_ne_zero s t hσ
      (germ_tensorPowSection_ne_zero F hF s t σ hσ k)

omit [IsAlgClosed K] in
/-- **Tensor powers of nonzero sections of lisse Weil sheaves are nonzero.** -/
theorem eq_zero_of_tensorPowSection_eq_zero (F : WeilSheaf k₀ l X) (hF : F.IsLisse)
    {W : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber.ProEt}
    (σ : ToType (F.obj.carrier.X.obj.obj (op W))) (k : ℕ)
    (h : tensorPowSection F hF σ k = 0) : σ = 0 := by
  refine ProEtale.IsAdicLisseSheaf.eq_zero_of_germ_eq_zero hF σ fun K _ _ w t ↦ ?_
  by_contra hσ
  exact germ_tensorPowSection_ne_zero F hF (w ≫ W.hom) t σ hσ k (by rw [h, map_zero])

end TensorPowSection

section Main

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
  [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  {V : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.ProEt}
  (t : Scheme.ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ s).obj V)

/-- The germ of the unit section of `φ_* ℚ̄_ℓ` is the image of `1` under the unit of the
pushforward. -/
lemma germ_lowerStar_adicUnitSection :
    germ (WeilCoefficients.{u} l) s
        ((Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].obj
          (adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) t
        (adicUnitSection _) =
      ((stalkSheafFunctor k₀ l Y s).map
        (ε (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[WeilCoefficients.{u} l] ≫
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].map
            (MonObj.one (X := adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)))).hom
        ((ε (stalkSheafFunctor k₀ l Y s)).hom (1 : ULift.{u + 1} (PadicAlgCl l))) := by
  have e : (ε (sheafToPresheaf (Scheme.ProEt.topology _) (WeilCoefficients.{u} l))).app
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).obj V)) ≫
      (MonObj.one (X := adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)).hom.app
        _ ≫ germ (WeilCoefficients.{u} l) s
          ((Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].obj
            (adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) t =
      ε (stalkSheafFunctor k₀ l Y s) ≫ (stalkSheafFunctor k₀ l Y s).map
        (ε (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[WeilCoefficients.{u} l] ≫
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].map
            (MonObj.one (X := adicConstantSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))) := by
    rw [germ_unit (l := l) t, Category.assoc, ← germ_naturality]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
    rw [ε_sheafToPresheaf_app_comp_ε_lowerStar_app_assoc]
    rfl
  exact congrArg (fun f ↦ f.hom (1 : ULift.{u + 1} (PadicAlgCl l))) e

/-- The germ of `σ ⊗ τ` at `s`, for sections of `φ_* F` and `φ_* N` over `V`, is the pairing of the
germs under `φ_* F ⊗ φ_* N ⟶ φ_* (F ⊗ N) ⟶ φ_* 𝓗om(F^∨, N)`. -/
lemma germ_lowerStar_toIhomDualSection (F N : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (σ : ToType (((Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].obj F.X).obj.obj (op V)))
    (τ : ToType (((Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].obj N.X).obj.obj (op V))) :
    germ (WeilCoefficients.{u} l) s
        ((Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].obj
          ((Mod.ihom ((Mod.ihom F).obj (AdicSheaf.unit l _))).obj N).X) t
        (toIhomDualSection (F := F) (N := N) σ τ) =
      ((stalkSheafFunctor k₀ l Y s).map
        (μ (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[WeilCoefficients.{u} l] F.X N.X ≫
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].map (Mod.toIhomDual F N))).hom
        ((μ (stalkSheafFunctor k₀ l Y s) _ _).hom
          (germ (WeilCoefficients.{u} l) s _ t σ ⊗ₜ germ (WeilCoefficients.{u} l) s _ t τ)) := by
  have e : (germ (WeilCoefficients.{u} l) s
        ((Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].obj F.X) t ⊗ₘ
      germ (WeilCoefficients.{u} l) s
        ((Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].obj N.X) t) ≫
      μ (stalkSheafFunctor k₀ l Y s) _ _ ≫ (stalkSheafFunctor k₀ l Y s).map
        (μ (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[WeilCoefficients.{u} l] F.X N.X ≫
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].map (Mod.toIhomDual F N)) =
      (μ (sheafToPresheaf (Scheme.ProEt.topology _) (WeilCoefficients.{u} l)) F.X N.X).app
          (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤
            (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).obj V)) ≫
        (Mod.toIhomDual F N).hom.app _ ≫ germ (WeilCoefficients.{u} l) s
          ((Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].obj
            ((Mod.ihom ((Mod.ihom F).obj (AdicSheaf.unit l _))).obj N).X) t := by
    rw [germ_tensor_assoc, ← germ_naturality]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
    rw [μ_sheafToPresheaf_app_comp_μ_lowerStar_app_assoc]
    rfl
  exact (congrArg (fun f ↦ f.hom (σ ⊗ₜ τ)) e).symm

/-- **Powers of eigenvalues on stalks of pushforwards of tensor powers.** If `α` is an eigenvalue
of the local Frobenius on the stalk `(φ_* F)_s` of the pushforward of a lisse Weil sheaf `F`, then
`α ^ k` is an eigenvalue of the local Frobenius on `(φ_* (F^{⊗ k}))_s`. -/
theorem hasEigenvalue_stalkAt_lowerStar_tensorPow {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (m : ℕ) (hs : s ≫ ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s) {α : PadicAlgCl l}
    (hα : (((lowerStar φ).obj F).stalkAt s m hs).frobeniusEnd.HasEigenvalue α) (k : ℕ) :
    (((lowerStar φ).obj (F.tensorPow hF k)).stalkAt s m hs).frobeniusEnd.HasEigenvalue
      (α ^ k) := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hv
  obtain ⟨V, t, σ, hσv⟩ := exists_germ_eq s
    ((Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[WeilCoefficients.{u} l].obj
      F.obj.carrier.X) v
  -- the candidate eigenvectors: the germs of the tensor powers of `σ`
  let w (k : ℕ) : (((lowerStar φ).obj (F.tensorPow hF k)).stalkAt s m hs).carrier :=
    germ (WeilCoefficients.{u} l) s
      ((Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*[_].obj
        (F.tensorPow hF k).obj.carrier.X) t (tensorPowSection F hF σ k)
  have hfrob (k : ℕ) : (((lowerStar φ).obj (F.tensorPow hF k)).stalkAt s m hs).frobenius (w k) =
      (α ^ k) • w k := by
    induction k with
    | zero =>
      have h := stalkAt_unit_frobenius s m hs ((lowerStar φ).obj (F.tensorPow hF 0)) _
        (lowerStar_unit_str φ (adicConstant k₀ l X) _ adicConstant_unit_str)
      have hw : w 0 = _ := germ_lowerStar_adicUnitSection φ s t
      rw [hw, pow_zero, one_smul]
      exact h
    | succ k ih =>
      have h := stalkAt_pairing_frobenius s m hs ((lowerStar φ).obj F)
        ((lowerStar φ).obj (F.tensorPow hF k)) ((lowerStar φ).obj (F.tensorPow hF (k + 1))) _
        (lowerStar_pairing_str φ F (F.tensorPow hF k) (F.tensorPow hF (k + 1)) _
          (toIhomDual_str F (F.tensorPow hF k) hF)) v (w k)
      have hw : w (k + 1) = _ := germ_lowerStar_toIhomDualSection φ s t F.obj.carrier
        (F.tensorPow hF k).obj.carrier σ (tensorPowSection F hF σ k)
      have hv₁ : (((lowerStar φ).obj F).stalkAt s m hs).frobenius v = α • v := hv.1
      rw [hw, ← hσv, ← h]
      erw [hσv, hv₁, ih]
      change _ = (ULift.up (α ^ (k + 1)) : ULift.{u + 1} (PadicAlgCl l)) • _
      rw [← TensorProduct.smul_tmul_smul]
      erw [map_smul, map_smul]
      congr 1
      exact congrArg ULift.up (pow_succ' α k).symm
  have hne (k : ℕ) : w k ≠ 0 := by
    intro h
    obtain ⟨V', f, t', ht', hf⟩ := exists_map_eq_zero_of_germ_eq_zero s _ t _ h
    have h₁ : tensorPowSection F hF (F.obj.carrier.X.obj.map
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤
          (Scheme.Hom.geometricFiberMap φ (comp_over φ _))).map f).op σ) k = 0 :=
      (map_tensorPowSection F hF _ σ k).symm.trans hf
    have h₂ := eq_zero_of_tensorPowSection_eq_zero F hF _ k h₁
    apply hv.2
    rw [← hσv, ← map_germ f t t' ht']
    erw [ConcreteCategory.comp_apply, h₂, map_zero]
  exact Module.End.hasEigenvalue_of_hasEigenvector
    (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 (hfrob k), hne k⟩)

end Main

end AlgebraicGeometry.WeilSheaf
