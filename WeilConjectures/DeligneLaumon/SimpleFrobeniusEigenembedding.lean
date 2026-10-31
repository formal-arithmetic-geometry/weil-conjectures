/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.BaseChangeField.Transport
import WeilConjectures.WeilSheaf.GeometricConstituent
import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! # An eigenembedding for a periodic simple geometric local system

Source: the multiplicity eigenline in paragraphs 1--2 of
`lem-zl-geometric-constituents-any-base.proof.md`.
(blueprint: lem-zl-simple-frobenius-eigenembedding).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.WeilSheaf
open ProEtale

section ScalarHelpers

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}

private noncomputable instance homSMul (M N : AdicSheaf l Y) :
    SMul (ULift.{u + 1} (PadicAlgCl l)) (M ⟶ N) :=
  ⟨fun c f ↦ AdicSheaf.smul c M ≫ f⟩

private theorem hom_smul {M N : AdicSheaf l Y}
    (c : ULift.{u + 1} (PadicAlgCl l)) (f : M ⟶ N) :
    (c • f).hom = c • f.hom := by
  change (AdicSheaf.smul c M ≫ f).hom = _
  simp

private noncomputable instance homModule (M N : AdicSheaf l Y) :
    Module (ULift.{u + 1} (PadicAlgCl l)) (M ⟶ N) :=
  Function.Injective.module (ULift.{u + 1} (PadicAlgCl l))
    { toFun := fun f ↦ f.hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
    (fun _ _ h ↦ Mod.hom_ext _ _ h) hom_smul

private noncomputable instance adicLinear :
    Linear (ULift.{u + 1} (PadicAlgCl l)) (AdicSheaf l Y) where
  smul_comp _ _ _ c f g := Mod.hom_ext _ _ (by simp [hom_smul])
  comp_smul _ _ _ f c g := Mod.hom_ext _ _ (by simp [hom_smul])

private noncomputable instance lowerStarLinear {Z : Scheme.{u}} (g : Y ⟶ Z) :
    Functor.Linear (ULift.{u + 1} (PadicAlgCl l)) (g)_*ᵃ[l] := by
  apply (Functor.linear_iff _ _).2
  intro M c
  have hscalar (M : AdicSheaf l Y) : c • 𝟙 M = AdicSheaf.smul c M := by
    apply Mod.hom_ext
    simp [hom_smul]
  rw [hscalar, AdicSheaf.adicLowerStar_map_smul]
  apply Mod.hom_ext
  simp [hom_smul]

private noncomputable instance upperStarLinear {Z : Scheme.{u}} (g : Y ⟶ Z) :
    Functor.Linear (ULift.{u + 1} (PadicAlgCl l)) (g)^*ᵃ[l] :=
  (adicUpperStarLowerStarAdjunction l g).left_adjoint_linear

private noncomputable instance forgetLinear :
    Functor.Linear (ULift.{u + 1} (PadicAlgCl l)) (AdicSheaf.forget (l := l) Y) where
  map_smul f c := hom_smul c f

private theorem mono_of_simple_nonzero [IrreducibleSpace Y]
    {S Z : AdicSheaf l Y} (hS : IsIrreducibleAdicLocalSystem S)
    (hZ : IsAdicLisseSheaf Z) (f : S ⟶ Z) (hf : f ≠ 0) : Mono f := by
  have hK := (hS.1.kernel_cokernel_of_irreducibleSpace hZ f).1
  rcases hS.2.2 _ (kernel.ι f) inferInstance hK with hz | hi
  · exact Preadditive.mono_of_isZero_kernel f hz
  · exact (hf (by rw [← cancel_epi (kernel.ι f), kernel.condition, comp_zero])).elim

private theorem simple_stalk_map_injective [IrreducibleSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    {S Z : AdicSheaf l Y} (hS : IsIrreducibleAdicLocalSystem S)
    (hZ : IsAdicLisseSheaf Z) :
    Function.Injective ((geometricStalkFunctor l s).map : (S ⟶ Z) → _) := by
  have hzero (f : S ⟶ Z) (hf : (geometricStalkFunctor l s).map f = 0) : f = 0 := by
    by_contra h
    have := mono_of_simple_nonzero hS hZ f h
    have hz := IsZero.of_mono_eq_zero ((geometricStalkFunctor l s).map f) hf
    have hdim : Module.finrank (PadicAlgCl l)
        ((WeilCoefficients.toModuleCat l).obj ((geometricStalkFunctor l s).obj S)) = 0 := by
      have := ModuleCat.subsingleton_of_isZero ((WeilCoefficients.toModuleCat l).map_isZero hz)
      exact Module.finrank_zero_of_subsingleton
    exact hS.2.1 ((hS.1.isZero_iff_finrank_geometricStalkFunctor_eq_zero s).2 hdim)
  intro f g h
  apply sub_eq_zero.1
  apply hzero
  rw [Functor.map_sub, h, sub_self]

private theorem finite_stalk [IrreducibleSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    {Z : AdicSheaf l Y} (hZ : IsAdicLisseSheaf Z) :
    FiniteDimensional (ULift.{u + 1} (PadicAlgCl l)) ((geometricStalkFunctor l s).obj Z) := by
  let K := ULift.{u + 1} (PadicAlgCl l)
  let M := (geometricStalkFunctor l s).obj Z
  let inst : Module (PadicAlgCl l) M :=
    ((WeilCoefficients.toModuleCat l).obj M).isModule
  have : Module.Finite (PadicAlgCl l) M := hZ.finiteDimensional_geometricStalkFunctor s
  have : IsScalarTower (PadicAlgCl l) K M :=
    ⟨fun a b x ↦ by change (ULift.up a * b) • x = ULift.up a • (b • x); exact mul_smul _ _ _⟩
  exact Module.Finite.of_restrictScalars_finite (PadicAlgCl l) K M

end ScalarHelpers

/-- A periodic simple local system that embeds in a lisse Weil sheaf admits an
embedding whose image is stable under that power of Frobenius.

Source: blueprint `sec-deligne-laumon-general/sk-lem-wgen-geometric-constituents/`
`lem-zl-geometric-constituents-any-base.proof.md`, paragraphs 1--2, the eigenline
of the multiplicity operator.
(blueprint: lem-zl-simple-frobenius-eigenembedding).

Proof: Put Q = (Fr^d)^* and choose the supplied isomorphism e : Q(S) = S.
The nonzero vector space Hom(S,V) is finite dimensional over Qlbar: evaluation
at a geometric point is injective on morphisms of lisse sheaves, and embeds it
in Hom(S_s,V_s). The operator j |-> e^{-1} ; Q(j) ; phi_d is an invertible
Qlbar-linear operator on this space. Choose a nonzero eigenvector j' with
eigenvalue lambda. Invertibility gives lambda != 0. The morphism j' is mono:
its kernel is lisse and simplicity of S makes the kernel zero, since j' != 0.
The isomorphism e' = lambda e then satisfies the asserted equation. No
irreducibility or semisimplicity of V is used. For d=0 the original embedding
and the canonical identity-pullback isomorphism already suffice. -/
theorem exists_simple_frobenius_eigenembedding
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    [IrreducibleSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    (V : WeilSheaf k₀ l X) (hV : V.IsLisse)
    (S : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (hS : IsIrreducibleAdicLocalSystem S) (j : S ⟶ V.obj.carrier) [Mono j]
    (d : ℕ) (e : (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X d).obj S ≅ S) :
    ∃ (j' : S ⟶ V.obj.carrier), Mono j' ∧
      ∃ e' : (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X d).obj S ≅ S,
        e'.hom ≫ j' =
          (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X d).map j' ≫
            (V.obj.frobeniusPowIso d).hom := by
  classical
  let K := ULift.{u + 1} (PadicAlgCl l)
  have : IsAlgClosed K := by
    refine ⟨fun p ↦ ?_⟩
    let e : K ≃+* PadicAlgCl l := ULift.ringEquiv
    have h := (IsAlgClosed.splits (p.map e.toRingHom)).map e.symm.toRingHom
    simpa only [Polynomial.map_map, RingEquiv.symm_toRingHom_comp_toRingHom,
      Polynomial.map_id] using h
  let Q := ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X d
  have : Functor.Linear K Q := by
    dsimp [Q, K, ProEtaleWeilSheaf.frobeniusPowPullback]
    infer_instance
  let H := S ⟶ V.obj.carrier
  have hj0 : j ≠ 0 := fun h ↦ hS.2.1 (IsZero.of_mono_eq_zero j h)
  have : Nontrivial H := nontrivial_of_ne j 0 hj0
  let Y := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  let s : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
        Y.fromSpecResidueField y
  let ω := geometricStalkFunctor l s
  have : Functor.Linear K ω := by dsimp [ω, geometricStalkFunctor, K]; infer_instance
  have : FiniteDimensional K (ω.obj S) := finite_stalk s hS.1
  have : FiniteDimensional K (ω.obj V.obj.carrier) := finite_stalk s hV
  have : FiniteDimensional K (ω.obj S ⟶ ω.obj V.obj.carrier) :=
    Module.Finite.equiv
      (ModuleCat.homLinearEquiv (R := K) (S := K)
        (M := ω.obj S) (N := ω.obj V.obj.carrier)).symm
  have : FiniteDimensional K H :=
    FiniteDimensional.of_injective (ω.mapLinearMap K) (simple_stalk_map_injective s hS hV)
  let B : Module.End K H :=
    (Linear.leftComp K V.obj.carrier e.inv).comp
      ((Linear.rightComp K (Q.obj S) (V.obj.frobeniusPowIso d).hom).comp
        (Q.mapLinearMap K))
  have hB : Function.Injective B := by
    intro f g h
    apply Q.map_injective
    apply (cancel_mono (V.obj.frobeniusPowIso d).hom).1
    apply (cancel_epi e.inv).1
    exact h
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue B
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hc0 : c ≠ 0 := by
    intro hc0
    have hBv : B v = B 0 := by rw [hv.apply_eq_smul, hc0, zero_smul, map_zero]
    exact hv.2 (hB hBv)
  have hvmono : Mono v := mono_of_simple_nonzero hS hV v hv.2
  let e' : Q.obj S ≅ S :=
    { hom := c • e.hom
      inv := c⁻¹ • e.inv
      hom_inv_id := by
        simp only [Linear.smul_comp, Linear.comp_smul, Iso.hom_inv_id,
          ← mul_smul, inv_mul_cancel₀ hc0, one_smul]
      inv_hom_id := by
        simp only [Linear.smul_comp, Linear.comp_smul, Iso.inv_hom_id,
          ← mul_smul, mul_inv_cancel₀ hc0, one_smul] }
  refine ⟨v, hvmono, e', ?_⟩
  change (c • e.hom) ≫ v = Q.map v ≫ (V.obj.frobeniusPowIso d).hom
  have heq : e.inv ≫ Q.map v ≫ (V.obj.frobeniusPowIso d).hom = c • v :=
    hv.apply_eq_smul
  have h := congrArg (fun f ↦ e.hom ≫ f) heq
  calc
    (c • e.hom) ≫ v = c • (e.hom ≫ v) := Linear.smul_comp _ _ _ _ _ _
    _ = e.hom ≫ (c • v) := (Linear.comp_smul _ _ _ _ _ _).symm
    _ = Q.map v ≫ (V.obj.frobeniusPowIso d).hom := by
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h.symm

end AlgebraicGeometry.WeilSheaf
