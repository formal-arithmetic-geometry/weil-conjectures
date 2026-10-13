/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Sheaf.AlgebraicGeometry.CompletionAffineSectionsCoordinates
import Sheaf.AlgebraicGeometry.AffineInternalHomEvaluationBijective
import Sheaf.AlgebraicGeometry.CoherentSheafHom
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import all Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Componentwise completed internal-Hom evaluation

Source: Stacks Project, Tag 0882, affine-local evaluation construction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

open scoped TensorProduct

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Two nested tensor inductions elaborate the sheaf scalar actions at each quotient.
/-- Construct completed evaluation and identify its individual quotient components.
This does not identify equality with an arbitrary compatible family of morphisms and
makes no assertion about an externally supplied map epsilon.

Source: Stacks Project, Tag 0882, affine argument, and Tag 087W, module/sections comparison.
(blueprint: lem-weil-pbc-completion-internal-hom-affine-componentwise).

Proof:
1. Coherence makes N, M and the sections Hs of internal Hom finite on U. The affine
   Hom-section evaluation bijection gives K : Hs ≃ Hom_A(N,M). The proved affine
   quotient-coordinate lemma identifies compatible H quotient sections with the
   completion of Hs. Compose with AdicCompletion.congr K to construct rho.
2. Construct E using the three finite tensor/completion equivalences, the tensor
   extension of ordinary linear maps, and conjugation between completed N and M.
   Completion-map naturality proves E(of(h)) = AdicCompletion.map J h.
3. Apply he on U to an ordinary internal-Hom section h and evaluate on an ordinary
   G section y. By the definitions of homObjMap and homObjEvalId this gives exactly
   quotient evaluation: e_n(class(h))(class(y)) = class(K(h)(y)).
4. The completion of finite N is generated over B by of(N). Tensor induction,
   using pN and pM's scalar formulas with representatives modulo J^(n+1), extends
   step 3 to arbitrary completed inputs x. A second tensor induction on completed Hs,
   using its canonical scalar formula and linearity of e_n and E, extends this
   equation to arbitrary completed Hom sections. The projections of the inverse
   limit representative of s are s_n, giving the displayed component formula.
5. Each quotient of coherent G is coherent, hence quasi-coherent. Apply the same
   affine Hom-section evaluation bijection to each quotient to obtain injectivity.
This uses no flat base-change comparison for Hom. -/
theorem completion_internal_hom_affine_componentwise {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F G : CoherentModules X)
    (e : ∀ n : ℕᵒᵖ,
      formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
        (R := X.toRingedSpace.sheaf) G.obj F.obj) ⟶
        SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) (formalModuleQuotient I (n.unop + 1) G.obj)
          (formalModuleQuotient I (n.unop + 1) F.obj))
    (he : ∀ n : ℕᵒᵖ,
        formalModuleQuotientπ I (n.unop + 1) (SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) G.obj F.obj) ≫
          e n ≫ SheafOfModules.homObjMap
            (R := X.toRingedSpace.sheaf) (formalModuleQuotientπ I (n.unop + 1) G.obj)
            (𝟙 (formalModuleQuotient I (n.unop + 1) F.obj)) =
        SheafOfModules.homObjMap
          (R := X.toRingedSpace.sheaf) (𝟙 G.obj) (formalModuleQuotientπ I (n.unop + 1) F.obj))
    (U : X.affineOpens)
    :
    let A := Γ(X, U.val)
    let B := AdicCompletion (I.ideal U) A
    let N := Γ(G.obj, U.val)
    let M := Γ(F.obj, U.val)
    ∀ (pN : ∀ n : ℕᵒᵖ, AdicCompletion (I.ideal U) N →ₗ[A]
        Γ(formalModuleQuotient I (n.unop + 1) G.obj, U.val))
      (pM : ∀ n : ℕᵒᵖ, AdicCompletion (I.ideal U) M →ₗ[A]
        Γ(formalModuleQuotient I (n.unop + 1) F.obj, U.val)),
      (∀ n x, pN n (AdicCompletion.of (I.ideal U) _ x) =
        (formalModuleQuotientπ I (n.unop + 1) G.obj).val.app (op U.val) x) →
      (∀ n x, pM n (AdicCompletion.of (I.ideal U) _ x) =
        (formalModuleQuotientπ I (n.unop + 1) F.obj).val.app (op U.val) x) →
      (∀ n (r : B) (a : A) (x : AdicCompletion (I.ideal U) N),
        AdicCompletion.evalₐ (I.ideal U) (n.unop + 1) r = Ideal.Quotient.mk _ a →
          pN n (r • x) = a • pN n x) →
      (∀ n (r : B) (a : A) (x : AdicCompletion (I.ideal U) M),
        AdicCompletion.evalₐ (I.ideal U) (n.unop + 1) r = Ideal.Quotient.mk _ a →
          pM n (r • x) = a • pM n x) →
    ∃ ρ : {s : ∀ n : ℕᵒᵖ,
          (formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
            (R := X.toRingedSpace.sheaf) G.obj F.obj)).val.obj (op U.val) //
          ∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
            ((formalCompletionSystem I (SheafOfModules.homObj
              (R := X.toRingedSpace.sheaf) G.obj F.obj)).map f).val.app (op U.val)
              (s a) = s b} ≃ AdicCompletion (I.ideal U) (N →ₗ[A] M),
    ∃ E : AdicCompletion (I.ideal U) (N →ₗ[A] M) →ₗ[B]
        (AdicCompletion (I.ideal U) N →ₗ[B] AdicCompletion (I.ideal U) M),
      (∀ h : N →ₗ[A] M, E (AdicCompletion.of (I.ideal U) _ h) =
        AdicCompletion.map (I.ideal U) h) ∧
      (∀ s n x,
        PresheafOfModules.homObjEvalId
          (formalModuleQuotient I (n.unop + 1) G.obj).val
          (formalModuleQuotient I (n.unop + 1) F.obj).val U.val
          ((e n).val.app (op U.val) (s.val n)) (pN n x) = pM n (E (ρ s) x)) ∧
      (∀ n : ℕᵒᵖ, Function.Injective (PresheafOfModules.homObjEvalId
        (formalModuleQuotient I (n.unop + 1) G.obj).val
        (formalModuleQuotient I (n.unop + 1) F.obj).val U.val)) := by
  classical
  let A := Γ(X, U.val)
  let J := I.ideal U
  let B := AdicCompletion J A
  let N := Γ(G.obj, U.val)
  let M := Γ(F.obj, U.val)
  let H := N →ₗ[A] M
  let Hobj := SheafOfModules.homObj (R := X.toRingedSpace.sheaf) G.obj F.obj
  let Hs := Γ(Hobj, U.val)
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
  have hGfinite := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X G.obj).mp G.property
  have : G.obj.IsQuasicoherent := hGfinite.1
  have : G.obj.IsFiniteType := hGfinite.2
  have : Module.Finite A N := Scheme.Modules.finite_sections_of_finiteType G.obj U.property
  have hFfinite := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X F.obj).mp F.property
  have : F.obj.IsQuasicoherent := hFfinite.1
  have : F.obj.IsFiniteType := hFfinite.2
  have : Module.Finite A M := Scheme.Modules.finite_sections_of_finiteType F.obj U.property
  have : Module.Finite A H := inferInstance
  have hH := Scheme.Modules.isCoherent_homObj X F.obj G.obj F.property G.property
  have hHfinite := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X Hobj).mp hH
  have : Hobj.IsQuasicoherent := hHfinite.1
  have : Hobj.IsFiniteType := hHfinite.2
  have : Module.Finite A Hs := Scheme.Modules.finite_sections_of_finiteType Hobj U.property
  let K : Hs ≃ₗ[A] H := LinearEquiv.ofBijective
    (PresheafOfModules.homObjEvalId G.obj.val F.obj.val U.val)
    (affine_internalHom_evaluation_bijective G.obj F.obj U.val U.property)
  let cH := AdicCompletion.ofTensorProductEquivOfFiniteNoetherian J H
  let cN := AdicCompletion.ofTensorProductEquivOfFiniteNoetherian J N
  let cM := AdicCompletion.ofTensorProductEquivOfFiniteNoetherian J M
  let T := B ⊗[A] N →ₗ[B] B ⊗[A] M
  let β : B ⊗[A] H →ₗ[B] T := TensorProduct.AlgebraTensorModule.lift
    { toFun := fun b ↦ LinearMap.lsmul B T b ∘ₗ LinearMap.baseChangeHom A B N M
      map_add' := by intro b b'; ext h; simp
      map_smul' := by
        intro b b'
        apply LinearMap.ext
        intro h
        change (b * b') • LinearMap.baseChangeHom A B N M h =
          b • (b' • LinearMap.baseChangeHom A B N M h)
        exact mul_smul _ _ _ }
  have hβ (h : H) : β (1 ⊗ₜ[A] h) = LinearMap.baseChangeHom A B N M h := by
    change (1 : B) • LinearMap.baseChangeHom A B N M h = _
    exact one_smul B _
  let C : T ≃ₗ[B] (AdicCompletion J N →ₗ[B] AdicCompletion J M) :=
    LinearEquiv.arrowCongr cN cM
  let E := C.toLinearMap ∘ₗ β ∘ₗ cH.symm.toLinearMap
  have hEof (h : H) : E (AdicCompletion.of J H h) = AdicCompletion.map J h := by
    change C (β (cH.symm (AdicCompletion.of J H h))) = AdicCompletion.map J h
    rw [AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of, hβ]
    apply C.symm.injective
    rw [LinearEquiv.symm_apply_apply]
    exact AdicCompletion.tensor_map_id_left_eq_map J h
  dsimp only
  intro pN pM hofN hofM hscalarN hscalarM
  obtain ⟨pH, hsurjH, hinjH, htransH, hofH, hscalarH, hlimH⟩ :=
    completion_affine_sections_coordinates I ⟨Hobj, hH⟩ U
  let r (x : AdicCompletion J Hs) :=
    (⟨fun n ↦ pH n x, fun a b f ↦ htransH a b f x⟩ :
      {s : ∀ n : ℕᵒᵖ, Γ(formalModuleQuotient I (n.unop + 1) Hobj, U.val) //
        ∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
          ((formalCompletionSystem I Hobj).map f).val.app (op U.val) (s a) = s b})
  have hr : Function.Bijective r := by
    constructor
    · intro x y h
      exact hinjH x y (fun n ↦ congrArg (fun s ↦ s.val n) h)
    · intro s
      obtain ⟨x, hx⟩ := hlimH s.val s.property
      exact ⟨x, Subtype.ext (funext hx)⟩
  let R := Equiv.ofBijective r hr
  let ρ := R.symm.trans (AdicCompletion.congr J K).toEquiv
  let κ (n : ℕᵒᵖ) :
      Γ(SheafOfModules.homObj (R := X.toRingedSpace.sheaf)
        (formalModuleQuotient I (n.unop + 1) G.obj)
        (formalModuleQuotient I (n.unop + 1) F.obj), U.val) →ₗ[A]
      (Γ(formalModuleQuotient I (n.unop + 1) G.obj, U.val) →ₗ[A]
        Γ(formalModuleQuotient I (n.unop + 1) F.obj, U.val)) :=
    PresheafOfModules.homObjEvalId
      (formalModuleQuotient I (n.unop + 1) G.obj).val
      (formalModuleQuotient I (n.unop + 1) F.obj).val U.val
  have hbase (n : ℕᵒᵖ) (h : Hs) (y : N) :
      κ n ((e n).val.app (op U.val)
        ((formalModuleQuotientπ I (n.unop + 1) Hobj).val.app (op U.val) h))
        ((formalModuleQuotientπ I (n.unop + 1) G.obj).val.app (op U.val) y) =
      (formalModuleQuotientπ I (n.unop + 1) F.obj).val.app (op U.val) (K h y) := by
    have h' := congrArg (fun k ↦
      PresheafOfModules.homObjEvalId G.obj.val
        (formalModuleQuotient I (n.unop + 1) F.obj).val U.val
        (k.val.app (op U.val) h) y) (he n)
    exact h'
  have hon (n : ℕᵒᵖ) (h : Hs) (x : AdicCompletion J N) :
      κ n ((e n).val.app (op U.val)
        ((formalModuleQuotientπ I (n.unop + 1) Hobj).val.app (op U.val) h)) (pN n x) =
      pM n (AdicCompletion.map J (K h) x) := by
    obtain ⟨z, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite J N x
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b y =>
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ J (n.unop + 1) b)
      rw [AdicCompletion.ofTensorProduct_tmul, hscalarN n b a _ ha.symm,
        map_smul, map_smul, hscalarM n b a _ ha.symm, AdicCompletion.map_of,
        hofN, hofM, hbase]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcomponent (z : AdicCompletion J Hs) (n : ℕᵒᵖ) (x : AdicCompletion J N) :
      κ n ((e n).val.app (op U.val) (pH n z)) (pN n x) =
        pM n (E (AdicCompletion.congr J K z) x) := by
    obtain ⟨w, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite J Hs z
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | tmul b h =>
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ J (n.unop + 1) b)
      rw [AdicCompletion.ofTensorProduct_tmul, hscalarH n b a _ ha.symm, hofH]
      simp only [map_smul, LinearMap.smul_apply]
      rw [hscalarM n b a _ ha.symm]
      simp only [AdicCompletion.congr_apply, AdicCompletion.map_of, hEof]
      rw [hon]
      rfl
    | add w z hw hz => simp only [map_add, LinearMap.add_apply, hw, hz]
  refine ⟨ρ, E, hEof, ?_, ?_⟩
  · intro s n x
    have hp : pH n (R.symm s) = s.val n :=
      congrArg (fun z ↦ z.val n) (R.apply_symm_apply s)
    change κ n ((e n).val.app (op U.val) (s.val n)) (pN n x) =
      pM n (E (AdicCompletion.congr J K (R.symm s)) x)
    rw [← hp]
    exact hcomponent (R.symm s) n x
  · intro n
    have hcoh := (formalCompletionSystem_coherent I G).1 n.unop
    have : (formalModuleQuotient I (n.unop + 1) G.obj).IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp hcoh).1
    exact (affine_internalHom_evaluation_bijective _ _ U.val U.property).1

end AlgebraicGeometry
