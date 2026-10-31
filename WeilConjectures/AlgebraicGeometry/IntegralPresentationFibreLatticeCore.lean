/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Module.Lattice
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic

/-! Scalar-extension lattice core for the integral presentation. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.LisseQlbar

private theorem tensor_lattice
    {A K M V : Type*} [CommRing A] [Nontrivial A] [Field K] [Algebra A K] [FaithfulSMul A K]
    [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M]
    [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (t : (K ⊗[A] M) ≃ₗ[K] V) :
    ∃ N : Submodule A V,
      Nonempty (Module.Basis (Fin (Module.finrank K V)) A N) ∧
      Submodule.IsLattice K N ∧
      (∃ e : M ≃ₗ[A] N, ∀ z : M, (e z : V) = t (1 ⊗ₜ[A] z)) ∧
      (∃ q : (K ⊗[A] N) ≃ₗ[K] V,
        ∀ (b : K) (z : N), q (b ⊗ₜ[A] z) = b • (z : V)) := by
  classical
  let f : M →ₗ[A] V := t.toLinearMap.restrictScalars A ∘ₗ TensorProduct.mk A K M 1
  have hf : Function.Injective f :=
    t.injective.comp (Module.Flat.tensorProduct_mk_injective A M K)
  let N := f.range
  let e : M ≃ₗ[A] N := LinearEquiv.ofInjective f hf
  let b := Module.finBasis A M
  let bV := (b.baseChange K).map t
  have hbV (i) : bV i = f (b i) := by simp [bV, f]
  have hspan : Submodule.span K (N : Set V) = ⊤ := by
    apply top_unique
    rw [← bV.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, (hbV i).symm⟩
  have hr : Module.finrank K V = Module.finrank A M := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis bV
  have he (z : M) : (e z : V) = t (1 ⊗ₜ[A] z) := rfl
  have hfg : N.FG := by
    simpa only [Submodule.map_top] using (Module.Finite.fg_top (R := A) (M := M)).map f
  refine ⟨N, ⟨(b.map e).reindex (finCongr hr.symm)⟩, ⟨hfg, hspan⟩, ⟨e, he⟩, ?_⟩
  refine ⟨(TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e.symm).trans t,
    ?_⟩
  intro a z
  change t (a ⊗ₜ[A] e.symm z) = a • (z : V)
  calc
    _ = t (a • (1 ⊗ₜ[A] e.symm z)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = a • t (1 ⊗ₜ[A] e.symm z) := t.map_smul a _
    _ = a • (z : V) := by rw [← he, e.apply_symm_apply]

namespace AlgebraicGeometry.ProEtale.RealIntegral
section FibreHelpers
variable {Λ B D : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj B] [IsCommMonObj B]
  [MonObj D] [IsCommMonObj D]
  {X : Scheme.{u}} {Ω : Type u} [Field Ω]
  (x : Spec (.of Ω) ⟶ X)
private theorem fibreMap_comp
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj D X))
    (f : L.X ⟶ M.X) (g : M.X ⟶ N.X) :
    fibreMap Λ B x L M f ≫ fibreMap B D x M N g =
      fibreMap Λ D x L N (f ≫ g) := by
  unfold fibreMap
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
private theorem comparison_one
    {R : Type} [CommRing R] (sR : R → condensedScalarRing Λ)
    {G : Type v} [Group G]
    {P : ObjectProperty
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))}
    {Q : ObjectProperty (Rep.{u + 1} R G)}
    (e : FibreEquivalence Λ R sR x G P Q) (L : P.FullSubcategory)
    (z : (fibre Λ x).obj L.obj) :
    CondensedRing.affineScalarSection Λ (Spec (.of Ω)) (sR 1) • z = z := by
  have h := e.linear L 1 (e.comparison.inv.app L z)
  simpa only [id_eq, one_smul, ← ConcreteCategory.comp_apply, Iso.inv_hom_id_app,
    ConcreteCategory.id_apply] using h.symm

end FibreHelpers

variable (l : ℕ) [Fact l.Prime]
variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (x : Spec (.of Ω) ⟶ X) (G : ProfiniteGrp.{u})
  [∀ P, MulAction G ((FiniteEtale.fiber x).obj P)]
  (c : Correspondence l x G)

set_option maxHeartbeats 0 in
-- Comparing scalar adjunctions expands large internal-module types.
private theorem factor_presentation
    (F : (integralClosure l X).FullSubcategory)
    (E : PadicAlgCl.FiniteIntermediateField l)
    (L : ObjectProperty.FullSubcategory
      (CondensedRing.LocallyFree (condensedRingObj (integerRing l E) X)))
    (i : L.obj ⟶ (Mod.comap (coefficientMap (integerInclusion l E ≫
      Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)).obj F.obj)
    (hi : IsIso (((Mod.extendRestrictAdjunction (coefficientMap
      (integerInclusion l E ≫ Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)).homEquiv
      L.obj F.obj).symm i)) :
    let a := coefficientMap (integerInclusion l E) X
    let b := coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X
    let U : (integralField l E X).FullSubcategory :=
      ⟨(Mod.extendScalars a).obj L.obj, (c.localization E).closed L⟩
    ∃ k : U.obj ⟶ (Mod.comap b).obj F.obj,
      IsIso (((Mod.extendRestrictAdjunction b).homEquiv U.obj F.obj).symm k) ∧
      (Mod.extendUnit a L.obj).hom ≫ k.hom = i.hom := by
  classical
  dsimp only
  let a := coefficientMap (integerInclusion l E) X
  let b := coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X
  let d := coefficientMap
    (integerInclusion l E ≫ Profinite.padicSubfieldRingObjToPadicAlgCl l E) X
  let A := Mod.extendRestrictAdjunction a
  let B := Mod.extendRestrictAdjunction b
  let D := Mod.extendRestrictAdjunction d
  let δ : Mod.comap b ⋙ Mod.comap a ≅ Mod.comap d :=
    (Mod.comapComp a b).symm ≪≫
      Mod.comapCongr (coefficientMap_comp (integerInclusion l E)
        (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X).symm
  let AB := (A.comp B).ofNatIsoRight δ
  let e := D.leftAdjointUniq AB
  let J := (D.homEquiv L.obj F.obj).symm i
  have : IsIso J := hi
  let J' := e.inv.app L.obj ≫ J
  have : IsIso J' := inferInstance
  let k := B.homEquiv _ _ J'
  refine ⟨k, ?_, ?_⟩
  · change IsIso ((B.homEquiv _ _).symm (B.homEquiv _ _ J'))
    simpa only [Equiv.symm_apply_apply] using (inferInstance : IsIso J')
  · have hx : AB.homEquiv _ _ J' = i := by
      calc
        _ = D.homEquiv _ _ (e.hom.app L.obj ≫ J') := by
          simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
          rw [show D.unit.app L.obj ≫ (Mod.comap d).map (e.hom.app L.obj) =
            AB.unit.app L.obj from Adjunction.unit_leftAdjointUniq_hom_app D AB L.obj]
        _ = i := by simp [J', J]
    have hx' := congrArg Mod.Hom.hom hx
    change (A.homEquiv _ _ k ≫ δ.hom.app F.obj).hom = i.hom at hx'
    simp only [Mod.comp_hom', δ, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Mod.comapComp_inv_app_hom, Mod.comapCongr_hom_app_hom] at hx'
    exact hx'


set_option maxHeartbeats 0 in
-- The normalized fibre comparisons have large internal-module types.
/-- The scalar-extension and equivariant lattice clauses of the normalized fibre theorem.
Source: latest blueprint, sec-purity-real-sheaves/sk-p-real-integral; this is the
first (comparison and lattice) paragraph of `p-real-integral.proof.md`.
(blueprint: lem-real-integral-presentation-fibre-lattice-core).

Proof in words:
1. The integral equivalence's image condition makes M finite free over A, and the
algebraic equivalence's image condition makes V finite dimensional. Extend L to the
finite field E. The localization comparison gives E tensor_A M as its rational fibre.
Use composition of the scalar adjunctions to factor the supplied presentation through
this rational sheaf; its E-to-Qlbar adjunct is an isomorphism. The algebraic-extension
comparison and tensor associativity therefore give t : Qlbar tensor_A M = V. The
pure-tensor formulas in both comparisons, their linearity, and cancellation of the
intermediate fibre comparisons show t(b tensor m) = b times j(m). Their equivariance
formulas show j intertwines the actions.
2. Define the A-linear map phi(m) = t(1 tensor m) = j(m), and take N to be its range.
The map M to Qlbar tensor_A M is injective: choose a finite A-basis of M, after which
it is the coordinatewise injective inclusion A to Qlbar. Thus phi identifies M with N.
The transported basis makes N finitely generated, and surjectivity of t shows its
Qlbar-span is V. Base-changing this basis shows that its cardinality equals dim V;
reindex it by Fin(dim V). Transport t across M = N to obtain the tensor isomorphism
with the displayed pure-tensor formula. Equivariance gives stability, using g inverse
for the reverse inclusion. -/
theorem integralPresentation_fibre_lattice_core
    (F : (integralClosure l X).FullSubcategory)
    (E : PadicAlgCl.FiniteIntermediateField l)
    (L : ObjectProperty.FullSubcategory
      (CondensedRing.LocallyFree (condensedRingObj (integerRing l E) X)))
    (i : L.obj ⟶ (Mod.comap (coefficientMap (integerInclusion l E ≫
      Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)).obj F.obj)
    (_hi : Mono i)
    (_he : IsIso (((Mod.extendRestrictAdjunction (coefficientMap
      (integerInclusion l E ≫ Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)).homEquiv
      L.obj F.obj).symm i)) :
  let j := (c.integral E).comparison.hom.app L ≫
    fibreMap (integerRing l E) (Profinite.padicAlgClRingObj l) x L.obj F.obj i.hom ≫
    c.algebraic.comparison.inv.app F
  let A := Padic.coefficientExtensionIntegers l E
  let V := (c.algebraic.functor.obj F).V
  let M := ((c.integral E).functor.obj L).V
  let a := (algebraMap E (PadicAlgCl l)).comp A.subtype
  letI : Algebra A (PadicAlgCl l) := a.toAlgebra
  letI : Module A V := Module.compHom V a
  ∃ N : Submodule A V,
      Nonempty (Module.Basis (Fin (Module.finrank (PadicAlgCl l) V)) A N) ∧
      Submodule.IsLattice (PadicAlgCl l) N ∧
      (∀ g : G, (c.algebraic.functor.obj F).ρ g '' (N : Set V) = (N : Set V)) ∧
      (∃ e : M ≃ₗ[A] N, ∀ z : M, (e z : V) = j z) ∧
      (∃ t : (PadicAlgCl l ⊗[A] N) ≃ₗ[PadicAlgCl l] V,
        ∀ (b : PadicAlgCl l) (z : N), t (b ⊗ₜ[A] z) = b • (z : V)) ∧
      (∀ (g : G) (z : M),
        j (((c.integral E).functor.obj L).ρ g z) =
          (c.algebraic.functor.obj F).ρ g (j z)) := by
  classical
  dsimp only
  let A := Padic.coefficientExtensionIntegers l E
  let K := PadicAlgCl l
  let V := (c.algebraic.functor.obj F).V
  let M := ((c.integral E).functor.obj L).V
  let a := (algebraMap E K).comp A.subtype
  let : Algebra A K := a.toAlgebra
  let : Module A V := Module.compHom V a
  let : IsScalarTower A E K := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A K V := IsScalarTower.of_compHom A K V
  have : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective A K).2
      ((algebraMap E K).injective.comp Subtype.val_injective)
  have hM : integralRep l E G ((c.integral E).functor.obj L) :=
    ((c.integral E).image _).mp ⟨L, ⟨Iso.refl _⟩⟩
  have : Module.Free A M := hM.1
  have : Module.Finite A M := hM.2.1
  let f := coefficientMap (integerInclusion l E) X
  let U : (integralField l E X).FullSubcategory :=
    ⟨(Mod.extendScalars f).obj L.obj, (c.localization E).closed L⟩
  obtain ⟨k, hk, hfactor⟩ := factor_presentation l x G c F E L i _he
  have hunit : IsIso (((Mod.extendRestrictAdjunction f).homEquiv L.obj U.obj).symm
      (Mod.extendUnit f L.obj)) := by
    change IsIso (((Mod.extendRestrictAdjunction f).homEquiv L.obj U.obj).symm
      ((Mod.extendRestrictAdjunction f).unit.app L.obj))
    rw [← Adjunction.homEquiv_id, Equiv.symm_apply_apply]
    infer_instance
  obtain ⟨t₁, h₁, hg₁⟩ :=
    (c.localization E).comparison L U (Mod.extendUnit f L.obj) hunit
  obtain ⟨t₂, h₂, hg₂⟩ := (c.algebraicExtension E).comparison U F k hk
  have h₁' (z : M) :
      (c.rational E).comparison.hom.app U (t₁ (1 ⊗ₜ[A] z)) =
        fibreMap (integerRing l E) (fieldRing l E) x L.obj U.obj
          (Mod.extendUnit f L.obj).hom ((c.integral E).comparison.hom.app L z) := by
    simpa only [id_eq, comparison_one x (fieldScalar l E) (c.rational E) U] using h₁ 1 z
  have h₂' (w : ((c.rational E).functor.obj U).V) :
      c.algebraic.comparison.hom.app F (t₂ (1 ⊗ₜ[E] w)) =
        fibreMap (fieldRing l E) (Profinite.padicAlgClRingObj l) x U.obj F.obj k.hom
          ((c.rational E).comparison.hom.app U w) := by
    simpa only [id_eq, comparison_one x
      (Profinite.PadicAlgCl.constSectionRingHom l (op (⊤_ Profinite.{u})))
      c.algebraic F] using h₂ 1 w
  let t : (K ⊗[A] M) ≃ₗ[K] V :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A E K K M).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) t₁ ≪≫ₗ t₂
  let j := (c.integral E).comparison.hom.app L ≫
    fibreMap (integerRing l E) (Profinite.padicAlgClRingObj l) x L.obj F.obj i.hom ≫
    c.algebraic.comparison.inv.app F
  have ht (z : M) : t (1 ⊗ₜ[A] z) = j z := by
    change t₂ (1 ⊗ₜ[E] t₁ (1 ⊗ₜ[A] z)) = j z
    calc
      _ = c.algebraic.comparison.inv.app F
          (c.algebraic.comparison.hom.app F
            (t₂ (1 ⊗ₜ[E] t₁ (1 ⊗ₜ[A] z)))) := by
        simp only [← ConcreteCategory.comp_apply, Iso.hom_inv_id_app,
          ConcreteCategory.id_apply]
      _ = j z := by
        rw [h₂', h₁']
        have hc := fibreMap_comp x L.obj U.obj F.obj
          (Mod.extendUnit f L.obj).hom k.hom
        rw [hfactor] at hc
        simp only [j, ConcreteCategory.comp_apply]
        rw [← ConcreteCategory.comp_apply
          (fibreMap (integerRing l E) (fieldRing l E) x L.obj U.obj
            (Mod.extendUnit f L.obj).hom)
          (fibreMap (fieldRing l E) (Profinite.padicAlgClRingObj l) x U.obj F.obj k.hom),
          hc]
        rfl
  have hj (q : G) (z : M) :
      j (((c.integral E).functor.obj L).ρ q z) =
        (c.algebraic.functor.obj F).ρ q (j z) := by
    rw [← ht, ← ht]
    change t₂ (1 ⊗ₜ[E] t₁ (1 ⊗ₜ[A] ((c.integral E).functor.obj L).ρ q z)) =
      (c.algebraic.functor.obj F).ρ q (t₂ (1 ⊗ₜ[E] t₁ (1 ⊗ₜ[A] z)))
    rw [hg₁, hg₂]
  obtain ⟨N, hb, hlat, ⟨e, he⟩, htensor⟩ := tensor_lattice t
  have he' (z : M) : (e z : V) = j z := (he z).trans (ht z)
  have hmem (q : G) (z : N) : (c.algebraic.functor.obj F).ρ q (z : V) ∈ N := by
    have hh := hj q (e.symm z)
    rw [← he', ← he', e.apply_symm_apply] at hh
    exact hh ▸ (e (((c.integral E).functor.obj L).ρ q (e.symm z))).property
  refine ⟨N, hb, hlat, ?_, ⟨e, he'⟩, htensor, hj⟩
  intro q
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hmem q ⟨z, hz⟩
  · intro z hz
    refine ⟨(c.algebraic.functor.obj F).ρ q⁻¹ z, hmem q⁻¹ ⟨z, hz⟩, ?_⟩
    change (((c.algebraic.functor.obj F).ρ q) *
      ((c.algebraic.functor.obj F).ρ q⁻¹)) z = z
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

end AlgebraicGeometry.ProEtale.RealIntegral
