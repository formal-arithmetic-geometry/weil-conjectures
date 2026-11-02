/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedComponentScalarModel.CondensedComponentScalarModelData
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentDerivedPullbackSquare
import WeilConjectures.AlgebraicGeometry.CondensedFiniteClosedModelLifts
import all WeilConjectures.RingTheory.WContractibleGeometricCriterion

/-! # A finite closed-lift cover carrying a prescribed scalar model

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Theorem 4.13,
finite-component reduction, with contractible covers before henselian closed lifting.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.privateModule false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedComponentScalarModel
/-- Componentwise models of one perfect scalar value yield a finite affine pro-etale
cover of every affine test, carrying that same scalar value.

Source: HRS Theorem 4.13, finite-component reduction; Bhatt--Scholze, Lemmas 2.2.12
and 6.1.1 (blueprint: lem-pod-condensed-closed-component-cover).

Proof: pull each reduced component back to Spec A. The resulting closed immersion
is a quotient spectrum Spec(A/J). Choose a faithfully flat ind-etale contractible
algebra Cbar over this quotient. Its spectrum is an affine contractible test of the
component, so the hypothesis gives its prescribed model. The pullback equation and
the quotient factorization identify its map to X with Spec Cbar -> Spec A -> X.
Apply the existing finite-closed-model-lifts theorem to f^*K, the ideals J and these
models. Its hypotheses follow from monoidal pullback preservation of dualizability,
perfectness of P and the fact that the quotient spectra cover Spec A. That theorem
constructs the actual henselian closed lifts and proves their covering property and
model extension. Derived inverse-image composition gives the displayed conclusion.
The argument allows empty pullbacks and never assumes a quotient of A contractible. -/
theorem closed_component_spec_cover
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) [IsAffine X]
    (hcomponents : (irreducibleComponents X).Finite)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)))
    (hK : Nonempty (HasRightDual K))
    (P : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ.X)))
    (hP : DerivedCategory.IsPerfectRingComplex P)
    (hmodel : ∀ Z, HasModel Λ X K P Z)
    (A : Type u) [CommRing A] (f : Spec (.of A) ⟶ X) [WeaklyEtale f] :
    ∃ (I : Type u) (_ : Finite I) (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ Spec (.of A)),
      (∀ i, IsAffine (T i)) ∧ (∀ i, WeaklyEtale (g i)) ∧
      Presieve.ofArrows T g ∈ Scheme.proetalePrecoverage (Spec (.of A)) ∧
      (∀ i, Nonempty ((CondensedRing.upperStar Λ.X (g i ≫ f)).mapDerivedCategory.obj K ≅
        (condensedScalarRealization Λ.X (T i)).obj P)) := by
  classical
  let Z := irreducibleComponents X
  have : Finite Z := hcomponents.to_subtype
  let Y (z : Z) := pullback f (inclusion X z)
  let a (z : Z) : Y z ⟶ Spec (.of A) := pullback.fst f (inclusion X z)
  let b (z : Z) : Y z ⟶ component X z := pullback.snd f (inclusion X z)
  have ha (z : Z) : IsClosedImmersion (a z) := inferInstance
  have hb (z : Z) : WeaklyEtale (b z) := inferInstance
  choose J e he using fun z : Z ↦ (IsClosedImmersion.Spec_iff (f := a z)).mp (ha z)
  choose Cbar cr ca ci cf cw using fun z : Z ↦ exists_isWContractibleRing (A ⧸ J z)
  let := cr
  let := ca
  let := ci
  let := cf
  let := cw
  let alg (z : Z) : Algebra A (Cbar z) :=
    ((algebraMap (A ⧸ J z) (Cbar z)).comp (Ideal.Quotient.mk (J z))).toAlgebra
  let := alg
  have tower (z : Z) : IsScalarTower A (A ⧸ J z) (Cbar z) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let q (z : Z) : Spec (.of (Cbar z)) ⟶ Spec (.of (A ⧸ J z)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ J z) (Cbar z)))
  let w (z : Z) : Spec (.of (Cbar z)) ⟶ component X z := q z ≫ (e z).inv ≫ b z
  have hw (z : Z) : WeaklyEtale (w z) := by
    dsimp only [w, q]
    infer_instance
  have hcbar (z : Z) : IsWContractibleRing Γ(Spec (.of (Cbar z)), ⊤) :=
    RingHom.wContractible_of_ringEquiv
      (Scheme.ΓSpecIso (.of (Cbar z))).commRingCatIsoToRingEquiv.symm
  have hwp (z : Z) : w z ≫ inclusion X z =
      Spec.map (CommRingCat.ofHom (algebraMap A (Cbar z))) ≫ f := by
    dsimp only [w, b]
    rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc]
    have heq : (e z).inv ≫ a z =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J z))) := by
      rw [he z]
      simp
    change ((q z ≫ (e z).inv) ≫ a z) ≫ f = _
    rw [Category.assoc (q z), heq, ← Spec.map_comp]
    rfl
  have hcover : ∀ x : PrimeSpectrum A, ∃ z : Z, J z ≤ x.asIdeal := by
    intro x
    let z : Z := ⟨irreducibleComponent (f x),
      irreducibleComponent_mem_irreducibleComponents (f x)⟩
    have hz : f x ∈ Set.range (inclusion X z) := by
      rw [range_inclusion]
      exact mem_irreducibleComponent
    obtain ⟨y, hy⟩ := hz
    obtain ⟨v, hv, _⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := f) (g := inclusion X z) x y hy.symm
    have hqx : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J z))) ((e z).hom v) = x := by
      rw [← Scheme.Hom.comp_apply, ← he z]
      exact hv
    refine ⟨z, ?_⟩
    rw [← hqx]
    intro r hr
    change Ideal.Quotient.mk (J z) r ∈ ((e z).hom v).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact Ideal.zero_mem _
  let K' := (CondensedRing.upperStar Λ.X f).mapDerivedCategory.obj K
  have hK' : IsDualizable K' :=
    condensed_derivedPullback_preserves_dualizable Λ f K hK
  have α (z : Z) : (CondensedRing.upperStar Λ.X
      (closedModelFiberMap A (Cbar z) ≫ closedModelLiftMap A (Cbar z))).mapDerivedCategory.obj K' ≅
        (condensedScalarRealization Λ.X (Spec (.of (Cbar z)))).obj P := by
    let m := (hmodel z (Scheme.ProEt.mk (w z))
      (inferInstanceAs (IsAffine (Spec (.of (Cbar z))))) (hcbar z)).some
    have hcomp : closedModelFiberMap A (Cbar z) ≫ closedModelLiftMap A (Cbar z) =
        Spec.map (CommRingCat.ofHom (algebraMap A (Cbar z))) := by
      unfold closedModelFiberMap closedModelLiftMap
      rw [← Spec.map_comp]
      congr 1
      ext r
      exact (Algebra.ClosedLift.toAlgHom A (Cbar z)).commutes r
    rw [hcomp]
    exact ((ComponentDerivedSquare.schemeComposition Λ f _).app K).symm ≪≫
      eqToIso (congrArg (fun g ↦ (CondensedRing.upperStar Λ.X g).mapDerivedCategory.obj K)
        (hwp z).symm) ≪≫ m
  obtain ⟨hlift, _, _, _, _, hcov⟩ :=
    condensed_finite_closed_model_lifts Λ A Z J hcover Cbar K' hK' (fun _ ↦ P)
      (fun _ ↦ hP) α
  refine ⟨Z, inferInstance, fun z ↦ Spec (.of (Algebra.ClosedLift A (Cbar z))),
    fun z ↦ closedModelLiftMap A (Cbar z), fun _ ↦ inferInstance,
    fun z ↦ (hlift z).2.2.2.2.2.1, ?_, ?_⟩
  · exact hcov
  · intro z
    obtain ⟨m, _⟩ := (hlift z).2.2.2.2.1.exists
    exact ⟨(ComponentDerivedSquare.schemeComposition Λ f _).app K ≪≫ m⟩
end AlgebraicGeometry.ProEtale.CondensedComponentScalarModel
