/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
import Sheaf.AlgebraicGeometry.EtaleFieldGeometricAction
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
import Mathlib.FieldTheory.IsAlgClosed.Classification

/-!
# Open stabilizers for the action on geometric étale lifts

Source: Stacks Project, Tag 03QW, and Tag 03QR for the separable-closure action.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem exists_algEquiv_extension
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω] (g : Gal(Ks/K)) :
    ∃ τ : Ω ≃ₐ[K] Ω, (algebraMap Ks Ω).comp g.toRingHom =
      τ.toRingHom.comp (algebraMap Ks Ω) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis Ks Ω
  let v : s → Ω := Subtype.val
  let A := Algebra.adjoin Ks (Set.range v)
  let e := hs.1.aevalEquiv
  let f : A ≃+* A := e.symm.toRingEquiv.trans
    ((MvPolynomial.mapEquiv s g.toRingEquiv).trans e.toRingEquiv)
  let : IsAlgClosure A Ω := IsAlgClosed.isAlgClosure_of_transcendence_basis v hs
  let t : Ω ≃+* Ω := IsAlgClosure.equivOfEquiv Ω Ω f
  have ht (a : Ks) : t (algebraMap Ks Ω a) = algebraMap Ks Ω (g a) := by
    have he (a : Ks) : e (MvPolynomial.C a) = algebraMap Ks A a := by
      exact e.commutes a
    have hf (a : Ks) : f (algebraMap Ks A a) = algebraMap Ks A (g a) := by
      change e (MvPolynomial.mapEquiv s g.toRingEquiv (e.symm (algebraMap Ks A a))) = _
      rw [← he, e.symm_apply_apply]
      simpa using he (g a)
    rw [IsScalarTower.algebraMap_apply Ks A Ω]
    change t (algebraMap A Ω _) = _
    rw [IsAlgClosure.equivOfEquiv_algebraMap, hf]
    rfl
  let τ : Ω ≃ₐ[K] Ω :=
    { t with
      commutes' := fun a ↦ by
        change t (algebraMap K Ω a) = algebraMap K Ω a
        rw [IsScalarTower.algebraMap_apply K Ks Ω, ht, g.commutes] }
  exact ⟨τ, RingHom.ext fun a ↦ (ht a).symm⟩

private theorem separablePoint_stabilizer_open
    (K Ks : Type u) [Field K] [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]
    (X : (Spec (.of K)).Etale)
    (y : etaleFieldBasePoint K Ks ⟶ (Etale.forget _).obj X) :
    IsOpen {g : Gal(Ks/K) | etaleFieldPointAutomorphism K Ks g ≫ y = y} := by
  let A := etaleFieldGeometricAction K Ks X
  let : HasForget₂ (Type u) TopCat := etaleFieldDiscreteForget₂
  have hcont := etaleFieldGeometricAction_continuous K Ks X
  change ContinuousSMul (Gal(Ks/K))
    ((forget₂ (Action (Type u) (Gal(Ks/K))) TopCat).obj A) at hcont
  have : DiscreteTopology
      ((forget₂ (Action (Type u) (Gal(Ks/K))) TopCat).obj A) := by
    change DiscreteTopology (TopCat.discrete.obj A.V)
    infer_instance
  exact (continuousSMul_iff_stabilizer_isOpen.mp hcont) y

/-- (blueprint: lem-exc-galois-point-action-open).

Open stabilizers for the action on geometric étale lifts.

(source: Stacks Project, Tag 03QW, discussion before Theorem 59.56.3;
 blueprint: lem-exc-galois-point-action-open).

For an action obtained by precomposition with extensions of Galois automorphisms, a lift
factors through the finite separable residue field of its image point.  The subgroup fixing
that finite intermediate field is open in the Krull topology and fixes the lift.  The full
stabilizer is a union of its translates and is therefore open.
-/
theorem galoisPointAction_open_stabilizers
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (ρ : Gal(Ks/K) →* End (pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber)
    (hρ : ∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω)
      (_ : (algebraMap Ks Ω).comp g.toRingHom =
        τ.toRingHom.comp (algebraMap Ks Ω))
      (X : (Spec (.of K)).Etale)
      (x : (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X),
      ((ρ g).app X x).left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left) :
    ∀ (X : (Spec (.of K)).Etale)
      (x : (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X),
      IsOpen {g : Gal(Ks/K) | (ρ g).app X x = x} := by
  classical
  intro X x
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap Ks Ω)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K Ks)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact (IsScalarTower.algebraMap_apply K Ks Ω a).symm
  have : IsSepClosed Ks := IsSepClosure.sep_closed K
  obtain ⟨l, hl, hr⟩ := X.hom.exists_SpecMap_comp_eq_of_isSepClosed
    (CommRingCat.ofHom (algebraMap Ks Ω))
    (Spec.map (CommRingCat.ofHom (algebraMap K Ks))) x.left
    ((Over.w x).trans hbase.symm)
  let y : etaleFieldBasePoint K Ks ⟶ (Etale.forget _).obj X := Over.homMk l hr
  let : MulAction (Gal(Ks/K)) ((pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X) :=
    { smul := fun g z ↦ (ρ g).app X z
      one_smul := fun z ↦ by
        change (ρ 1).app X z = z
        rw [ρ.map_one]
        rfl
      mul_smul := fun g h z ↦ by
        change (ρ (g * h)).app X z = (ρ g).app X ((ρ h).app X z)
        rw [ρ.map_mul]
        rfl }
  let A := etaleFieldGeometricAction K Ks X
  let H : Subgroup (Gal(Ks/K)) :=
    @MulAction.stabilizer (Gal(Ks/K)) A.V _ (Action.instMulAction A) y
  apply Subgroup.isOpen_mono (H₁ := H) (H₂ := MulAction.stabilizer (Gal(Ks/K)) x) ?_
    (separablePoint_stabilizer_open K Ks X y)
  intro g hg
  change (ρ g).app X x = x
  obtain ⟨τ, hτ⟩ := exists_algEquiv_extension K Ks Ω g
  apply Over.OverMorphism.ext
  rw [hρ g τ hτ X x, ← hl, ← Category.assoc, ← Spec.map_comp]
  have hcomm : CommRingCat.ofHom (algebraMap Ks Ω) ≫
      CommRingCat.ofHom τ.toRingHom =
      CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom (algebraMap Ks Ω) := by
    exact congrArg CommRingCat.ofHom hτ.symm
  rw [hcomm, Spec.map_comp, Category.assoc]
  have hfix : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ l = l :=
    congrArg Over.Hom.left hg
  rw [hfix]

end AlgebraicGeometry.Scheme
