module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Etale.Pi

set_option linter.privateModule false

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- STATEMENT-DISPUTED: The structure equation does not determine the pointing.
-- The private theorem `pointing_counterexample` below constructs a counterexample
-- for every local triple t under exactly the stated base-pointing hypotheses.
/-- Certified counterexample to the disputed theorem above, without using that theorem.

Proof: Let B = R × R, written as `Fin 2 → R`, and give it the diagonal R-algebra
structure, which is etale by Mathlib's finite-product instance. Write b for the fixed
map R → K. Point B in K through evaluation at coordinate 0 followed by b. The field-point
correspondence supplies its prime and residue-field embedding, and compatibility forces
this prime to lie above p. Define i using evaluation at coordinate 1 followed by
R → R_p → t.B. Both coordinate projections split the diagonal, proving the structure
equation. The hypotheses hψ and hK and t.compatible identify its composite to K with
coordinate 1 followed by b. If it equalled the pointing through coordinate 0, evaluating
on the vector (1, 0) would give 0 = 1 in the field K, a contradiction.

The field point is obtained directly from Mathlib’s `SpecToEquivOfField` equivalence.
Its inverse law gives the factorization, and its point is definitionally the image
of the closed point of Spec K. The counterexample argument is written by R2. -/
private theorem pointing_counterexample
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K)
    (q : Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)))
    (ψ : (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).residueField q ⟶
      CommRingCat.of K)
    [Algebra (Localization.AtPrime p.asIdeal) K]
    (hψ : (ΓSpecIso (CommRingCat.of (Localization.AtPrime p.asIdeal))).inv ≫
      (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).Γevaluation q ≫ ψ =
        CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K))
    (hK : CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫
      CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal) K) =
        (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ)
    (t : EtaleResidueTriples (CommRingCat.of (Localization.AtPrime p.asIdeal)) q K ψ) :
    ∃ (c : EtaleResidueTriples R p K χ) (i : c.B ⟶ t.B),
      c.α ≫ i = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α ∧
      i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ ≠
        (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ := by
  let B := CommRingCat.of (Fin 2 → R)
  let a : R ⟶ B := CommRingCat.ofHom (algebraMap R (Fin 2 → R))
  let b := (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ
  let e₀ : B ⟶ R := CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 2 ↦ R) 0)
  let e₁ : B ⟶ R := CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 2 ↦ R) 1)
  let f := Spec.map (e₀ ≫ b)
  let z := (SpecToEquivOfField K (Spec B) f).1
  let φ := (SpecToEquivOfField K (Spec B) f).2
  have hφ : (ΓSpecIso B).inv ≫ (Spec B).Γevaluation z ≫ φ = e₀ ≫ b := by
    apply Spec.map_injective
    have h := (SpecToEquivOfField K (Spec B)).symm_apply_apply f
    change Spec.map φ ≫ (Spec B).fromSpecResidueField z = f at h
    change Spec.map ((ΓSpecIso B).inv ≫ (Spec B).Γevaluation z ≫ φ) = f
    rw [← h]
    simp only [fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
    rfl
  have hae₀ : a ≫ e₀ = 𝟙 R := by ext r; rfl
  have hae₁ : a ≫ e₁ = 𝟙 R := by ext r; rfl
  have hc : a ≫ (ΓSpecIso B).inv ≫ (Spec B).Γevaluation z ≫ φ = b := by
    rw [hφ, ← Category.assoc, hae₀, Category.id_comp]
  let c : EtaleResidueTriples R p K χ :=
    { B := B
      α := a
      etale := (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mpr
        (RingHom.etale_algebraMap.mpr inferInstance)
      q := z
      over := by
        change (Spec.map a) (f (IsLocalRing.closedPoint K)) = p
        have hf : f ≫ Spec.map a = Spec.map b := by
          rw [← Spec.map_comp, ← Category.assoc, hae₀, Category.id_comp]
        have hpoint : Spec.map b = Spec.map χ ≫ (Spec R).fromSpecResidueField p := by
          simp only [b, fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
          rfl
        have h := congrArg
          (fun g : Spec (CommRingCat.of K) ⟶ Spec R ↦ g (IsLocalRing.closedPoint K))
          (hf.trans hpoint)
        simpa using h
      φ := φ
      compatible := hc }
  let l := CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal))
  let i : c.B ⟶ t.B := e₁ ≫ l ≫ t.α
  refine ⟨c, i, ?_, ?_⟩
  · change a ≫ e₁ ≫ l ≫ t.α = l ≫ t.α
    rw [← Category.assoc, hae₁, Category.id_comp]
  · intro heq
    change e₁ ≫ l ≫ t.α ≫ (ΓSpecIso t.B).inv ≫
      (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso B).inv ≫ (Spec B).Γevaluation z ≫ φ at heq
    rw [t.compatible, hψ, hK, hφ] at heq
    have h := congrArg (fun f : B ⟶ CommRingCat.of K ↦
      f.hom (fun j : Fin 2 ↦ if j = 0 then 1 else 0)) heq
    change b.hom (if (1 : Fin 2) = 0 then 1 else 0) =
      b.hom (if (0 : Fin 2) = 0 then 1 else 0) at h
    simp at h

end AlgebraicGeometry.Scheme
