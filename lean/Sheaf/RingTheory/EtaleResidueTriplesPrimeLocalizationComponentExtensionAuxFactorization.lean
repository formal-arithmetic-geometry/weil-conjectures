module

public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Etale.Pi

-- This retired module retains only private counterexample certificates.
set_option linter.privateModule false

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The residue-pointing maps form a cocone, so the disputed statement's cocone
hypothesis can be fulfilled with V = K. This is an explicit construction. -/
private noncomputable def residuePointingCocone
    (R : CommRingCat.{u}) (p : Spec R) (K : Type u) [Field K]
    (χ : (Spec R).residueField p ⟶ CommRingCat.of K) :
    etaleResidueTriplesRingDiagram R p K χ ⟶
      (Functor.const _).obj (CommRingCat.of K) where
  app s := (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ
  naturality c s a := by
    change a.hom.right.left ≫
      ((ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ) =
        ((ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ) ≫ 𝟙 _
    have h := Over.w a.hom.right
    change a.hom.right.left ≫
      ((ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ) =
        (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ at h
    exact h.trans (Category.comp_id _).symm

/-- Certificate for the failure of the cancellation conclusion above.

Source: Mathlib's finite-product étaleness and `SpecToEquivOfField`; elementary
product counterexample, written by B2. The field-point construction follows the
checked counterexample in EtaleResidueTriplesPrimeLocalizationComponentExtensionAuxModelPointing.

Take c to be the identity pointed triple over R and s to be the pointed étale
algebra R × R (written as Fin 2 → R), with its first-coordinate pointing to K.
Let i be R → R_p → t.B and β be the first projection followed by i. The two
compatibility equations hold by t.compatible, hψ and hK. Every arrow c → s has
underlying ring map equal to the diagonal, by its R-algebra compatibility. The
maps s.B → K through the two projections agree after the diagonal. Cancellation
would make them equal, but evaluation on (1, 0) gives 1 = 0 in K.

This certificate does not use the disputed theorem or any project theorem with
sorry. It works for every t under the original base-pointing hypotheses. -/
private theorem factorization_counterexample
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
    ∃ (c s : EtaleResidueTriples R p K χ) (i : c.B ⟶ t.B) (β : s.B ⟶ t.B),
      c.α ≫ i = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α ∧
      i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ ∧
      s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α ∧
      β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ ∧
      ¬ ∃ a : c ⟶ s,
        (etaleResidueTriplesRingDiagram R p K χ).map a ≫ β = i ∧
        ∀ (f g : s.B ⟶ CommRingCat.of K),
          (etaleResidueTriplesRingDiagram R p K χ).map a ≫ f =
            (etaleResidueTriplesRingDiagram R p K χ).map a ≫ g → f = g := by
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
  let s : EtaleResidueTriples R p K χ :=
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
  let c : EtaleResidueTriples R p K χ :=
    ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩
  let i : c.B ⟶ t.B := l ≫ t.α
  let β : s.B ⟶ t.B := e₀ ≫ l ≫ t.α
  refine ⟨c, s, i, β, ?_, ?_, ?_, ?_, ?_⟩
  · exact Category.id_comp _
  · change l ≫ t.α ≫ (ΓSpecIso t.B).inv ≫
      (Spec t.B).Γevaluation t.q ≫ t.φ = b
    rw [t.compatible, hψ, hK]
  · change a ≫ e₀ ≫ l ≫ t.α = l ≫ t.α
    rw [← Category.assoc, hae₀, Category.id_comp]
  · change e₀ ≫ l ≫ t.α ≫ (ΓSpecIso t.B).inv ≫
      (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso B).inv ≫ (Spec B).Γevaluation z ≫ φ
    rw [t.compatible, hψ, hK, hφ]
  · rintro ⟨a', _, hepi⟩
    have ha : (etaleResidueTriplesRingDiagram R p K χ).map a' = a := by
      have h := congrArg CommaMorphism.left (Under.w a'.hom)
      change (𝟙 R) ≫ (etaleResidueTriplesRingDiagram R p K χ).map a' = a at h
      simpa using h
    have heq : e₀ ≫ b = e₁ ≫ b := hepi (e₀ ≫ b) (e₁ ≫ b) (by
      change a'.hom.right.left ≫ (e₀ ≫ b) = a'.hom.right.left ≫ (e₁ ≫ b)
      have ha' : a'.hom.right.left = a := ha
      rw [ha']
      change a ≫ (e₀ ≫ b) = a ≫ (e₁ ≫ b)
      exact (Category.assoc a e₀ b).symm.trans
        ((congrArg (fun k : R ⟶ R ↦ k ≫ b) (hae₀.trans hae₁.symm)).trans
          (Category.assoc a e₁ b)))
    have h := congrArg (fun f : B ⟶ CommRingCat.of K ↦
      f.hom (fun j : Fin 2 ↦ if j = 0 then 1 else 0)) heq
    change b.hom (if (0 : Fin 2) = 0 then 1 else 0) =
      b.hom (if (1 : Fin 2) = 0 then 1 else 0) at h
    simp at h

/-- The full universally quantified statement above is false, already for the
explicit cocone of residue-pointing maps with vertex K. -/
private theorem factorization_statement_refuted
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
    ¬ ∀ (c : EtaleResidueTriples R p K χ) (i : c.B ⟶ t.B),
      c.α ≫ i = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α →
      i ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
        (ΓSpecIso c.B).inv ≫ (Spec c.B).Γevaluation c.q ≫ c.φ →
      ∃ b : t.B ⟶ CommRingCat.of K,
        i ≫ b = (residuePointingCocone R p K χ).app c ∧
        ∀ (s : EtaleResidueTriples R p K χ) (β : s.B ⟶ t.B),
          s.α ≫ β = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ t.α →
          β ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
            (ΓSpecIso s.B).inv ≫ (Spec s.B).Γevaluation s.q ≫ s.φ →
          ∃ a : c ⟶ s,
            (etaleResidueTriplesRingDiagram R p K χ).map a ≫ β = i ∧
            ∀ (f g : s.B ⟶ CommRingCat.of K),
              (etaleResidueTriplesRingDiagram R p K χ).map a ≫ f =
                (etaleResidueTriplesRingDiagram R p K χ).map a ≫ g → f = g := by
  intro h
  obtain ⟨c, s, i, β, hiα, hiφ, hβα, hβφ, hno⟩ :=
    factorization_counterexample R p K χ q ψ hψ hK t
  obtain ⟨_, _, hfac⟩ := h c i hiα hiφ
  exact hno (hfac s β hβα hβφ)

end AlgebraicGeometry.Scheme
