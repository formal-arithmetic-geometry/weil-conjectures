module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.CategoryTheory.Endomorphism
public import Sheaf.FieldTheory.FieldTower
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Geometric orbits under a finite normal scalar extension

Source: ILO, Travaux de Gabber, X 2.3 Step 2, printed p.150, diagram (2.b);
Stacks Tags 00FV, 09HN and 0BR4.
(blueprint: lem-sfb-normal-scalar-extension-geometric-orbits).

The chosen model of W_b is (V ×_B Spec Ω) ×_F Spec K. Pullback associativity
identifies this canonically with (V ×_F Spec K) ×_B Spec Ω, preserving all projections.
The auxiliary declarations construct only these projections and induced maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.NormalScalarExtension

/-- The scalar projection of a geometric fibre.
Source: ILO X 2.3 Step 2, p.150 (blueprint: lem-sfb-normal-scalar-extension-geometric-orbits). -/
abbrev fibreScalar {F Ω : Type u} [Field F] [Field Ω] {V B : Scheme.{u}}
    (p : V ⟶ Spec (.of F)) (v : V ⟶ B) (b : Spec (.of Ω) ⟶ B) :
    pullback v b ⟶ Spec (.of F) :=
  pullback.fst v b ≫ p

/-- W_b, with the scalar extension performed after the geometric base change.
Source: ILO X 2.3 Step 2, p.150 (blueprint: lem-sfb-normal-scalar-extension-geometric-orbits). -/
abbrev scalarFibre {F Ω : Type u} (K : Type u) [Field F] [Field K] [Field Ω]
    [Algebra F K] {V B : Scheme.{u}} (p : V ⟶ Spec (.of F))
    (v : V ⟶ B) (b : Spec (.of Ω) ⟶ B) : Scheme.{u} :=
  pullback (fibreScalar p v b) (Spec.map (CommRingCat.ofHom (algebraMap F K)))

/-- The action induced on V_b by the actual pullback universal property.
Source: ILO X 2.3 Step 2, p.150 (blueprint: lem-sfb-normal-scalar-extension-geometric-orbits). -/
def fibreMap {Ω : Type u} [Field Ω] {V B : Scheme.{u}}
    {J : Type v} [Group J] (a : J →* Aut V) (v : V ⟶ B)
    (hv : ∀ j : J, (a j).hom ≫ v = v) (b : Spec (.of Ω) ⟶ B) (j : J) :
    pullback v b ⟶ pullback v b :=
  pullback.map v b v b (a j).hom (𝟙 _) (𝟙 _)
    ((Category.comp_id v).trans (hv j).symm) (by simp)

/-- The actual diagonal map on W_b, with the inverse scalar-automorphism convention.
Source: ILO X 2.3 Step 2, p.150 (blueprint: lem-sfb-normal-scalar-extension-geometric-orbits). -/
def diagonalMap {e F K Ω : Type u} [Field e] [Field F] [Field K] [Field Ω]
    [Algebra e F] [Algebra e K] [Algebra F K]
    {J : Type v} [Group J] {Γ : Type w} [Group Γ]
    (ρ : J →* (F ≃ₐ[e] F)) (r : Γ →* J) (α : Γ →* (K ≃ₐ[e] K))
    {V B : Scheme.{u}} (p : V ⟶ Spec (.of F)) (a : J →* Aut V)
    (hs : ∀ j : J, (a j).hom ≫ p =
      p ≫ Spec.map (CommRingCat.ofHom (ρ j).symm.toRingHom))
    (hc : ∀ γ : Γ,
      Spec.map (CommRingCat.ofHom (algebraMap F K)) ≫
          Spec.map (CommRingCat.ofHom (ρ (r γ)).symm.toRingHom) =
        Spec.map (CommRingCat.ofHom (α γ).symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap F K)))
    (v : V ⟶ B) (hv : ∀ j : J, (a j).hom ≫ v = v)
    (b : Spec (.of Ω) ⟶ B) (γ : Γ) : scalarFibre K p v b ⟶ scalarFibre K p v b :=
  pullback.map (fibreScalar p v b) _ (fibreScalar p v b) _
    (fibreMap a v hv b (r γ))
    (Spec.map (CommRingCat.ofHom (α γ).symm.toRingHom))
    (Spec.map (CommRingCat.ofHom (ρ (r γ)).symm.toRingHom))
    (by simp [fibreScalar, fibreMap, Category.assoc, hs]) (hc γ)

/-- Rationality, the canonical evaluation bijection, its kernel-action formula, and
nonempty transitivity after finite normal scalar extension. No separability,
reducedness, faithfulness, or normality of the intermediate extension is required.

Source: ILO, Travaux de Gabber, X 2.3 Step 2, printed p.150, diagram (2.b);
Stacks 00FV, 09HN and 0BR4 (blueprint: lem-sfb-normal-scalar-extension-geometric-orbits).

Proof:
1. By lem-weil-pbc-lft-affine-pairs, finite generation over F, together with a
   finite e-basis of F, gives finite generation over e and over each affine base
   ring in B. Thus v is locally of finite type. Apply lem-weil-pbc-lft-base-change.
2. The finite transitive nonempty point set of V_b is T0. A minimal nonempty
   point closure is a singleton, so there is a closed point; its translates show
   every point is closed. Lem-weil-pbc-closed-point-residue-field-base gives the
   structural residue isomorphism with Ω at every point.
3. Pullback associativity gives our model of W_b. By lem-weil-pbc-fibre-product-points
   and lem-weil-pbc-fibre-product-affine-spectra its fibre at x is Spec(Ω ⊗_F K).
4. This tensor algebra is finite-dimensional over Ω. Every prime quotient is a
   finite-dimensional domain, hence a field algebraic over Ω. By
   lem-weil-pbc-algebraic-over-algebraically-closed-subfield it is Ω, canonically.
   This argument permits nilpotents.
5. Each prime thus gives the unique evaluation z ⊗ k ↦ z β(k), and conversely
   evaluation has prime kernel. These maps are inverse. Existence follows from
   lem-weil-pbc-algebraic-extension-embeds-algebraically-closed. The projections
   of the evaluation point are exactly the rational section at x and Spec β;
   this characterizes the correspondence without choosing a tensor presentation.
6. For γ in ker r the pullback on the tensor algebra sends z ⊗ k to
   z ⊗ α(γ)⁻¹(k). Composing evaluation gives β ∘ α(γ)⁻¹, proving the formula.
7. By lem-weil-pbc-normal-extension-normal-over-intermediate, K/F is normal.
   Lem-sfb-normal-embeddings-automorphism-transitive and the kernel-image
   hypothesis make the kernel transitive on each nonempty fibre.
8. Lift an element carrying the projections of two points through the surjection r,
   then correct within the target fibre by an element of ker r. This proves
   nonempty transitivity on W_b.
-/
theorem geometric_orbits
    {e F K : Type u} [Field e] [Field F] [Field K]
    [Algebra e F] [Algebra F K] [Algebra e K] [IsScalarTower e F K]
    [Module.Finite e K] [Normal e K]
    {J : Type v} [Group J] [Finite J] {Γ : Type w} [Group Γ] [Finite Γ]
    (ρ : J →* (F ≃ₐ[e] F)) (r : Γ →* J) (hr : Function.Surjective r)
    (α : Γ →* (K ≃ₐ[e] K))
    (hc : ∀ γ : Γ,
      Spec.map (CommRingCat.ofHom (algebraMap F K)) ≫
          Spec.map (CommRingCat.ofHom (ρ (r γ)).symm.toRingHom) =
        Spec.map (CommRingCat.ofHom (α γ).symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap F K)))
    (hk : ∀ τ : K ≃ₐ[e] K,
      (∃ γ : Γ, r γ = 1 ∧ α γ = τ) ↔
        ∀ t : F, τ (algebraMap F K t) = algebraMap F K t)
    (V : Scheme.{u}) (p : V ⟶ Spec (.of F))
    [LocallyOfFiniteType p] [QuasiCompact p] (a : J →* Aut V)
    (hs : ∀ j : J, (a j).hom ≫ p =
      p ≫ Spec.map (CommRingCat.ofHom (ρ j).symm.toRingHom))
    (B : Scheme.{u}) (s : B ⟶ Spec (.of e)) (v : V ⟶ B)
    (he : v ≫ s = p ≫ Spec.map (CommRingCat.ofHom (algebraMap e F)))
    (hv : ∀ j : J, (a j).hom ≫ v = v)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ B)
    (hn : Nonempty ↥(pullback v b))
    (ht : ∀ x y : ↥(pullback v b), ∃ j : J, fibreMap a v hv b j x = y) :
    (∀ x : ↥(pullback v b),
      ∃ i : CommRingCat.of Ω ≅ (pullback v b).residueField x,
        i.hom = Spec.preimage ((pullback v b).fromSpecResidueField x ≫ pullback.snd v b) ∧
        ∃ E : {β : K →+* Ω // ∀ t : F,
            β (algebraMap F K t) =
              (Spec.preimage ((pullback v b).fromSpecResidueField x ≫ fibreScalar p v b) ≫
                i.inv) t} ≃
            {y : scalarFibre K p v b //
              pullback.fst (fibreScalar p v b)
                (Spec.map (CommRingCat.ofHom (algebraMap F K))) y = x},
          Nonempty {β : K →+* Ω // ∀ t : F,
            β (algebraMap F K t) =
              (Spec.preimage ((pullback v b).fromSpecResidueField x ≫ fibreScalar p v b) ≫
                i.inv) t} ∧
          (∀ β, ∃ t : Spec (.of Ω) ⟶ scalarFibre K p v b,
            t ≫ pullback.fst (fibreScalar p v b)
                (Spec.map (CommRingCat.ofHom (algebraMap F K))) =
              Spec.map i.inv ≫ (pullback v b).fromSpecResidueField x ∧
            t ≫ pullback.snd (fibreScalar p v b)
                (Spec.map (CommRingCat.ofHom (algebraMap F K))) =
              Spec.map (CommRingCat.ofHom β.val) ∧
            t ≫ pullback.fst (fibreScalar p v b)
                (Spec.map (CommRingCat.ofHom (algebraMap F K))) ≫ pullback.snd v b =
              𝟙 (Spec (.of Ω)) ∧
            (E β).val = t (IsLocalRing.closedPoint Ω)) ∧
          (∀ (γ : Γ) (_ : r γ = 1) β₁, ∃ β₂,
            β₂.val = β₁.val.comp (α γ).symm.toRingHom ∧
              (E β₂).val = diagonalMap ρ r α p a hs hc v hv b γ (E β₁).val)) ∧
    Nonempty (scalarFibre K p v b) ∧
    (∀ y₁ y₂ : scalarFibre K p v b, ∃ γ : Γ,
      diagonalMap ρ r α p a hs hc v hv b γ y₁ = y₂) := by
  sorry

end AlgebraicGeometry.NormalScalarExtension
