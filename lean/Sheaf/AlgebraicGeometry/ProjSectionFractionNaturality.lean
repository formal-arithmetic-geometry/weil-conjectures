module

public import Sheaf.AlgebraicGeometry.StandardProjTwistTensor
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import Mathlib.Algebra.DirectSum.Module
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Naturality of twisted-section fraction evaluation on Proj

Source: Stacks Project, constructions.tex, Tag 0B5I
(lemma-comparison-proj-quasi-coherent), displayed fraction map and overlap verification.
(blueprint: lem-sfb-proj-section-fraction-naturality).

The domain is an additive subgroup of the ordinary module localization, with its
carrier specified by homogeneous fractions. Scalar closure and scalar compatibility
state linearity over the homogeneous localization without choosing new scalar instances.
Division by the trivializing section is specified by multiplication back by that section.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace LocalizedModule
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

variable {S : Type u} [CommRing S] (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]

/-- The fraction maps, their linearity, and all homogeneous restriction formulas.
This predicate only packages equations on the actual localization quotient.
Source: Stacks 0B5I, displayed map and overlap verification; 01M4, chart restrictions.
(blueprint: lem-sfb-proj-section-fraction-naturality). -/
def IsProjSectionFractionNaturality (F : (Proj 𝒜).Modules)
    [Module S (DirectSum ℤ (fun n : ℤ ↦ Γ(F ⊗ twist 𝒜 n, ⊤)))] : Prop :=
  ∃ (Z : ∀ f : {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2},
      AddSubgroup (LocalizedModule.Away f.val.1
        (DirectSum ℤ (fun n : ℤ ↦ Γ(F ⊗ twist 𝒜 n, ⊤)))))
    (phi : ∀ f : {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2},
      Z f →+ Γ(F, basicOpen 𝒜 f.val.1))
    (rho : ∀ (f g : {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}),
      basicOpen 𝒜 g.val.1 ≤ basicOpen 𝒜 f.val.1 → Z f →+ Z g),
    (∀ f : {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}, (Z f : Set (LocalizedModule.Away f.val.1
        (DirectSum ℤ (fun n : ℤ ↦ Γ(F ⊗ twist 𝒜 n, ⊤))))) =
      {q | ∃ (m : ℕ) (t : Γ(F ⊗ twist 𝒜 ((m * f.val.2 : ℕ) : ℤ), ⊤)),
        mk (DirectSum.of (fun n : ℤ ↦ Γ(F ⊗ twist 𝒜 n, ⊤))
          ((m * f.val.2 : ℕ) : ℤ) t)
          (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) = q}) ∧
    (∀ (f : {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2})
      (r : HomogeneousLocalization.Away 𝒜 f.val.1) (q : Z f),
      ∃ q' : Z f,
        (q' : LocalizedModule.Away f.val.1
          (DirectSum ℤ (fun n : ℤ ↦ Γ(F ⊗ twist 𝒜 n, ⊤)))) = r.val • q.val ∧
        phi f q' = @SMul.smul Γ(Proj 𝒜, basicOpen 𝒜 f.val.1)
          Γ(F, basicOpen 𝒜 f.val.1) inferInstance (awayToSection 𝒜 f.val.1 r) (phi f q)) ∧
    (∀ (f : {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2})
      (m : ℕ) (t : Γ(F ⊗ twist 𝒜 ((m * f.val.2 : ℕ) : ℤ), ⊤)) (q : Z f),
      (q : LocalizedModule.Away f.val.1
        (DirectSum ℤ (fun n : ℤ ↦ Γ(F ⊗ twist 𝒜 n, ⊤)))) =
        mk (DirectSum.of (fun n : ℤ ↦ Γ(F ⊗ twist 𝒜 n, ⊤))
          ((m * f.val.2 : ℕ) : ℤ) t)
          (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) →
      tmulSection (phi f q)
        ((unitToTwist (f := f.val.1 ^ m) (d := m * f.val.2)
          (by simpa only [smul_eq_mul] using SetLike.pow_mem_graded m f.property.2) ≫
          eqToHom (congrArg (twist 𝒜) (zero_add ((m * f.val.2 : ℕ) : ℤ)))).app
          (basicOpen 𝒜 f.val.1) (1 : Γ(Proj 𝒜, basicOpen 𝒜 f.val.1))) =
        (F ⊗ twist 𝒜 ((m * f.val.2 : ℕ) : ℤ)).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 f.val.1 ≤ ⊤)).op t) ∧
    (∀ (f g : {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2})
      (inc : basicOpen 𝒜 g.val.1 ≤ basicOpen 𝒜 f.val.1)
      (e c : ℕ) (a : S), 0 < e → a ∈ 𝒜 c →
      g.val.1 ^ e = a * f.val.1 → e * g.val.2 = c + f.val.2 →
      ∀ (m : ℕ) (t : Γ(F ⊗ twist 𝒜 ((m * f.val.2 : ℕ) : ℤ), ⊤)) (q : Z f),
      (q : LocalizedModule.Away f.val.1
        (DirectSum ℤ (fun n : ℤ ↦ Γ(F ⊗ twist 𝒜 n, ⊤)))) =
        mk (DirectSum.of (fun n : ℤ ↦ Γ(F ⊗ twist 𝒜 n, ⊤))
          ((m * f.val.2 : ℕ) : ℤ) t)
          (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) →
      (rho f g inc q : LocalizedModule.Away g.val.1
        (DirectSum ℤ (fun n : ℤ ↦ Γ(F ⊗ twist 𝒜 n, ⊤)))) =
        mk (a ^ m • DirectSum.of (fun n : ℤ ↦ Γ(F ⊗ twist 𝒜 n, ⊤))
          ((m * f.val.2 : ℕ) : ℤ) t)
          (⟨g.val.1 ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g.val.1)) ∧
    (∀ (f g : {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2})
      (inc : basicOpen 𝒜 g.val.1 ≤ basicOpen 𝒜 f.val.1) (q : Z f),
      phi g (rho f g inc q) = F.presheaf.map (homOfLE inc).op (phi f q))

/-- Homogeneous fraction evaluation is linear and natural on every standard open,
for an arbitrary module sheaf on a Proj covered by degree-one standard opens.
Source: Stacks Project, constructions.tex, 0B5I, with the explicit chart check of
01MS and 01MT. (blueprint: lem-sfb-proj-section-fraction-naturality).

Proof:
1. The canonical section g and the fraction 1/g have product one on each intersection
   with a degree-one chart, by the fraction multiplication and unit laws of
   lem-sfb-standard-proj-twist-tensor and def-weil-pbc-proj-twisting-sheaf.
   Hence g is a free generator. Its powers give inverse trivializations for F(md).
2. Sum the homogeneous multiplication maps to construct the action on the direct sum.
   The unit and associativity laws of lem-sfb-standard-proj-twist-tensor give the
   module laws. For equality t/g^m = v/g^n, def-weil-pbc-module-localization gives
   g^k(g^n t - g^m v)=0. Restrict and multiply by g^(-k-m-n); the two values agree.
   The localization addition formula gives additivity.
3. For scalars s/g^r, tensor balancing in def-pur-sheaf-tensor-product and associative
   multiplication identify the value of st/g^(r+m) with (s/g^r) times that of t/g^m.
   This gives both scalar closure of the degree-zero subgroup and linearity.
4. For U_g contained in U_h, lem-weil-pbc-proj-graded-module-sheaf-exists and
   lem-weil-pbc-proj-standard-open-inclusion give g^e=ah and restriction
   t/h^m to a^m t/g^(em), independently of e,a. On U_g, both a^m/g^(em) and
   h^(-m) become one after multiplying by h^m. Its invertibility makes them equal.
   Thus evaluation commutes with restriction, by def-weil-sheaf-of-modules-category.
   Every element has a homogeneous fraction representative, so the equations hold
   on the quotient, independently of all representatives and relation witnesses.
   For m=0 use the unit law; for an empty chart use the zero section module.
   This uses no finite generation, quasi-compactness or quasi-coherence.
-/
theorem projSectionFractionNaturality
    (cover : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f)
    (F : (Proj 𝒜).Modules) :
    (∀ (g : S) (d : ℕ) (hd : 0 < d) (hg : g ∈ 𝒜 d),
      IsFreeGenerator ((unitToTwist hg).app (basicOpen 𝒜 g)
        (1 : Γ(Proj 𝒜, basicOpen 𝒜 g)))) ∧
    ∃ m : Module S (DirectSum ℤ (fun n : ℤ ↦ Γ(F ⊗ twist 𝒜 n, ⊤))),
      (∀ (d : ℕ) (n : ℤ) (s : S) (hs : s ∈ 𝒜 d)
        (t : Γ(F ⊗ twist 𝒜 n, ⊤)),
        @SMul.smul S (DirectSum ℤ (fun k : ℤ ↦ Γ(F ⊗ twist 𝒜 k, ⊤))) m.toSMul s
          (DirectSum.of (fun k : ℤ ↦ Γ(F ⊗ twist 𝒜 k, ⊤)) n t) =
          DirectSum.of (fun k : ℤ ↦ Γ(F ⊗ twist 𝒜 k, ⊤)) (n + d)
            ((F ◁ twistMul n hs).app ⊤ t)) ∧
      @IsProjSectionFractionNaturality S _ 𝒜 _ F m := by
  sorry

end AlgebraicGeometry.Proj
