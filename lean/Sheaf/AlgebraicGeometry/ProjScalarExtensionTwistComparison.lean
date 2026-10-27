/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.RingTheory.HomogeneousLocalizationScalarExtension
import Sheaf.Algebra.Module.GradedLocalizationScalarExtension
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections

/-! # Scalar extension of arbitrary Proj twists

Source: Stacks Project, constructions.tex, Tags 01N2, 01MY and 01MZ
(blueprint: lem-sfb-proj-scalar-extension-twist-comparison).

The fraction normalization is stated using the existing pointwise realization of twists.
Multiplying by the denominator avoids choosing a representative in a localization.
The product law is stated on local sections, which generate the sheaf tensor product.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- Apply a twist comparison to the actual pullback section `1 ⊗ s`.
Source: Stacks 01MY (blueprint: lem-sfb-proj-scalar-extension-twist-comparison). -/
noncomputable def scalarExtensionTwistSection
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (j : ℤ) (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 j, U)) :
    Γ(twist ℬ j, r ⁻¹ᵁ U) :=
  (θ j).hom.app (r ⁻¹ᵁ U) (tensorPullbackSection r (twist 𝒜 j) U s)

/-- The normalized fraction rule for the scalar-extension comparison. A section `s=a/b`
is specified by `b*s=a` where `b` is invertible. For `b=f^m`, this is exactly
`(a/f^m) ⊗ c ↦ c*ψ(a)/ψ(f)^m`. All opens are allowed, so the rule includes further
standard-open restrictions. Source: Stacks 01MY
(blueprint: lem-sfb-proj-scalar-extension-twist-comparison). -/
def IsScalarExtensionTwistComparison
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j) : Prop :=
  ∀ (j : ℤ) (i k : ℕ) (a : A) (b : A), a ∈ 𝒜 i → b ∈ 𝒜 k →
    (i : ℤ) = (k : ℤ) + j →
    ∀ (U : (Proj 𝒜).Opens), U ≤ basicOpen 𝒜 b →
    ∀ (s : Γ(twist 𝒜 j, U)),
      (∀ y : U, (s.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
        Localization.mk b 1 = Localization.mk a 1) →
    ∀ (c : Γ(Proj ℬ, r ⁻¹ᵁ U)) (x : r ⁻¹ᵁ U),
      ((c • scalarExtensionTwistSection r θ j U s).1 x :
        Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * Localization.mk (ψ b) 1 =
        (c.1 x).val * Localization.mk (ψ a) 1

/-- Scalar extension preserves every twist, with its fraction, algebra, section and
composition normalizations. Source: Stacks 01N2(3), 01MY, 01MZ
(blueprint: lem-sfb-proj-scalar-extension-twist-comparison).

Proof: (1) The scalar-extension Proj theorem gives the covering by inverse images of
standard opens. The graded-module sheaf theorem makes both twists quasi-coherent, and
pullback preserves this. The affine pullback-sections theorem identifies the source on
D_+(ψ(f)) with (A_f)_j tensor_(A_f)_0 (B_ψ(f))_0 for every integer j.
(2) The homogeneous localization scalar-extension theorem identifies the second ring
with S tensor_R (A_f)_0. Rebracket u tensor (s tensor h) as s tensor hu, with inverse
s tensor u mapped to u tensor (s tensor 1). The graded-module localization comparison,
followed by β on fractions, gives the isomorphism sending (a/f^m) tensor c to
c ψ(a)/ψ(f)^m. These formulas respect balancing and are inverse on pure tensors.
(3) The affine tilde--sections adjunction turns this into an isomorphism of the two
quasi-coherent sheaves on each chart.
(4) On the fg chart, both restrictions send a/f^m to ψ(a)ψ(g)^m/ψ(fg)^m.
For a general inclusion with g^e=hf, both send it to ψ(h)^mψ(a)/ψ(g)^(em).
Affine adjunction and module-sheaf gluing give the global isomorphism and its uniqueness.
(5) Products give ce ψ(ab)/ψ(f)^(m+n) in both orders. The affine tensor-sections theorem
and the section-normalized pullback--tensor comparison identify this with the sheaf
multiplication square. The unit 1/1 stays 1/1, the degree-zero formula is the structural
pullback identification, and a/1 maps to ψ(a)/1 for every nonnegative degree.
(6) The coefficient associator sends t tensor a to t tensor (1 tensor a), with inverse
t tensor (s tensor a) mapped to ts tensor a. After γ and β this gives the composite
graded algebra isomorphism. Chart uniqueness gives r_(χψ)=r_χ followed by r_ψ.
The normalized pullback-composition map sends ((u tensor b) tensor c) to
u tensor χ(b)c; both twist maps send this to cχ(b)χψ(u). Thus they agree on generators,
and gluing gives composition. For the identity extension the chart formula is u tensor c
mapped to cu, hence the normalized identity-pullback comparison. No flatness, finiteness,
degree-one generation, nonzero denominator, or equality A_0=R is used. -/
theorem scalarExtension_twist_comparison
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (ρA : R →+* 𝒜 0) (ρB : S →+* ℬ 0)
    (hρA : ∀ a : R, (ρA a : A) = algebraMap R A a)
    (hρB : ∀ b : S, (ρB b : B) = algebraMap S B b)
    (β : TensorProduct R S A ≃ₐ[S] B) (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A)))
    (r : Proj ℬ ⟶ Proj 𝒜)
    (hpre : ∀ (n : ℕ) (f : A), f ∈ 𝒜 n → 0 < n →
      r ⁻¹ᵁ basicOpen 𝒜 f = basicOpen ℬ (ψ f))
    (hchart : ∀ (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n),
      awayι ℬ (ψ f) (ψ.map_mem hf) hn ≫ r =
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f)) ≫
          awayι 𝒜 f hf hn) :
    ∃ θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j,
      IsScalarExtensionTwistComparison ψ r θ ∧
      (∀ θ' : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j,
        IsScalarExtensionTwistComparison ψ r θ' → θ' = θ) ∧
      (∀ (i j : ℤ) (U : (Proj 𝒜).Opens)
        (s : Γ(twist 𝒜 i, U)) (t : Γ(twist 𝒜 j, U))
        (v : Γ(twist 𝒜 (i + j), U)),
        (∀ x : U, (v.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
          (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * t.1 x) →
        ∀ x : r ⁻¹ᵁ U,
          ((scalarExtensionTwistSection r θ (i + j) U v).1 x :
            Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
          ((scalarExtensionTwistSection r θ i U s).1 x :
            Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
          (scalarExtensionTwistSection r θ j U t).1 x) ∧
      (∀ (U : (Proj 𝒜).Opens) (s : Γ(Proj 𝒜, U)),
        scalarExtensionTwistSection r θ 0 U
          (Scheme.Modules.Hom.app (unitToTwistZero (𝒜 := 𝒜)) U s) =
          Scheme.Modules.Hom.app (unitToTwistZero (𝒜 := ℬ)) (r ⁻¹ᵁ U) (r.app U s)) ∧
      (∀ (n : ℕ) (a : A) (ha : a ∈ 𝒜 n),
        scalarExtensionTwistSection r θ (0 + n) ⊤
          ((unitToTwist ha).app ⊤ (1 : Γ(Proj 𝒜, ⊤))) =
          (twist ℬ (0 + n)).presheaf.map
            (homOfLE (le_top : r ⁻¹ᵁ ⊤ ≤ ⊤)).op
            ((unitToTwist (ψ.map_mem ha)).app ⊤ (1 : Γ(Proj ℬ, ⊤)))) ∧
      (∀ {T C : Type u} [CommRing T] [CommRing C]
        [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Algebra T C]
        (𝒞 : ℕ → Submodule T C) [GradedRing 𝒞]
        (γ : TensorProduct S T B ≃ₐ[T] C) (χ : ℬ →+*ᵍ 𝒞),
        (∀ b : B, γ (TensorProduct.tmul S (1 : T) b) = χ b) →
        (∀ n : ℕ, 𝒞 n = Submodule.span T (χ '' (ℬ n : Set B))) →
        (∃ δ : TensorProduct R T A ≃ₐ[T] C,
          (∀ (t : T) (a : A), δ (TensorProduct.tmul R t a) = t • χ (ψ a)) ∧
          (∀ n : ℕ, 𝒞 n = Submodule.span T ((χ.comp ψ) '' (𝒜 n : Set A)))) ∧
        ∀ (q : Proj 𝒞 ⟶ Proj ℬ) (p : Proj 𝒞 ⟶ Proj 𝒜),
          (∀ (n : ℕ) (f : B) (hf : f ∈ ℬ n) (hn : 0 < n),
            awayι 𝒞 (χ f) (χ.map_mem hf) hn ≫ q =
              Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map χ f)) ≫
                awayι ℬ f hf hn) →
          (∀ (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n),
            awayι 𝒞 (χ (ψ f)) ((χ.comp ψ).map_mem hf) hn ≫ p =
              Spec.map (CommRingCat.ofHom
                (HomogeneousLocalization.Away.map (χ.comp ψ) f)) ≫ awayι 𝒜 f hf hn) →
          ∀ (η : ∀ j : ℤ, (tensorPullback q).obj (twist ℬ j) ≅ twist 𝒞 j)
            (ζ : ∀ j : ℤ, (tensorPullback p).obj (twist 𝒜 j) ≅ twist 𝒞 j),
            IsScalarExtensionTwistComparison χ q η →
            IsScalarExtensionTwistComparison (χ.comp ψ) p ζ →
            ∃ hp : p = q ≫ r, ∀ j : ℤ,
              ζ j = eqToIso (congrArg (fun f ↦ (tensorPullback f).obj (twist 𝒜 j)) hp) ≪≫
                (tensorPullbackSectionComp q r).app (twist 𝒜 j) ≪≫
                (tensorPullback q).mapIso (θ j) ≪≫ η j) ∧
      (∀ ι : ∀ j : ℤ, (tensorPullback (𝟙 (Proj 𝒜))).obj (twist 𝒜 j) ≅ twist 𝒜 j,
        IsScalarExtensionTwistComparison (GradedRingHom.id 𝒜) (𝟙 (Proj 𝒜)) ι →
        ∀ j : ℤ, ι j = (tensorPullbackSectionId (Proj 𝒜)).app (twist 𝒜 j)) := by
  sorry

end AlgebraicGeometry.Proj
