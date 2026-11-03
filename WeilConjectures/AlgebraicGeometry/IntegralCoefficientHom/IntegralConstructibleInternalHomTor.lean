/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientHom.IntegralConstructibleInternalHomData

/-! # Admissible finite-quotient Hom estimate

The helper refines the corresponding step of `cor-coef-integral-internal-hom`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralCoefficientHom
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]


/-- Constructibility and quantitative Tor bounds for finite-quotient internal Hom.
Source: latest blueprint `cor-coef-integral-internal-hom.proof.md`, sentences 2--3;
`lem-coef-integral-residue-tor` and `cor-weil-finite-constructible-hom`.
(blueprint: lem-coef-admissible-finite-hom-bound).

Proof: transport the actual quotient maps through the admissible coefficient
isomorphism, including associates of a standard uniformizer. Finite type makes X
Noetherian. The integral residue-Tor theorem gives finite Tor amplitude of all input
reductions. Positive reduction constructibility makes them bounded constructible.
The finite discrete coefficient equivalence provides ordinary module sheaves and
etale origins and preserves these properties. Apply finite constructible Hom in the
standing field setting, using conservative algebraic-closure pullback in the finite
field case. This gives bounded constructibility of every finite Hom. For the second
clause use the supplied Tor intervals themselves in the quantitative part of that
same finite-Hom theorem, obtaining [c-b-2d,e-a+2d]. The strong monoidal coefficient
encoding preserves closed Hom by uniqueness of the tensor right adjoint. Reflect
constructibility and tensor vanishing through these exact equivalences. No property
of the integral Hom or its comparison is used, so this estimate is independent of
the canonical integral Hom reduction. Empty schemes and zero objects are included. -/
theorem admissible_finite_hom_bound
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (_hk : Finite k ∨ IsAlgClosed k) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ p)
    (_hR :
      Nonempty (Mon.mk (Profinite.continuousCoefficientRingObj R) ≅
        Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      ∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk (Profinite.continuousCoefficientRingObj R) ≅
          Mon.mk (Profinite.padicIntegersRingObj ℓ E)))
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (π : R) (_hπ : Irreducible π)
    (K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X)))
    (_hK : boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X) K)
    (_hL : boundedConstructible
      (condensedRingObj (Profinite.continuousCoefficientRingObj R) X) L)
    :
    (∀ (n : ℕ), 1 ≤ n →
      boundedConstructible
        (condensedRingObj
          (Profinite.continuousCoefficientRingObj (R ⧸ Ideal.span ({π ^ n} : Set R))) X)
        (((CondensedRing.derivedHom
          (Profinite.continuousCoefficientRingObj (R ⧸ Ideal.span ({π ^ n} : Set R))) X).obj
            (op ((reduction R X π n).obj K))).obj ((reduction R X π n).obj L))) ∧
    ∀ (a b c e : ℤ), a ≤ b → c ≤ e →
      ∀ (d : ℕ), topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
        (∀ (n : ℕ), 1 ≤ n → _root_.DerivedCategory.torAmplitudeIn _ a b
          ((reduction R X π n).obj K)) →
        (∀ (n : ℕ), 1 ≤ n → _root_.DerivedCategory.torAmplitudeIn _ c e
          ((reduction R X π n).obj L)) →
        ∀ (n : ℕ), 1 ≤ n → _root_.DerivedCategory.torAmplitudeIn _
          (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ))
          (((CondensedRing.derivedHom
            (Profinite.continuousCoefficientRingObj (R ⧸ Ideal.span ({π ^ n} : Set R))) X).obj
              (op ((reduction R X π n).obj K))).obj ((reduction R X π n).obj L)) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralCoefficientHom
