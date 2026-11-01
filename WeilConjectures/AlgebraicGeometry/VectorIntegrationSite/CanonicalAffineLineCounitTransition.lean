/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.IntegrationProjectiveExponentSquare
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.CanonicalAffineTowerCounitTransition

/-! # Canonical affine-line counit transition

One-coordinate case of the root transition of the ordered affine counit, for the
canonical twist transports and projective-line data.
Source: blueprint thm-amb-vector-bundle-purity, proof, paragraph 2 (affine-space counit,
affine-line open triangle); Stacks Tags 03PK, 03Q1.
(blueprint: lem-pur-canonical-affine-line-counit-transition)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

attribute [local implicit_reducible] affineTraceTower affineTraceProjection

private theorem counitTowerOne {C : ℕ → Type*} [∀ d, Category (C d)]
    {L : ∀ d, C (d + 1) ⥤ C d} {R : ∀ d, C d ⥤ C (d + 1)}
    (a : ∀ d, L d ⊣ R d) (K : C 0) :
    (Etale.affineTraceAdjunctionTower a 1).counit.app K = (a 0).counit.app K := by
  change (a 0).counit.app K ≫ 𝟙 K = (a 0).counit.app K
  exact Category.comp_id _

/-- On the affine line over T, the root transition z (coefficient descent at s, pullback of
`baseExponentComparison` along A¹_T → T, inverse coefficient descent at r) followed by the
affine-line counit at exponent r equals the affine-line counit at exponent s, at the unit
coefficient complex, for the canonical transports and projective-line data.
Source: blueprint thm-amb-vector-bundle-purity, proof, paragraph 2; Stacks 03PK, 03Q1.
(blueprint: lem-pur-canonical-affine-line-counit-transition)

Proof: specialize `canonicalAffineTowerCounitTransition` to length one. Unfold the literal
ordered adjunction: its zero stage is the identity adjunction, so its length-one counit
is precisely the line counit. Simplify the length-one projection by the identity law.
The tower theorem independently proves the projective trace transition, open-counit
naturality, and compatibility of the ordered coefficient descent. -/
theorem canonicalAffineLineCounitTransition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (Etale.affineTraceLineLeft (Scheme.finiteTateCoefficient l E n) T).map
      ((Etale.affineLinearCoefficientDescent _ (l ^ (s + 1)) hs
          (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hs) T
          (by simpa only [Nat.cast_pow] using hT.pow (s + 1)) 1).hom ≫
        (Etale.ordinaryFinitePullback _ (AffineSpace PUnit.{u + 1} T ↘ T)).map
          (baseExponentComparison l E n T hT r s hrs hr hs 1).hom ≫
        (Etale.affineLinearCoefficientDescent _ (l ^ (r + 1)) hr
          (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hr) T
          (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) 1).inv) ≫
      (Etale.affineTraceLineAdjunction _ (l ^ (r + 1)) hr
        (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hr)
        T (by simpa only [Nat.cast_pow] using hT.pow (r + 1))
        (Etale.projectiveLineTraceDatum _ (pow_pos (Fact.out : l.Prime).pos _) _ hr T
          (by simpa only [Nat.cast_pow] using hT.pow (r + 1)))).counit.app
        (Etale.ordinaryFiniteUnit _ T) =
    (Etale.affineTraceLineAdjunction _ (l ^ (s + 1)) hs
      (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hs)
      T (by simpa only [Nat.cast_pow] using hT.pow (s + 1))
      (Etale.projectiveLineTraceDatum _ (pow_pos (Fact.out : l.Prime).pos _) _ hs T
        (by simpa only [Nat.cast_pow] using hT.pow (s + 1)))).counit.app
      (Etale.ordinaryFiniteUnit _ T) := by
  have h := canonicalAffineTowerCounitTransition l E n T hT r s hrs hr hs 1
  unfold Etale.affineTraceCounit Etale.affineTraceAdjunction at h
  rw [counitTowerOne, counitTowerOne] at h
  with_unfolding_all exact h

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
