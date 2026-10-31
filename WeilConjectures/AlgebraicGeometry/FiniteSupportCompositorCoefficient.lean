/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteAdjointCompositorTransposes

/-! # Coefficient compatibility of normalized finite compositors

Source: smooth-purity composition comparisons proof (2), proper/open coefficient pasting.
(blueprint: lem-sp-finite-support-compositor-coefficient).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- The left coefficient equation for any compositors with the recorded site normalization.
Source: blueprint det-sp-composition-comparisons, proof (2), coefficient/site pasting.
(blueprint: lem-sp-finite-support-compositor-coefficient).

Proof: Choose a bounded constructible etale origin L of M. It has the same Tor interval:
exact comparison pullback commutes with tensor, and its invertible unit detects zero
cohomology sheaves. Apply the composition equation of
lem-sp-et-proet-coefficient-compatibility to L. The normalization fields of DA and DB,
finite compact-site coherence, and the canonical scalar/site comparison identify its
compositors with the two displayed alpha maps. The refinement equation permits the
three specified compactifications, without a compatibility assumption on their choices.
Cancel the scalar/site comparison isomorphisms. Naturality along the origin isomorphism
then gives the stated equation for M. All arrows retain their B-module action; no
flatness or finite projective dimension of B over A is used.
-/
theorem finiteSupportCompositor_coefficient
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
  [QuasiCompact (Z ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    [QuasiCompact f] [QuasiCompact g]
    (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime] (_hpℓ : p ≠ ℓ) [CharP k p]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (DA : FiniteAdjointCompositorDatum A cf cg ch)
    (DB : FiniteAdjointCompositorDatum B cf cg ch)
    (hSX : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj M.obj))
    (M : spFiniteConstructibleTorCategory X A) :
    (scalarExtensionFunctor φ Z).map (DA.alpha.hom.app M).hom ≫
        (reductionDirectImageComparison φ ch.i ch.g).app M.obj =
      (reductionDirectImageComparison φ cg.i cg.g).app
          ((finiteAdjointSupport A cf DA.hFf).obj M).obj ≫
        (reductionCompactSupport B cg.i cg.g).map
          ((reductionDirectImageComparison φ cf.i cf.g).app M.obj) ≫
        (DB.alpha.hom.app ((reductionCtfScalar φ X hSX).obj M)).hom := by sorry

end AlgebraicGeometry.ProEtale
