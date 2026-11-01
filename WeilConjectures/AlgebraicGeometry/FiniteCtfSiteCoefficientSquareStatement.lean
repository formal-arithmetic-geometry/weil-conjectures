/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Finite coefficient site transport for the intrinsic compact-support comparison

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-exceptional.proof.md`, Charts
(blueprint: lem-sp-finite-ctf-site-coefficient-square).

The ambient functors and the coefficient arrow are the recorded intrinsic
`scalarExtensionFunctor`, `reductionCompactSupport`, and `reductionDirectImageComparison`.
Etale presentations use the existing ULift coefficient and sfIntrinsicDerivedEquivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

/-- The five-factor finite-site computation of the specified intrinsic coefficient map.
Here `reductionSiteCompactSupportIso` is oriented F C to C F; its inverse is the
counit-normalized proper site comparison followed by the exact open comparison.
The proofs of lower boundedness only allow evaluating that existing D+ comparison;
they choose neither a scalar arrow nor a realization.
Source: latest blueprint, exceptional reduction, Charts; Stacks 09A6, 09AF, 07A7,
0D6D and 0GL1 (blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfSiteCoefficientTransport
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (r : Z ⟶ Y) [IsProper r]
    (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X)
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (hLB : _root_.DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj L)) :
    (scalarExtensionFunctor φ Y).obj
        ((reductionCompactSupport A j r).obj ((reductionSite A X).obj L)) ⟶
      (reductionCompactSupport B j r).obj
        ((scalarExtensionFunctor φ X).obj ((reductionSite A X).obj L)) :=
  (scalarExtensionFunctor φ Y).map
      ((reductionSiteCompactSupportIso A j r).hom.app ⟨L, hL⟩) ≫
    (reductionSiteScalarIso φ Y).hom.app
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (⟨Z, r, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ r))).obj L) ≫
    (reductionSite B Y).map
      ((Etale.compactScalarMap (RingHom.ulift.{u + 1, u + 1, u, u} φ)
        (⟨Z, r, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ r))).app L) ≫
    (reductionSiteCompactSupportIso B j r).inv.app
      ⟨(Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj L, hLB⟩ ≫
    (reductionCompactSupport B j r).map ((reductionSiteScalarIso φ X).inv.app L)

/-- Finite-site computation agrees with the specified intrinsic pro-etale proper/open
coefficient map, for every etale presentation and naturally in the intrinsic input.
Source: latest blueprint, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-exceptional.proof.md`, Charts
(blueprint: lem-sp-finite-ctf-site-coefficient-square).

Proof: (1) The finite-ctf site equivalence, followed by sfIntrinsicDerivedEquivalence,
gives etale presentations with ULift coefficients. The common Tor interval of L,
tested on the degree-zero B-module sheaf, bounds its scalar extension L_B. Thus
both displayed lower-bound witnesses exist, without flatness or finite projective
dimension of B. Exact open extension preserves their lower bounds. Properness
makes r qcqs. (2) The proper site comparison is the counit-normalized mate and is
invertible at these bounded-below inputs; the exact open comparison is invertible.
Their existing composite is reductionSiteCompactSupportIso in the reverse direction.
Its realization factors are fixed by sfIntrinsicDerivedEquivalence and the uniquely
section-normalized direct-image comparison, so they introduce no arbitrary map.
(3) Express the inverse open site and scalar-balancing maps by their open-unit
adjuncts. (4) The normalized scalar/site/pullback cube identifies those adjuncts;
injectivity of the B-linear open adjunction gives the open square. (5) The proper
scalar/site mate equation applies at j_!L and its bounded-below scalar extension.
The intrinsic proper scalar map in reductionDirectImageComparison is exactly the
B-linear transpose of extension of the A-counit. The existing realization and site
comparisons preserve that counit normalization. (6) Paste the proper and open
squares. Naturality of the proper mate and open balancing gives T_Y(c_A), then
b(C_X L), then F_B(delta_X), equal to delta_Y, C_Y(beta), then c_B. (7) Invert only
c_A and delta_X and conjugate by the given eta. This yields the five-factor formula
for the actual reductionDirectImageComparison at M. All presentations equal this
same morphism, proving independence. Naturality of the actual ambient natural
transformation gives the final equation. Proof irrelevance removes any dependence
on the two lower-bound witnesses. -/
theorem finiteCtfSiteCoefficientSquare_statement
    {p ell : ℕ} (_hp : p.Prime) (_hell : ell.Prime)
    (k : Type u) [Field k] [CharP k p]
    (_hfield : Finite k ∨ IsAlgClosed k) (_hpell : p ≠ ell)
    {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (j : X ⟶ Z) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (r : Z ⟶ Y) [IsProper r] [r.IsOver (Spec (.of k))] (_hf : j ≫ r = f)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    (M : proEtaleDerivedCategory X A) (_hM : spFiniteConstructibleTor X A M) :
    (∀ (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X)
      (_hctf : Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X L)
      (η : (reductionSite A X).obj L ≅ M),
      ∃ (hL : _root_.DerivedCategory.TStructure.t.plus L)
        (hLB : _root_.DerivedCategory.TStructure.t.plus
          ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj L)),
        IsIso ((reductionSiteCompactSupportIso A j r).inv.app ⟨L, hL⟩) ∧
        IsIso ((reductionSiteCompactSupportIso B j r).inv.app
          ⟨(Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj L, hLB⟩) ∧
        (reductionDirectImageComparison φ j r).app M =
          (scalarExtensionFunctor φ Y).map ((reductionCompactSupport A j r).map η.inv) ≫
          finiteCtfSiteCoefficientTransport φ j r L hL hLB ≫
          (reductionCompactSupport B j r).map ((scalarExtensionFunctor φ X).map η.hom)) ∧
    ∀ (M' : proEtaleDerivedCategory X A) (_hM' : spFiniteConstructibleTor X A M')
      (g : M ⟶ M'),
      (scalarExtensionFunctor φ Y).map ((reductionCompactSupport A j r).map g) ≫
          (reductionDirectImageComparison φ j r).app M' =
        (reductionDirectImageComparison φ j r).app M ≫
          (reductionCompactSupport B j r).map ((scalarExtensionFunctor φ X).map g) := by
  sorry

end AlgebraicGeometry
