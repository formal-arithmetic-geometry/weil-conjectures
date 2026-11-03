/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineSiteScalarMiddle

/-! # The unshifted tensor, Tate and pullback site comparison

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`, Charts.
(blueprint: lem-sp-finite-affine-site-transport-left). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Compatibility of the tensor, Tate and pullback comparisons before shifting.

Source: Charts, site transport in the latest reduction-exceptional proof
(blueprint: lem-sp-finite-affine-site-transport-left).
Proof: choose flat-term K-flat representatives. The scalar/site and scalar/pullback
mates are the balanced B-linear chain maps. The tensor comparison is the same
signed total tensor map on the two sites, and the finite Tate balancing square
commutes by its ordinary root-tensor formula. Pasting these three squares and
localizing gives the displayed equality. No shift coherence is used here. -/
theorem finiteAffineSiteTransportLeft
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) (_hN : 0 < N) (_hX : IsUnit (N : Γ(X, ⊤)))
    (K : DerivedCategoryModule A S) :
    siteProPreScalar φ N hA hB f d
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj K) ≫
      (siteProPreOperation B N hB f d).map ((finiteAffineSiteScalarIso φ S).hom.app K) ≫
      (sitePreComparison B N hB f d).hom.app ((scalarExtension φ S).obj K) =
    L(ProEtale.sheafExtendScalars φ X).map ((sitePreComparison A N hA f d).hom.app K) ≫
      (finiteAffineSiteScalarIso φ X).hom.app ((siteEtalePreOperation A N hA f d).obj K) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
        (siteEtalePreScalar φ N hA hB f d K) := by
  sorry

end AlgebraicGeometry.Etale
