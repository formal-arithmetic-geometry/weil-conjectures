/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-! # Natural additive comparison for acyclic module direct image

Source: Stacks Project, Tags 01F4 (1), 01EY and 03FD.
(blueprint: lem-pc-k2-leray-acyclic-additive-naturality)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- The additive Leray comparison commutes with coefficient endomorphisms.

Source: Stacks Project, cohomology.tex, Tags 01F4 (1) and 01EY;
sites-cohomology.tex, Tag 03FD.
(blueprint: lem-pc-k2-leray-acyclic-additive-naturality)

Proof: Choose an injective resolution I of F in module sheaves. Its underlying
abelian sheaves are flasque. Flasque sheaves are direct-image acyclic: sections
of a short exact sequence beginning in a flasque sheaf are surjective on every
open, direct image therefore preserves that sequence, and a quotient of two
flasque sheaves is flasque. The acyclicity criterion and dimension shifting
prove the assertion. Forgetting coefficients is exact and commutes with direct
image. Thus the same complex p_*I computes the underlying abelian higher direct
images and the module higher direct images. The hypothesis makes all positive
abelian higher images zero. Apply the natural abelian Leray edge of 01F4 (1);
only row zero remains, so its components are additive isomorphisms. Identify
cohomology from the terminal free abelian representable with H: that sheaf is
canonically the constant integer sheaf, since there is a unique map from every
open to the terminal open. Precomposition by this source isomorphism is natural
in the coefficient sheaf, by associativity of Ext composition. Equivalently,
03FD compares the module and abelian resolution computations. Compose these
comparisons with the Leray edge to obtain e. Naturality of the edge and both
comparisons gives the displayed equation for every endomorphism of F. In degree
zero the argument is the identification of global sections; zero coefficients
and the empty scheme require no exceptions. No scalar linearity is asserted. -/
theorem exists_addEquiv_H_pushforward_natural_of_higherDirectImage_vanishing
    {Y X : Scheme.{u}} (p : Y ⟶ X) [HasInjectiveResolutions Y.Modules]
    (F : Y.Modules)
    (hF : ∀ q : ℕ, 0 < q → IsZero ((higherDirectImage p q).obj F)) (q : ℕ) :
    ∃ e : ((pushforward p).obj F).H q ≃+ F.H q,
      ∀ (φ : F ⟶ F) (x : ((pushforward p).obj F).H q),
        e (H.map ((pushforward p).map φ) q x) = H.map φ q (e x) := by sorry

end AlgebraicGeometry.Scheme.Modules
