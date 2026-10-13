/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.Paper.PQFCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Coproduct presentation of the ordinary external direct image

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, degree-zero formula.
(blueprint: lem-sc-picard-external-coefficients-pushforward-coproduct).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- The ordinary direct image of external coefficients is a coproduct of G.
No positive-degree acyclicity of either coefficient is needed.
Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, the degree-zero
case of the displayed derived-direct-image formula.
(blueprint: lem-sc-picard-external-coefficients-pushforward-coproduct).

Proof: Choose a k-basis of Gamma(X,F), indexed by a small type I. Each basis
section defines a map G to pr2_* E: over V send t to the external product of the
basis section with t. The adjunction-unit formulas commute with restrictions and
are O_Y(V)-linear, so these are morphisms of module sheaves. On every affine V,
the finite affine cover of X and affine-diagonal intersections identify sections
of pr2_* E with Gamma(X,F) tensor_k G(V). This is the affine-right external
section comparison; its pure-tensor formula identifies the displayed maps with
basis inclusions. Basis expansion gives the algebraic direct sum of copies of
G(V). The sheaf coproduct is obtained by sheafifying the presheaf coproduct.
Its comparison to pr2_* E is an isomorphism on the affine basis, hence on stalks
and therefore as a sheaf. Transfer the coproduct cofan along this isomorphism.
This uses sheafification, not an assertion about arbitrary sections of an infinite
sheaf coproduct. Zero Gamma(X,F) gives an empty basis and the zero coproduct;
empty schemes and zero G satisfy the same construction. -/
theorem picardExternalCupCoefficients_pushforward_coproduct
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [IsAffineHom (pullback.diagonal f)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    : ∃ (I : Type w)
      (ι : ∀ _ : I, G ⟶ (RingedSpace.moduleDirectImage
        (pullback.snd f g).toLRSHom.toShHom).obj (externalCupCoefficients f g F G)),
      Nonempty (IsColimit (Cofan.mk _ ι)) := by sorry

end AlgebraicGeometry.Scheme.Modules
