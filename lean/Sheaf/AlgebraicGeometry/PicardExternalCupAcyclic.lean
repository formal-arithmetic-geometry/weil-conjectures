/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.PicardExternalCupCochain
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Acyclic base case for external cup

Source: Stacks Project, Varieties, Tag 0BED, proof of lemma-kunneth.
(blueprint: lem-sc-picard-external-cup-acyclic).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- The normalized external cup comparison is invertible when both coefficients are acyclic.
Source: Stacks Project, Varieties, Tag 0BED, acyclic base case after
`equation-kunneth-on-cech` (blueprint: lem-sc-picard-external-cup-acyclic).

Proof: Choose finite affine covers of X and Y. Affine diagonal makes their finite
intersections affine, as well as the intersections in the product cover. The affine
pullback and tensor section formulas identify the Cech complex on X times an affine
open V of Y with Cech(X,F) tensor G(V). Exactness of tensor over k and affine Cech
comparison show that its positive cohomology vanishes and its degree-zero cohomology
is Gamma(X,F) tensor G(V). The higher-direct-image presheaf description on the affine
basis gives R^q pr2_* externalCupCoefficients = 0 for q>0, and identifies pr2_* with
Gamma(X,F) tensor G, naturally in the affine opens. Choose a basis of Gamma(X,F);
this identifies that sheaf with a direct sum of copies of G. Affine diagonal implies
quasi-separatedness, so direct-sum cohomology on qcqs Y makes it acyclic. Leray gives
zero positive product cohomology and Gamma(X,F) tensor Gamma(Y,G) in degree zero.
The section comparison sends s tensor t to the tensor of their projection pullbacks;
this is the affine section tensor isomorphism, checked on each product affine open.
The natural-degree tensor Kunneth theorem and picardScalarModelEquiv identify the
source homology with the same degree-zero tensor, and with zero in positive degrees.
Lift degree-zero homology elements through the surjective homology projections.
Its tensor-cycle formula and hc identify the degree-zero homology map of c with
that section comparison. Linearity extends equality from pure tensors. Thus it is
invertible in degree zero and between zero objects in positive degrees. No dimension
or nonemptiness hypothesis is needed: zero coefficients and empty schemes give zero
section tensors and zero homology. -/
theorem picardExternalCupCochain_isIso_of_acyclic
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hF : ∀ p : ℕ, 0 < p →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F))
    (hG : ∀ p : ℕ, 0 < p →
      IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj G))
    (c : picardExternalTotal f g F G ⟶
      picardScalarModel (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
    (hc : IsPicardExternalCupCochain f g F G c) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap c (n : ℤ)) := by sorry

end AlgebraicGeometry.Scheme.Modules
