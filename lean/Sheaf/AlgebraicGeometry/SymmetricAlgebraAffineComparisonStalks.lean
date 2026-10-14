/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.AlgebraicGeometry.SymmetricAlgebraAffineComparisonMap
import Sheaf.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import Sheaf.RingTheory.SymmetricAlgebraBaseChange

/-! # Stalk comparison on an affine chart for the symmetric algebra

Source: Stacks Project, Modules, Lemma 01CH and Schemes, Lemma 01I8.
(blueprint: lem-weil-pbc-symmetric-algebra-affine-comparison-stalks).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.SymmetricAlgebraSheaf

/-- The tilde comparison is bijective on every stalk of the affine chart.
Source: Stacks Project, Modules, Lemmas 01CG and 01CH; Schemes, Lemma 01I8;
Algebra, Lemma 0C6F. This is step 6 of the affine symmetric algebra comparison.
(blueprint: lem-weil-pbc-symmetric-algebra-affine-comparison-stalks).

Proof: write R = O_X(W), M = F(W), A = Sym_R(M), and S for the restriction of the
ring sheafification to Spec R. For each smaller affine V, quasi-coherent affine section
base change gives F(V) = O(V) tensor_R M. Symmetric algebra base change then gives a
bijection lambda_V : O(V) tensor_R A -> Sym_{O(V)}(F(V)). Tilde section base change
gives a second bijection beta_V : O(V) tensor_R A -> tilde(A)(V). Both send r tensor a
to r times the restriction of a. The comparison alpha satisfies
alpha_V beta_V = theta_V lambda_V: its equality on 1 tensor a follows from the adjunction
and naturality, and linearity gives equality on all tensors. These identifications commute
with restriction, since their formulas agree on pure tensors.
The ring sheafification unit theta is bijective on stalks (forgetting to abelian groups
commutes with sheafification). Affine neighbourhoods inside W are cofinal. For surjectivity
at x, lift a target germ through theta_x, represent the lift on an affine V, write its
representative as lambda_V(c), and use alpha_V(beta_V(c)) as its lift through alpha_x.
For injectivity, represent a source germ on an affine V as beta_V(c). If its image under
alpha_x is zero, injectivity of theta_x makes the germ of lambda_V(c) zero. Restrict to
an affine neighbourhood V' where lambda_V(c) vanishes. Restriction compatibility and
injectivity of lambda_V' force the restricted tensor c' to be zero. Thus beta_V'(c')
is zero, so the original source germ was zero. For two germs with equal images, apply
this zero-kernel argument to their difference. No finiteness or separatedness is used. -/
theorem affineComparison_stalk_bijective {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] {W : X.Opens} (hW : IsAffineOpen W)
    (x : Spec Γ(X, W)) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((Scheme.Modules.toPresheaf (Spec Γ(X, W))).map (affineComparison F hW))) := by sorry

end AlgebraicGeometry.SymmetricAlgebraSheaf
