/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.DirectSum.Module
import Sheaf.AlgebraicGeometry.ModuleCechComparisonIsoAffine
import Sheaf.AlgebraicGeometry.ModulePullbackTensor
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.Paper.CechCupPullbackCompat

/-! # Pullback compatibility of the quasi-coherent external cup product

(blueprint: lem-sc-picard-kunneth-qcoh-functoriality).
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct DirectSum

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false

/-- Pullback compatibility of the quasi-coherent external cup product.
Source: Stacks Project, Varieties, Tag 0BED, Lemma varieties-lemma-kunneth.
Also Cohomology, Tags 01FD and 07MB (pullback and cup compatibility).
(blueprint: lem-sc-picard-kunneth-qcoh-functoriality).

Proof:
1. Functoriality. Let u:X'\to X and v:Y'\to Y be morphisms of schemes over k and w = u x_k v :
X' x_k Y' \to X x_k Y, so that pr_1 o w = u o pr_1' and pr_2 o w = v o pr_2'
(def-pc-fibre-product); identify w^*(pr_1^*F tensor pr_2^*G) with pr_1'^*u^*F tensor pr_2'^*v^*G
by lem-pc-module-pullback-identity-composition and lem-weil-pbc-module-pullback-tensor. The
claim is w^*(pr_1^*a cup pr_2^*b) = pr_1'^*u^*a cup pr_2'^*v^*b for a in H^p(X,F), b in
H^q(Y,G). With U, V, W as in Step 1, a = c_U(alpha) and b = c_V(beta) for Cech cocycles alpha,
beta (lem-sc-cech-comparison-map-iso-affine). Use the covers u^{-1}U, v^{-1}V and W' = w^{-1}W,
which refines pr_1'^{-1}u^{-1}U and pr_2'^{-1}v^{-1}V by (i,j) \mapsto i, j since w^{-1}(U_i x
V_j) is contained in w^{-1}pr_1^{-1}U_i = pr_1'^{-1}u^{-1}U_i. By
lem-sc-picard-cech-cup-pullback-compat (a), each pullback in the claim is computed by the
refinement cochain map, whose components are pullbacks of sections; by
lem-pc-module-pullback-identity-composition the cochains obtained from alpha along w after pr_1
and along pr_1' after u coincide (both are pullback of the components along pr_1 o w = u o
pr_1'), and likewise for beta. By lem-weil-pbc-module-pullback-tensor (w^*(s tensor t) = w^*s
tensor w^*t) the refinement cochain map along w sends the signed Cech cup product of two
cochains to the cup product of their images. By lem-sc-picard-cech-cup-pullback-compat (b) the
Cech cup products induce the sheaf cup products on X x_k Y and on X' x_k Y'. Hence both sides of
the claim are c_{W'} of the same cochain, which proves the functoriality clause.

The scalar Ext comparison transports the injective-resolution cup and pullback
operations to the recorded module cohomology. Their sectionwise coefficient maps
are the tensor pairing and the normalized pullback unit. Consequently the Cech
compatibility formulas apply to scalarCohomologyPullback and scalarCohomologyCup,
and their composition computes externalCup. No comparison isomorphism on X' or Y'
is required: the refinement comparison commutes with pullback on arbitrary covers.
The canonical maps are k-linear. In degree zero this is the section tensor map;
zero modules and empty schemes give zero groups on both sides.
-/
theorem picard_kunneth_functoriality (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [CompactSpace Y]
    [IsAffineHom (Limits.pullback.diagonal f)] [IsAffineHom (Limits.pullback.diagonal g)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    ∀ (X' Y' : Scheme.{w}) (f' : X' ⟶ Spec (CommRingCat.of k))
      (g' : Y' ⟶ Spec (CommRingCat.of k)) (u : X' ⟶ X) (v : Y' ⟶ Y)
      (hu : u ≫ f = f') (hv : v ≫ g = g') (w : Limits.pullback f' g' ⟶ Limits.pullback f g)
      (h₁ : w ≫ Limits.pullback.fst f g = Limits.pullback.fst f' g' ≫ u)
      (h₂ : w ≫ Limits.pullback.snd f g = Limits.pullback.snd f' g' ≫ v)
      (p q : ℕ) (a : scalarCohomology f F p) (b : scalarCohomology g G q),
      scalarCohomologyMap (Limits.pullback.fst f' g' ≫ f')
        (externalCupPullbackIso f g f' g' u v w h₁ h₂ F G).hom (p + q)
        (scalarCohomologyPullback (Limits.pullback.fst f g ≫ f) (Limits.pullback.fst f' g' ≫ f') w
          (by rw [← Category.assoc, h₁, Category.assoc, hu])
          (externalCupCoefficients f g F G) (p + q) (externalCup f g F G p q a b)) =
        externalCup f' g' ((tensorPullback u).obj F) ((tensorPullback v).obj G) p q
          (scalarCohomologyPullback f f' u hu F p a)
          (scalarCohomologyPullback g g' v hv G q b) := by
  sorry
end
end AlgebraicGeometry.Scheme.Modules
