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
import Sheaf.AlgebraicGeometry.ScalarCupPullbackCoefficientNaturality
import Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackSquare

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
Unfold externalCup as the cup of the two projection pullbacks, and unfold
externalCupPullbackIso as the normalized tensor-pullback comparison followed by
the tensor of the two projection-square comparisons. Associativity, h₁ and hu show
that w is over k. Apply scalarCup_pullback_coefficient_naturality to w and the
homomorphisms of the two square comparisons. The result is the cup of the two
coefficient-adjusted pullbacks. Apply scalarCohomologyPullback_square to the first
projection using h₁ and hu, and to the second using h₂ and hv. For the second
projection the structure-map equalities are the fibre-product condition. These
two identities give exactly the two projection pullbacks defining the external
cup on X' ×ₖ Y'. The normalization and Ext-comparison arguments are isolated in
those two generic scalar identities; no inverse Cech comparison is used here.
The degree-zero identities are the section tensor and composition formulas;
zero coefficients or empty schemes give zero on both sides.
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
  intro X' Y' f' g' u v hu hv w h₁ h₂ p q a b
  have hw : w ≫ (Limits.pullback.fst f g ≫ f) = Limits.pullback.fst f' g' ≫ f' := by
    rw [← Category.assoc, h₁, Category.assoc, hu]
  simp only [externalCup, externalCupPullbackIso, Iso.trans_hom, tensorIso_hom]
  erw [scalarCup_pullback_coefficient_naturality k _ _ _ _ w hw]
  erw [scalarCohomologyPullback_square k _ _ _ _
    (Limits.pullback.fst f' g' ≫ f') (Limits.pullback.fst f g ≫ f) f' f
    w (Limits.pullback.fst f g) (Limits.pullback.fst f' g') u
    hw rfl rfl hu h₁ F p a]
  erw [scalarCohomologyPullback_square k _ _ _ _
    (Limits.pullback.fst f' g' ≫ f') (Limits.pullback.fst f g ≫ f) g' g
    w (Limits.pullback.snd f g) (Limits.pullback.snd f' g') v
    hw Limits.pullback.condition.symm Limits.pullback.condition.symm hv h₂ G q b]
end
end AlgebraicGeometry.Scheme.Modules
