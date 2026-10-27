module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import Sheaf.AlgebraicGeometry.FpqcAffineDescent
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover
import WeilConjectures.AlgebraicGeometry.FpqcDescendQuasiCompact
import Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality
import Sheaf.FieldTheory.FieldTower
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Rational Picard surjectivity for a torus torsor

Source: Sansuc, Groupe de Brauer et arithmetique des groupes algebriques lineaires
(1981), Proposition 6.10; the finite splitting and norm argument recorded in the DAG.
(blueprint: lem-sfb-torus-torsor-picard-rational-surjectivity)

The torsor is the existing represented right torsor, with no chosen local section.
The conclusion uses tensor inverse image and an actual isomorphism of line modules.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every line on a torus torsor over a smooth separated finite-type geometrically
integral variety has a positive tensor power pulled back from the base.

Source: Sansuc (1981), Proposition 6.10 (local original WANTED); Milne, Algebraic
Groups, Theorem 12.23 and Corollary 12.25; Stacks, Tags 0BCY and 0BD2.
(blueprint: lem-sfb-torus-torsor-picard-rational-surjectivity)

Proof plan:
1. Over the algebraic closure the torus is split, hence affine of finite type.
   The field-extension fpqc cover and fpqc descent of affineness, local finite
   type and quasi-compactness give these properties over k. These are
   lem-pc-field-extension-fpqc-cover, lem-weil-pbc-fpqc-descend-affine,
   lem-weil-pbc-fpqc-descend-locally-finite-type and
   lem-weil-pbc-fpqc-descend-quasi-compact.
2. By lem-sfb-multiplicative-character-antiduality choose a finite separable
   splitting field K/k. The character group over the algebraic closure is Z^r,
   so its diagonalizable group over K is the split rank-r torus. Its degree
   d = [K:k], as in def-pc-field-tower, is positive.
3. Base change the torsor and its action to K. Smoothness, separatedness, finite
   type and finite presentation persist by lem-pc-proper-base-change,
   lem-pod-separated-finite-type-base-change and
   lem-weil-pbc-qcqs-morphism-permanence. Faithful flatness and the torsor square
   persist by lem-sfb-space-fppf-covering-calculus and the universal property of
   def-pc-fibre-product. The resulting torsor satisfies all hypotheses of
   lem-sfb-split-torus-torsor-line-pullback.
4. Pull L to Y_K; it stays invertible by pulling back local trivializations.
   The split-torus lemma gives a line N on X_K with q_K^*N isomorphic to L_K.
   Take M to represent the norm of N. By
   lem-sfb-finite-field-picard-norm-base-change, q^*M has the same line class as
   the norm of L_K, which is L^{tensor d}. Equality of line classes gives the
   required isomorphism; take c = d. The pullbacks here are tensor inverse
   images (def-pc-module-pullback). Geometric integrality is retained, although
   the split-torus input does not need it. -/
theorem torus_torsor_picard_rational_surjectivity
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [Smooth X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [GeometricallyIntegral X.hom]
    (T : Grp (Over (Spec (.of k)))) (hT : MultiplicativeType.IsTorus T)
    (P : RepresentedRightTorsor T X)
    (L : P.space.left.Modules) [L.IsInvertible] :
    ∃ c : ℕ, 1 ≤ c ∧ ∃ M : X.left.Modules, M.IsInvertible ∧
      Nonempty ((Scheme.Modules.tensorPullback P.projection.left).obj M ≅ L.tensorPow c) := by
  sorry

end AlgebraicGeometry
