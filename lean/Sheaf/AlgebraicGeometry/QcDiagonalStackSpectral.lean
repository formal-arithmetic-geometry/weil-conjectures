module

public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Mathlib.Topology.Spectral.Basic
import Sheaf.AlgebraicGeometry.StackPointTopology

/-! # Spectrality of quasi-compact algebraic stacks with quasi-compact diagonal

Source: Stacks Project, stacks-morphisms.tex, Tags 0DQN and 0DQQ
(blueprint: lem-sfb-qc-diagonal-stack-spectral).

The diagonal is relative to Spec k. The topology is the smooth-atlas topology on the
existing field-object quotient, with no finite-type or separation assumption.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- A quasi-compact algebraic stack over a field with quasi-compact relative diagonal
has a spectral point space, hence is T0 and quasi-compact.
Source: Stacks Project, stacks-morphisms.tex, Tags 0DQN and 0DQQ
(blueprint: lem-sfb-qc-diagonal-stack-spectral).

Proof:
1. A field is a commutative ring (def-weil-field), so Spec k is affine by
   def-weil-affine-spectrum. The quasi-compact smooth surjective atlas is exactly
   IsQuasiCompactModuli (def-sfb-stack-qcqs-morphism). The structural functor below
   is the map to Spec k, so its relative diagonal is precisely X → X ×_k X.
2. Apply lem-sfb-qc-stack-spectral-point-space to this affine base. Its point quotient
   uses the same field objects and common-extension relation. Its smooth-atlas quotient
   topology agrees with moduliSmoothPointTopology by
   lem-sfb-smooth-presentation-closed-subsets and lem-sfb-stack-point-topology: both
   characterize closed subsets by closed inverse image under the same atlas.
   This gives compactness, a basis of compact opens stable under finite intersections,
   and a unique generic point for every nonempty irreducible closed subset.
3. If two points belong to exactly the same opens, their singleton closures agree.
   The closure of a singleton is nonempty irreducible, and both points are generic
   for this closed set. Uniqueness forces equality, giving T0. Compactness is already
   part of spectrality. The empty stack satisfies these assertions as well. -/
theorem qc_diagonal_stack_spectral (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hF : IsAlgebraicModuliStack F) (hqc : IsQuasiCompactModuli F)
    (hdiag : IsQuasiCompactAlgebraicModuliMap.{u, v, w, v, max w u, 0, 0}
      (moduliRelativeDiagonal (moduliBaseStructure F))) :
    @SpectralSpace (ModuliPoints F) (moduliSmoothPointTopology F) := by
  sorry

end CategoryTheory
