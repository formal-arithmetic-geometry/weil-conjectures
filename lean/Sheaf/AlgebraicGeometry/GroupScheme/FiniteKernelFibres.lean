/-
Copyright (c) 2026 NW. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NW
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism

/-!
# Finite kernels give finite scheme-theoretic fibres

Source: Milne, Abelian Varieties, Chapter I, Proposition 7.1, printed p.32,
first proof paragraph; Stacks Project, Tags 01WL, 02LA and 02NU
(blueprint: lem-sfb-finite-kernel-group-fibres).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A homomorphism of finite-type group schemes over a field with finite scheme-theoretic
kernel has finite scheme-theoretic fibres, of topological Krull dimension at most zero.
Source: Milne, Abelian Varieties, I, Proposition 7.1, printed p.32, first proof paragraph
(blueprint: lem-sfb-finite-kernel-group-fibres).

Proof:
1. Fix y, put F = κ(y) and P = G_y. If P is empty, it is Spec of the zero F-algebra,
   hence finite over F, and its dimension is bottom. Otherwise take z in P and L = κ(z).
   The canonical map Spec L to P supplies an L-point x of G mapping to y_L in H.
   This uses the scheme fibre and residue field definitions; no F-rational point is needed.
2. The group law defines mutually inverse scheme morphisms K_L to P_L and P_L to K_L
   by a ↦ xa and b ↦ x⁻¹b. The homomorphism diagrams give u(xa) = y_L and
   u(x⁻¹b) = e, so the pullback universal properties give these factorizations as
   scheme morphisms, including nilpotents. Associativity, unit and inverse diagrams
   show that the composites are identities. Thus P_L is isomorphic over L to K_L.
3. By lem-weil-pbc-finite-morphism-permanence (a), Stacks Tag 01WL, K_L is finite
   over L. The isomorphism transfers affineness and finiteness of coordinate algebras
   to P_L, which is therefore finite over L.
4. Spec L to Spec F is an fpqc covering: the field inclusion is flat (an F-basis
   expresses tensoring with L as a direct sum of identity functors), and both spectra
   have one point and are affine. This is def-weil-pbc-fpqc-covering. Apply
   lem-weil-pbc-fpqc-descend-finite (Stacks Tag 02LA) to descend finiteness to P over F.
5. Apply pqf-lem-finite-qf to P to Spec F. By pqf-def-quasifinite, every point is
   isolated in its fibre, which is P itself. Thus P is discrete. Each nonempty
   irreducible closed subset is a singleton, so no strict chain has positive length.
   By def-kun-topological-krull-dimension, dim P ≤ 0, also when P is empty. -/
theorem isFinite_fiber_and_krullDim_le_zero_of_isFinite_kernel
    {k : Type u} [Field k] {G H : Over (Spec (.of k))} [GrpObj G] [GrpObj H]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    (f : G ⟶ H) [IsMonHom f] [IsFinite (GrpObj.ker f).hom] (y : H.left) :
    IsFinite (f.left.fiberToSpecResidueField y) ∧
      topologicalKrullDim (f.left.fiber y) ≤ 0 := sorry

end AlgebraicGeometry
