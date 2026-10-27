/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.CoherentZeroDimensionalSupport
import Sheaf.AlgebraicGeometry.SectionAffineOpenKillsCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-! # An affine section gives vanishing of ideal twists on a proper integral curve

Source: Stacks Project, Varieties, Tag 0B5X, lemma-ample-curve, third proof paragraph
(blueprint: lem-trf-affine-section-ideal-twist-h1-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- A nonzero section with affine nonvanishing open on a proper integral curve gives a
positive multiple of its degree for which every specified quasi-coherent ideal twist has
vanishing first cohomology. The exponent may depend on the ideal.

Source: Stacks Project, Varieties, Tag 0B5X, lemma-ample-curve, third proof paragraph
(blueprint: lem-trf-affine-section-ideal-twist-h1-vanishing).

Proof:
1. Put L = N^n and F_e = I tensor L^e. By lem-trf-proper-field-invertible-coherent,
   C is Noetherian and O_C is coherent. The quasi-coherent ideal I is coherent by
   lem-weil-pbc-coherent-kernel-cokernel-locnoeth(2). Local trivializations show that
   all F_e are coherent and all powers of L are invertible. Noetherianity gives
   quasi-compactness and lem-weil-pbc-locally-noetherian-quasi-separated gives
   quasi-separatedness.
2. On every nonempty affine trivializing open the coefficient a of s is nonzero.
   Indeed, if s vanished on one such open, irreducibility and injectivity of localization
   in a domain would force its coefficient to vanish on every other such open, hence
   s = 0. Multiplication by a is injective on the ideal and invertible on D(a).
   Consequently the maps u_e : F_e -> F_(e+1) are injective and isomorphisms over C_s.
3. The coherent cokernel Q_e is supported in C minus C_s. This is a proper closed
   subset: the generic point lies in D(a). Any length-one chain of irreducible closed
   subsets of the support, after closure in C and appending C, would contradict dim C = 1.
   Thus the support has dimension at most zero.
4. By lem-sfb-coherent-zero-dimensional-support, H^1(Q_e) vanishes. The long exact
   sequence of pqf-def-cohomology makes H^1(u_e) surjective. Its composites
   T_e : H^1(I) -> H^1(F_e) are therefore surjective k-linear maps.
5. Apply lem-sc-section-affine-open-kills-cohomology to L, s, I and p = 1.
   Every class in H^1(I) is killed by some T_e. Locally both this composite and
   tensoring with s^e are multiplication by a^e, so these are the same map.
6. By lem-pc-coherent-hi, H^1(I) is finite-dimensional over k. Choose a finite basis
   and E at least one and at least every annihilating exponent for its basis vectors.
   Functoriality makes T_E zero on the basis, hence zero. Its surjectivity gives
   H^1(F_E) = 0. Grouping tensor factors identifies F_E with I tensor N^(E*n).
   For the empty basis take E = 1.
-/
theorem exists_ideal_tensorPow_h1_isZero_of_affine_nonvanishing
    {k : Type u} [Field k] {C : Scheme.{u}} [C.Over (Spec (.of k))]
    [IsIntegral C] [IsProper (C ↘ Spec (.of k))]
    (hdim : topologicalKrullDim C = (1 : WithBot ℕ∞))
    (N : C.Modules) [N.IsInvertible] (n : ℕ) (hn : 1 ≤ n)
    (s : (N.tensorPow n).val.presheaf.obj (op ⊤)) (hs : s ≠ 0)
    (U : C.Opens) (hU : (U : Set C) = nonvanishingLocus (N.tensorPow n) s)
    (hAffine : IsAffineOpen U) (I : C.IdealSheafData)
    (hI : I.toModules.IsQuasicoherent) :
    ∃ E : ℕ, 1 ≤ E ∧
      IsZero ((RingedSpace.moduleCohomology C.toRingedSpace 1).obj
        (I.toModules ⊗ N.tensorPow (E * n))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
