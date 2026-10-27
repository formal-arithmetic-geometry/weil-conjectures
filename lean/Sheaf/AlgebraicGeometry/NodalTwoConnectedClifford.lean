/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Sheaf.AlgebraicGeometry.NodalLineSerreRiemannRoch
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Sober

import Sheaf.AlgebraicGeometry.SubcanonicalSplittingIndex
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import Sheaf.AlgebraicGeometry.ReducedCurveDualizingModule

/-! # Clifford's inequality on a two-connected nodal curve

Source: Franciosi--Tenni, The canonical ring of a 3-connected curve,
Section 2, Theorem 2.7 (Cartier case), pp.40--41; Section 4,
Proposition 4.1 proof, p.48
(blueprint: lem-sfb-nodal-two-connected-clifford).

The dualizing line is specified by the natural representing isomorphisms of
`exists_nodal_line_serre_riemann_roch`. Two-connectedness is expressed on all
partitions of the actual irreducible components, with scheme-theoretic intersections.
The inequality is multiplied by two to use the integer Euler-characteristic degree.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- Clifford's inequality for a line with generically nonzero sections both in the line
and in its canonical dual on a nodal curve without a separating node.

Source: Franciosi--Tenni, The canonical ring of a 3-connected curve, Theorem 2.7,
pp.40--41, and Proposition 4.1 proof, p.48
(blueprint: lem-sfb-nodal-two-connected-clifford).

Proof:
1. Projectivity implies properness (lem-kun-projective-implies-proper), and invertible
   modules are coherent (lem-trf-proper-field-invertible-coherent). Fix the given map
   phi : M -> omega. On an affine trivialization it is multiplication by f, nonzero in
   every minimal-prime domain. If fa = 0, a belongs to every minimal prime and hence
   is zero by reducedness. Thus phi is injective and its image is an invertible Cartier
   ideal twist I_T omega. The zero scheme T contains no component and is zero-dimensional.
   The section of M makes T subcanonical (def-sfb-subcanonical-splitting-index).
2. Apply lem-sfb-nodal-linear-series-base-colength to the complete series of M. Its base
   ideal enlarges T to Tbar with length(Tbar) = length(T) + b and the same canonical
   section subspace, so the splitting index r is unchanged. If r = 0, b >= r. Otherwise,
   choose a maximizing partition into r+1 blocks. Every block boundary contains at
   least two nodes by two-connectedness. Every node between blocks is counted twice,
   giving at least r+1 cross-block nodes, and the base-ideal lemma gives b >= r+1 >= r.
   Self-nodes inside a block do not contribute to this count.
3. By lem-sfb-subcanonical-splitting-clifford-bound, h0(M) <= pa - (length(T)+b)/2 + r/2
   <= pa - length(T)/2. The corrected cluster Tbar need not be Cartier.
4. The exact sequence 0 -> M -> omega -> omega tensor O_T -> 0, Euler additivity
   (lem-pc-euler-additive), and lem-pc-chi-zero-dim-support give
   chi(M) = chi(omega) - length(T). Reduced-curve duality
   (lem-sfb-reduced-curve-dualizing-module), identified with the specified dualizing line
   by uniqueness in lem-sfb-nodal-line-serre-riemann-roch, gives chi(omega) = -chi(O).
   Therefore def-pc-degree-line-bundle gives deg(M) = 2pa - 2 - length(T).
   Substituting into step 3 gives twice the claimed inequality. Empty T and irreducible
   X are included.
-/
theorem nodal_two_connected_clifford
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsHProjective (X ↘ Spec (.of k))] [ConnectedSpace X] [IsReduced X]
    (hpure : X.IsPureDimension 1)
    (hnodal : ∀ x : X, IsClosed ({x} : Set X) →
      x ∉ (X ↘ Spec (.of k)).smoothLocus →
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)}),
        ∀ a : k, e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ((X.presheaf.germ ⊤ x (Set.mem_univ _))
            (scalarMap (X ↘ Spec (.of k)) ⊤ a))) =
          algebraMap k (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)}) a)
    (htwo : ∀ (A B : Scheme.{u}) (a : A ⟶ X) (b : B ⟶ X),
      IsClosedImmersion a → IsClosedImmersion b → IsReduced A → IsReduced B →
      Nonempty A → Nonempty B →
      (∃ P Q : Set (Set X), P ⊆ irreducibleComponents X ∧ Q ⊆ irreducibleComponents X ∧
        Disjoint P Q ∧ P ∪ Q = irreducibleComponents X ∧
        Set.range a = ⋃₀ P ∧ Set.range b = ⋃₀ Q) →
      2 ≤ @Module.finrank k Γ(pullback a b, ⊤) _ _
        (Module.compHom _ (scalarMap (pullback.fst a b ≫ a ≫ X ↘ Spec (.of k)) ⊤)))
    (ω : X.Modules) [ω.IsInvertible]
    (e : ∀ (F : X.Modules), F.IsQuasiCoherentFiniteType →
      (F ⟶ ω) ≃ₗ[k] Module.Dual k (scalarCohomology (X ↘ Spec (.of k)) F 1))
    (he : ∀ (F G : X.Modules) (hF : F.IsQuasiCoherentFiniteType)
      (hG : G.IsQuasiCoherentFiniteType) (a : F ⟶ G) (φ : G ⟶ ω)
      (z : scalarCohomology (X ↘ Spec (.of k)) F 1),
      e F hF (a ≫ φ) z = e G hG φ (scalarCohomologyMap (X ↘ Spec (.of k)) a 1 z))
    (M : X.Modules) [M.IsInvertible]
    (hs : ∃ s : Γ(M, ⊤), ∀ C : irreducibleComponents X,
      TopCat.Presheaf.germ M.presheaf ⊤ (genericPoints.ofComponent C).val
        (Set.mem_univ _) s ≠ 0)
    (hφ : ∃ φ : M ⟶ ω, ∀ C : irreducibleComponents X,
      (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (genericPoints.ofComponent C).val).map φ ≠ 0) :
    2 * (Module.finrank k (scalarCohomology (X ↘ Spec (.of k)) M 0) : ℤ) ≤
      Scheme.Modules.degree k M + 2 := by
  sorry

end AlgebraicGeometry
