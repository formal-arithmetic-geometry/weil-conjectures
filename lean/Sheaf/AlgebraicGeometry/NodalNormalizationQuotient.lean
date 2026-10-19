/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.RingTheory.PowerSeriesNormalDomain
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import Sheaf.AlgebraicGeometry.NormalizationSingularSkyscraper

/-! # Normalization quotient at split nodes

Source: Stacks Project, Varieties, Tag 0C1R (lemma-prepare-delta-invariant),
parts (2), (4), (9), and Curves, Tags 0C4A (lemma-2-branches-delta-1), Case I,
and 0CBW (lemma-split-node) (blueprint: lem-trf-nodal-normalization-quotient).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The componentwise normalization of a proper reduced connected curve with split nodal
completed local rings has a coherent quotient equal to one copy of the residue field at
each nonsmooth point. Its support is contained in the nonsmooth locus, and its Euler
characteristic is the number of nonsmooth points. The first arrow is the canonical map
of structure sheaves. Each `i x` is the closed `k`-point at `x`: the equation over `k` and
its singleton image characterize the inclusion used in the skyscraper summand. The
coproduct of sheaves of modules is their direct sum, including the empty direct sum.

Source: Stacks Project, Varieties, Tag 0C1R (lemma-prepare-delta-invariant),
parts (2), (4), (9), and Curves, Tags 0C4A (lemma-2-branches-delta-1), Case I,
and 0CBW (lemma-split-node) (blueprint: lem-trf-nodal-normalization-quotient).

Proof:
1. Properness gives finite type. Apply `lem-trf-normalization-singular-skyscraper` to
   the reduced pure one-dimensional curve. It gives finiteness of the nonsmooth locus,
   its closed points with structural residue field `k`, finiteness of the componentwise
   normalization, the coherent exact sequence, and its decomposition into skyscrapers
   of the local normalization quotients. Completion identifies each local quotient
   with the quotient of the integral closure of its completed local ring.
2. For `R = k[[u,v]]/(uv)`, restriction to the axes identifies `R` with the pairs in
   `P = k[[u]] × k[[v]]` having equal constant term. The element `(u,v)` is a
   non-zero-divisor. Clearing negative powers by its powers identifies the total
   fraction ring with `k((u)) × k((v))`.
3. The idempotent `(1,0) = (u,0)/(u,v)` is integral over `R` and generates `P` as an
   `R`-algebra. Apply `lem-weil-pbc-power-series-normal-domain` to the field `k`.
   Each factor of `P` is normal, so projecting a monic equation shows that `P` is
   precisely the integral closure of `R` in that total fraction ring.
4. The difference of constant terms maps `P` onto `k` with kernel `R`. The `R`-action
   factors through its residue field. Therefore the quotient is one-dimensional over
   the residue field of the original local ring, which is structurally `k`. This also
   handles a completion isomorphism that twists scalars: a nonzero quotient vector
   gives a linear identification with the structural residue field. Substitute these
   identifications in the skyscraper decomposition. Self-nodes and intersections of
   distinct components both contribute a single copy of `k`.
5. The support is contained in the finite closed nonsmooth locus. Apply
   `lem-pc-chi-zero-dim-support`: positive cohomology vanishes and the Euler
   characteristic is the dimension of global sections. The finite direct sum of
   skyscraper fields has global sections the direct sum of `|N|` copies of `k`.
   For empty `N` this is the zero module and its Euler characteristic is zero. -/
theorem nodal_normalization_quotient
    (k : Type u) [Field k] [IsAlgClosed k] (B : Scheme.{u})
    [B.Over (Spec (.of k))] [IsProper (B ↘ Spec (.of k))]
    [IsReduced B] [ConnectedSpace B]
    (hpure : ∀ Z : Set B, Z ∈ irreducibleComponents B → topologicalKrullDim Z = 1)
    (hnodal : ∀ x : B, x ∉ (B ↘ Spec (.of k)).smoothLocus →
      Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (B.presheaf.stalk x))
        (B.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸ Ideal.span
            {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})))
    (N : Set B) (hN : N = {x : B | x ∉ (B ↘ Spec (.of k)).smoothLocus}) :
    N.Finite ∧ IsFinite B.fromReducedNormalization ∧
    RingedSpace.IsCoherent B.toRingedSpace (Modules.unit B) ∧
    RingedSpace.IsCoherent B.toRingedSpace
      ((Modules.pushforward B.fromReducedNormalization).obj
        (Modules.unit B.reducedNormalization)) ∧
    ∃ (Q : B.Modules)
      (q : (Modules.pushforward B.fromReducedNormalization).obj
        (Modules.unit B.reducedNormalization) ⟶ Q)
      (hq : SheafOfModules.unitToPushforwardObjUnit
        B.fromReducedNormalization.toRingCatSheafHom ≫ q = 0),
      (ShortComplex.mk (SheafOfModules.unitToPushforwardObjUnit
        B.fromReducedNormalization.toRingCatSheafHom) q hq).ShortExact ∧
      RingedSpace.IsCoherent B.toRingedSpace Q ∧
      (∃ i : N → (Spec (.of k) ⟶ B),
        (∀ x : N, IsClosedImmersion (i x) ∧
          i x ≫ (B ↘ Spec (.of k)) = 𝟙 (Spec (.of k)) ∧
          Set.range (i x) = {x.val}) ∧
        Nonempty (Q ≅ ∐ (fun x : N ↦
          (Modules.pushforward (i x)).obj (Modules.unit (Spec (.of k)))))) ∧
      {x : B | ¬ Subsingleton (Q.presheaf.stalk x)} ⊆ N ∧
      Q.eulerChar k = (N.ncard : ℤ) := by
  sorry

end AlgebraicGeometry.Scheme
