/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Sheaf.AlgebraicGeometry.SubcanonicalResidualDuality
public import Sheaf.AlgebraicGeometry.SubcanonicalSplittingIndex
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete

/-! # Residual nesting for an extremal subcanonical cluster

Source: Franciosi--Tenni, On Clifford's theorem for singular curves,
Lemma 3.1, pp.234--235, strict branch, with the union-stratum hypothesis explicit
(blueprint: lem-sfb-extremal-cluster-residual-nesting).

The residual is specified by the canonical evaluation image of the recorded residual
construction. The union is the subscheme of the intersection of the two ideal sheaves.
Containment is an inequality of ideal sheaves, so it retains the scheme structures.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A strict negative Clifford minimizer of maximal length contains its residual,
provided their union is subcanonical and stays in the splitting stratum.
Source: Franciosi--Tenni, Lemma 3.1, pp.234--235, strict branch, with the missing
union-stratum hypothesis explicit; the same-section argument is the node's correction
(blueprint: lem-sfb-extremal-cluster-residual-nesting).

Here `c` is exactly the integer c(S), as fixed by `hc`. Competitor data `E` and union
data `DU` use the very same dualizing module as `D`. Their other fields record the
geometric hypotheses already present on X and on the zero-dimensional clusters.
The residual ideal `J` is characterized by its evaluation image, as in
`subcanonical_residual_duality`. The conclusion `i.ker ≤ J` means S* is contained
in S as a closed subscheme. No bound on the residual's or intersection's splitting
index, genericity of the chosen section, or Cartier hypothesis is required.

Proof, following the node's six steps:
1. Put T = S*, U = S union T and Z = S intersection T. Residual duality
   (`lem-sfb-subcanonical-residual-duality`) gives T subcanonical and T* = S for
   the same ambient canonical section s. Evaluating the inclusion F_S into omega
   shows s lies in V_T, hence in V_U and V_Z. Thus Z is subcanonical as well.
2. Trivialize omega locally. Then F_Z = F_S + F_T and F_U = F_S intersect F_T.
   A map on F_Z restricts to maps on F_S and F_T with the same value at s.
   Conversely, maps on F_S and F_T with the same value at s agree on F_U,
   since evaluation on Hom(F_U, omega) is injective by residual duality for U.
   They therefore glue on the sum. Evaluation for Z is injective, so the local
   glued maps agree on overlaps. Its image is the intersection of the evaluation
   images for S and T, namely F_T intersect F_S = F_U. Residual uniqueness gives Z* = U.
3. The addition map V_S direct-sum V_T to V_Z has kernel the anti-diagonal V_U.
   Rank-nullity gives v(S) + v(T) ≤ v(U) + v(Z), without requiring surjectivity.
   Residual duality gives length(S) + length(T) = length(Z) + length(U) = 2pa - 2,
   c(T) = c(S) and c(Z) = c(U). Substitution gives 2c(U) ≤ 2c(S).
4. The explicit union hypotheses permit extremal comparison with U, yielding
   c(S) ≤ c(U), hence equality. Maximal length among minimizers gives length(U) ≤ length(S).
5. Projectivity implies properness (`lem-kun-projective-implies-proper`), hence
   finite type, and X is Noetherian (`lem-weil-pbc-finite-type-over-noetherian`).
   Its closed subscheme U is Noetherian and zero-dimensional, hence finite discrete
   (`lem-sc-zero-dim-noetherian-finite-discrete`). On this finite discrete space,
   sections are the finite product of stalks. The inclusion S into U gives a
   stalkwise surjection of structure sheaves and therefore a surjection on global
   sections. Finite-dimensionality gives length(S) ≤ length(U).
6. Equal lengths make this surjection an isomorphism; every stalk kernel vanishes.
   Thus I_S/I_U = 0, I_S = I_U, and T is contained in S, including nilpotents.
-/
theorem extremal_cluster_residual_nesting
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsHProjective (X ↘ Spec (.of k))] [ConnectedSpace X] [IsReduced X]
    (hTwoConnected : ∀ (A B : Scheme.{u}) (a : A ⟶ X) (b : B ⟶ X),
      IsClosedImmersion a → IsClosedImmersion b → IsReduced A → IsReduced B →
      Nonempty A → Nonempty B →
      (∃ P Q : Set (Set X), P ⊆ irreducibleComponents X ∧ Q ⊆ irreducibleComponents X ∧
        Disjoint P Q ∧ P ∪ Q = irreducibleComponents X ∧
        Set.range a = ⋃₀ P ∧ Set.range b = ⋃₀ Q) →
      2 ≤ Module.finrank k (scalarCohomology
        (CategoryTheory.Limits.pullback.fst a b ≫ a ≫ X ↘ Spec (.of k))
        (unit (CategoryTheory.Limits.pullback a b)) 0))
    (S : Scheme.{u}) (i : S ⟶ X) [IsClosedImmersion i]
    (D : SubcanonicalClusterData k X S i)
    (hSsub : IsSubcanonicalCluster i D.dualizing)
    (R : ℕ) (hSplitting : subcanonicalSplittingIndex D ≤ R)
    (c : ℤ)
    (hc : c = 2 * (1 - eulerChar k (unit X)) -
      (Module.finrank k (scalarCohomology (i ≫ X ↘ Spec (.of k)) (unit S) 0) : ℤ) -
      2 * (Module.finrank k (scalarCohomology (X ↘ Spec (.of k))
        (subcanonicalModule i D.dualizing) 0) : ℤ))
    (hNegative : c < 0)
    (hExtremal : ∀ (T : Scheme.{u}) (j : T ⟶ X) [IsClosedImmersion j]
      (E : SubcanonicalClusterData k X T j),
      E.dualizing = D.dualizing → IsSubcanonicalCluster j E.dualizing →
      subcanonicalSplittingIndex E ≤ R →
      c ≤ 2 * (1 - eulerChar k (unit X)) -
          (Module.finrank k (scalarCohomology (j ≫ X ↘ Spec (.of k)) (unit T) 0) : ℤ) -
          2 * (Module.finrank k (scalarCohomology (X ↘ Spec (.of k))
            (subcanonicalModule j E.dualizing) 0) : ℤ) ∧
        (c = 2 * (1 - eulerChar k (unit X)) -
            (Module.finrank k (scalarCohomology (j ≫ X ↘ Spec (.of k)) (unit T) 0) : ℤ) -
            2 * (Module.finrank k (scalarCohomology (X ↘ Spec (.of k))
              (subcanonicalModule j E.dualizing) 0) : ℤ) →
          Module.finrank k (scalarCohomology (j ≫ X ↘ Spec (.of k)) (unit T) 0) ≤
            Module.finrank k (scalarCohomology (i ≫ X ↘ Spec (.of k)) (unit S) 0)))
    (s : Γ(subcanonicalModule i D.dualizing, ⊤))
    (hs : ∀ C : irreducibleComponents X,
      TopCat.Presheaf.germ (subcanonicalModule i D.dualizing).presheaf ⊤
        (genericPoints.ofComponent C).val (Set.mem_univ _) s ≠ 0)
    (J : X.IdealSheafData) (hJdim : topologicalKrullDim J.subscheme ≤ 0)
    (hResidual : imageSubobject (subcanonicalEvaluation (subcanonicalModule i D.dualizing)
      D.dualizing s) = imageSubobject (subcanonicalModuleInclusion J.subschemeι D.dualizing))
    (DU : SubcanonicalClusterData k X (i.ker ⊓ J).subscheme (i.ker ⊓ J).subschemeι)
    (hUnionDualizing : DU.dualizing = D.dualizing)
    (hUnionSubcanonical : IsSubcanonicalCluster (i.ker ⊓ J).subschemeι DU.dualizing)
    (hUnionSplitting : subcanonicalSplittingIndex DU ≤ R) :
    i.ker ≤ J := by
  sorry

end AlgebraicGeometry.Scheme.Modules
