/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NodalLineSerreRiemannRoch
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Topology.Sober

/-! # Subcanonical clusters and their splitting index

Source: Franciosi--Tenni, On Clifford's theorem for singular curves, Definitions 2.9,
2.16 and Proposition 2.17(i), pp.231, 233--234
(blueprint: def-sfb-subcanonical-splitting-index).

The section spaces are represented by their actual global sections. The ideal inclusion
embeds them in the canonical sections. Supported sections are intersections of generic-germ
kernels. Admissibility means that the canonical finite direct-sum map is bijective.
The index is the supremum of the numbers of blocks minus one, with the separate convention
that the empty cluster has index zero. The geometric hypotheses make this a nonempty bounded
set of natural numbers, so its supremum is its largest element.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory TopologicalSpace DirectSum

namespace AlgebraicGeometry.Scheme.Modules

/-- The module `I_T ⊗ ω`, using the kernel ideal of the given closed immersion.
Source: Franciosi--Tenni, Definition 2.9
(blueprint: def-sfb-subcanonical-splitting-index). -/
noncomputable def subcanonicalModule {X T : Scheme.{u}} (i : T ⟶ X) (ω : X.Modules) :
    X.Modules :=
  i.ker.toModules ⊗ ω

/-- The canonical inclusion of `I_T ⊗ ω` into `ω`, when `ω` is invertible.
The formula is defined without any invertibility assumption.
Source: Franciosi--Tenni, Definition 2.9
(blueprint: def-sfb-subcanonical-splitting-index). -/
noncomputable def subcanonicalModuleInclusion {X T : Scheme.{u}} (i : T ⟶ X)
    (ω : X.Modules) : subcanonicalModule i ω ⟶ ω :=
  i.ker.toModulesι ▷ ω ≫ (λ_ ω).hom

/-- Sections supported on a union of components: the germ is zero at the generic
point of every component outside the block. This additive subgroup is also a vector
subspace over the base field, since all germ maps respect scalars.
Source: Franciosi--Tenni, Definition 2.16 and Proposition 2.17(i)
(blueprint: def-sfb-subcanonical-splitting-index). -/
noncomputable def subcanonicalSupportedSections {X : Scheme.{u}} (F : X.Modules)
    (A : Set (irreducibleComponents X)) : AddSubgroup Γ(F, ⊤) :=
  ⨅ (C : irreducibleComponents X) (_ : C ∉ A),
    (TopCat.Presheaf.germ F.presheaf ⊤ (genericPoints.ofComponent C).val
      (Set.mem_univ _)).hom.ker

/-- A cluster is subcanonical when `I_T ⊗ ω` has one global section whose germ is
nonzero at every component generic point.
Source: Franciosi--Tenni, Definition 2.9
(blueprint: def-sfb-subcanonical-splitting-index). -/
def IsSubcanonicalCluster {X T : Scheme.{u}} (i : T ⟶ X) (ω : X.Modules) : Prop :=
  ∃ s : Γ(subcanonicalModule i ω, ⊤), ∀ C : irreducibleComponents X,
    TopCat.Presheaf.germ (subcanonicalModule i ω).presheaf ⊤
      (genericPoints.ofComponent C).val (Set.mem_univ _) s ≠ 0

/-- The summation map from the direct sum of the supported section spaces.
Source: Franciosi--Tenni, Definition 2.16 and Proposition 2.17(i)
(blueprint: def-sfb-subcanonical-splitting-index). -/
noncomputable def subcanonicalPartitionSum {X : Scheme.{u}} (F : X.Modules)
    (P : Finpartition (Set.univ : Set (irreducibleComponents X))) :
    (⨁ A : P.parts, subcanonicalSupportedSections F A.val) →+ Γ(F, ⊤) :=
  DirectSum.toAddMonoid (fun A : P.parts ↦ (subcanonicalSupportedSections F A.val).subtype)

/-- An admissible partition splits every section uniquely into sections supported
on its blocks. The summation map is linear; hence bijectivity is exactly the stated
isomorphism of vector spaces, expressed on the underlying additive groups.
Source: Franciosi--Tenni, Definition 2.16 and Proposition 2.17(i)
(blueprint: def-sfb-subcanonical-splitting-index). -/
def IsSubcanonicalAdmissiblePartition {X : Scheme.{u}} (F : X.Modules)
    (P : Finpartition (Set.univ : Set (irreducibleComponents X))) : Prop :=
  Function.Bijective (subcanonicalPartitionSum F P)

/-- The geometric data of a subcanonical cluster on the nodal curve in the node.
The dualizing module is specified with the natural representing isomorphisms of
`exists_nodal_line_serre_riemann_roch`, rather than replaced by an arbitrary line bundle.
The inequality for the cluster dimension includes the empty scheme.
Source: Franciosi--Tenni, Definitions 2.3, 2.9, 2.16; Stacks, Tags 0BS2 and 0E6R
(blueprint: def-sfb-subcanonical-splitting-index). -/
structure SubcanonicalClusterData (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsHProjective (X ↘ Spec (.of k))] [ConnectedSpace X] [IsReduced X]
    (T : Scheme.{u}) (i : T ⟶ X) [IsClosedImmersion i] where
  /-- Every irreducible component has dimension one. -/
  pure_dimension : X.IsPureDimension 1
  /-- Every singular closed point is an ordinary node. -/
  nodal : ∀ x : X, IsClosed ({x} : Set X) →
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
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k)}) a
  /-- A zero-dimensional closed subscheme, allowing the empty cluster. -/
  zero_dimensional : topologicalKrullDim T ≤ 0
  /-- The specified dualizing module. -/
  dualizing : X.Modules
  /-- Nodal dualizing modules are invertible. -/
  invertible : dualizing.IsInvertible
  /-- The Serre-duality representing isomorphisms. -/
  duality : ∀ (F : X.Modules), F.IsQuasiCoherentFiniteType →
    (F ⟶ dualizing) ≃ₗ[k]
      Module.Dual k (scalarCohomology (X ↘ Spec (.of k)) F 1)
  /-- Naturality in the coherent module. -/
  duality_natural : ∀ (F G : X.Modules) (hF : F.IsQuasiCoherentFiniteType)
    (hG : G.IsQuasiCoherentFiniteType) (a : F ⟶ G) (φ : G ⟶ dualizing)
    (x : scalarCohomology (X ↘ Spec (.of k)) F 1),
    duality F hF (a ≫ φ) x = duality G hG φ
      (scalarCohomologyMap (X ↘ Spec (.of k)) a 1 x)
  /-- A nonempty cluster is subcanonical; the empty cluster has index zero by convention. -/
  subcanonical : IsEmpty T ∨ IsSubcanonicalCluster i dualizing

open Classical in
/-- The splitting index: for a nonempty cluster, the largest number of admissible
blocks minus one; for an empty cluster, zero regardless of its section-space splitting.
The one-block partition is admissible. Projectivity over a field implies Noetherianity,
so there are finitely many components and partitions, and this supremum is a maximum.
Source: Franciosi--Tenni, Definition 2.16 and Proposition 2.17(i)
(blueprint: def-sfb-subcanonical-splitting-index). -/
noncomputable def subcanonicalSplittingIndex
    {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsHProjective (X ↘ Spec (.of k))] [ConnectedSpace X] [IsReduced X]
    {T : Scheme.{u}} {i : T ⟶ X} [IsClosedImmersion i]
    (D : SubcanonicalClusterData k X T i) : ℕ :=
  if IsEmpty T then 0 else
    sSup {n : ℕ | ∃ P : Finpartition (Set.univ : Set (irreducibleComponents X)),
      IsSubcanonicalAdmissiblePartition (subcanonicalModule i D.dualizing) P ∧
        n = P.parts.card - 1}

end AlgebraicGeometry.Scheme.Modules
