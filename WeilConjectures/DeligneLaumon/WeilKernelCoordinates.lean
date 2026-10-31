/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.GroupTheory.WeilGroup
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Separation.Hausdorff

/-! # The open geometric subgroup without a degree-one hypothesis

Source: Weil II (1.1.10)--(1.1.12), the kernel part of the Weil-group construction.
(blueprint: lem-dl-a1-weil-open-kernel-coordinates).
-/

@[expose] public section
set_option autoImplicit false
universe u v w

namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil.WeilKernel

variable {P : Type u} {G : Type v} {Γ : Type w} [Group P] [Group G] [Group Γ]

/-- Place an arithmetic kernel element in degree zero. This construction needs neither
surjectivity of the arithmetic quotient nor infinite order of Frobenius.
Source: Weil II (1.1.10) (blueprint: lem-dl-a1-weil-open-kernel-coordinates). -/
def lift (π : G →* Γ) (Φ : Γ) (j : P →* G) (h : ∀ p, π (j p) = 1) :
    P →* π.weilGroup Φ :=
  (j.prod 1).codRestrict _ fun p ↦ by
    rw [MonoidHom.mem_weilGroup]
    exact (h p).trans (zpow_zero Φ).symm

/-- Any compact geometric group identified with the arithmetic kernel identifies with the
open degree-zero subgroup of the Weil group. In particular the statement remains valid when
the image of the degree is a proper subgroup of the integers.

Source: Weil II (1.1.10)--(1.1.12), kernel identification in step 3 of the generic-fibre proof.
(blueprint: lem-dl-a1-weil-open-kernel-coordinates).

Proof: the first coordinate of the lifted map is j and the second coordinate is the identity.
Injectivity follows from the first coordinate. A degree-zero Weil element has first coordinate
in ker pi; the range hypothesis on j gives its unique preimage. The lifted map is continuous
because j is continuous. A continuous injection from a compact space into the Hausdorff Weil
group is a topological embedding. Its range is the preimage of the open singleton {0} under
the continuous integer-degree map, hence is open. -/
theorem coordinates (π : G →* Γ) (Φ : Γ) (j : P →* G) (h : ∀ p, π (j p) = 1)
    [TopologicalSpace P] [CompactSpace P] [TopologicalSpace G] [T2Space G]
    (hj : Function.Injective j) (hr : j.range = π.ker) (hc : Continuous j) :
    Function.Injective (lift π Φ j h) ∧
      (lift π Φ j h).range = (π.weilGroupDeg Φ).ker ∧
      Topology.IsOpenEmbedding (lift π Φ j h) := by
  have hi : Function.Injective (lift π Φ j h) := by
    intro a b hab
    exact hj (congrArg (fun z : π.weilGroup Φ ↦ z.val.1) hab)
  have hkr : (lift π Φ j h).range = (π.weilGroupDeg Φ).ker := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      rfl
    · intro hz
      have hz0 : z.val.2 = 1 := hz
      have hz1 : z.val.1 ∈ π.ker := by
        rw [MonoidHom.mem_ker, MonoidHom.mem_weilGroup.mp z.property, hz0]
        exact zpow_zero Φ
      rw [← hr] at hz1
      obtain ⟨p, hp⟩ := hz1
      exact ⟨p, Subtype.ext (Prod.ext hp hz0.symm)⟩
  have hcont : Continuous (lift π Φ j h) :=
    (hc.prodMk continuous_const).subtype_mk _
  refine ⟨hi, hkr, ⟨(hcont.isClosedEmbedding hi).isEmbedding, ?_⟩⟩
  change IsOpen (↑((lift π Φ j h).range) : Set (π.weilGroup Φ))
  rw [hkr]
  change IsOpen ((fun z : π.weilGroup Φ ↦ z.val.2) ⁻¹' {1})
  exact (isOpen_discrete ({1} : Set (Multiplicative ℤ))).preimage
    (continuous_snd.comp continuous_subtype_val)

end AlgebraicGeometry.ProEtale.CondensedGenericWeil.WeilKernel
