/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker Q67
-/
module

public import Sheaf.RepresentationTheory.DiscreteContinuousCohomology
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Completed group algebra and its augmentation

Source: ILO, Expose XVII, 1.2.1.1, pp. 259–260
(blueprint: def-per-completed-augmentation-algebra).
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace Rep.CompletedAugmentation

variable (Λ : Type v) [CommRing Λ] (G : Type u) [Group G] [TopologicalSpace G]

/-- Finite-quotient group rings, ILO XVII 1.2.1.1
(blueprint: def-per-completed-augmentation-algebra). -/
abbrev Coordinate (U : OpenNormalSubgroup G) := MonoidAlgebra Λ (G ⧸ U.toSubgroup)

/-- Push coefficients along a quotient of groups, ILO XVII 1.2.1.1
(blueprint: def-per-completed-augmentation-algebra). -/
def transition (U V : OpenNormalSubgroup G) (h : U ≤ V) :
    Coordinate Λ G U →ₐ[Λ] Coordinate Λ G V :=
  MonoidAlgebra.mapDomainAlgHom Λ Λ
    (QuotientGroup.map U.toSubgroup V.toSubgroup (MonoidHom.id G) h)

/-- The compatible-family subalgebra, ILO XVII 1.2.1.1
(blueprint: def-per-completed-augmentation-algebra). -/
def compatible : Subalgebra Λ (∀ U : OpenNormalSubgroup G, Coordinate Λ G U) :=
  ⨅ U : OpenNormalSubgroup G, ⨅ V : OpenNormalSubgroup G, ⨅ h : U ≤ V,
    AlgHom.equalizer
      ((transition Λ G U V h).comp (Pi.evalAlgHom Λ _ U)) (Pi.evalAlgHom Λ _ V)

/-- The actual inverse-limit ring, ILO XVII 1.2.1.1
(blueprint: def-per-completed-augmentation-algebra). -/
abbrev Algebra := compatible Λ G

/-- The inverse-limit topology of discrete finite group rings, ILO XVII 1.2.1.1
(blueprint: def-per-completed-augmentation-algebra). -/
instance algebraTopology : TopologicalSpace (Algebra Λ G) :=
  TopologicalSpace.induced Subtype.val
    (@Pi.topologicalSpace (OpenNormalSubgroup G) (Coordinate Λ G) (fun _ ↦ ⊥))

/-- The whole open normal subgroup, used to read the augmentation, ILO XVII 1.2.1.1
(blueprint: def-per-completed-augmentation-algebra). -/
def whole : OpenNormalSubgroup G :=
  { toSubgroup := ⊤
    isOpen' := isOpen_univ }

/-- Sum of coefficients, evaluated at the trivial quotient, ILO XVII 1.2.1.1
(blueprint: def-per-completed-augmentation-algebra). -/
def augmentation : Algebra Λ G →ₐ[Λ] Λ :=
  ((MonoidAlgebra.lift Λ Λ (G ⧸ (whole G).toSubgroup)) 1).comp
    ((Pi.evalAlgHom Λ _ (whole G)).comp (compatible Λ G).val)

/-- The augmentation ideal with its inherited module structure, ILO XVII 1.2.1.1
(blueprint: def-per-completed-augmentation-algebra). -/
abbrev Ideal := RingHom.ker (augmentation Λ G).toRingHom

/-- The subspace topology on the augmentation ideal, ILO XVII 1.2.1.1
(blueprint: def-per-completed-augmentation-algebra). -/
instance idealTopology : TopologicalSpace (Ideal Λ G) :=
  TopologicalSpace.induced Subtype.val (algebraTopology Λ G)

/-- The group elements give compatible quotient coordinates, ILO XVII 1.2.1.1
(blueprint: def-per-completed-augmentation-algebra).
Proof: pushing a basis vector along G/U -> G/V gives the basis vector at the image
of the same group element. Thus it lies in every equalizer defining the limit. -/
theorem groupElement_mem (g : G) :
    (fun U : OpenNormalSubgroup G ↦
      MonoidAlgebra.single (QuotientGroup.mk' U.toSubgroup g) (1 : Λ)) ∈ compatible Λ G := by
  sorry

/-- The canonical group element in the completed algebra, ILO XVII 1.2.1.1
(blueprint: def-per-completed-augmentation-algebra). -/
def groupElement (g : G) : Algebra Λ G :=
  ⟨_, groupElement_mem Λ G g⟩

/-- A basis element has augmentation one, ILO XVII 1.2.1.1
(blueprint: def-per-completed-augmentation-algebra).
Proof: the augmentation sums coefficients, and this vector has the single coefficient one. -/
theorem groupElement_sub_one_mem (g : G) : groupElement Λ G g - 1 ∈ Ideal Λ G := by
  sorry

/-- The canonical element g-1 of I, ILO XVII 1.2.1.1
(blueprint: def-per-completed-augmentation-algebra). -/
def difference (g : G) : Ideal Λ G :=
  ⟨groupElement Λ G g - 1, groupElement_sub_one_mem Λ G g⟩

variable [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [Finite Λ]

/-- The completed action is uniquely determined by continuity and its group values.
Source: ILO XVII 1.2.1.1 (blueprint: def-per-completed-augmentation-algebra).
Proof: every finite subset of M lies in the span of finitely many finite G-orbits.
This finite stable module is killed by an open normal subgroup U. Let a act through
its U-coordinate in Λ[G/U]. A common refinement proves independence and all module laws.
The orbit maps factor through finite discrete coordinates, hence are continuous.
The ordinary group algebra is dense in the compatible-family algebra: lift each finite
quotient vector and refine finitely many coordinates by intersection. Agreement on group
vectors and scalars therefore proves uniqueness of each continuous orbit map. -/
theorem existsUnique_action (M : DiscreteContinuousRep.{v, u, w} Λ G) :
    ∃! α : Algebra Λ G →ₐ[Λ] Module.End Λ M.obj.V,
      (∀ g : G, α (groupElement Λ G g) = M.obj.ρ g) ∧
      (∀ m : M.obj.V, @Continuous (Algebra Λ G) M.obj.V
        (algebraTopology Λ G) ⊥ (fun a ↦ α a m)) := by
  sorry

/-- The canonical continuous completed action, characterized uniquely by its group action.
Source: ILO XVII 1.2.1.1 (blueprint: def-per-completed-augmentation-algebra). -/
noncomputable def action (M : DiscreteContinuousRep.{v, u, w} Λ G) :
    Algebra Λ G →ₐ[Λ] Module.End Λ M.obj.V :=
  Classical.choose (existsUnique_action Λ G M)

end Rep.CompletedAugmentation
