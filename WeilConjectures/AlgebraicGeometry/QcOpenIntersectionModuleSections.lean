/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Topology.SubspaceRingRestrictionUnitCoherence
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.Topology.InverseImageModule

/-! # Module-sheaf sections on intersections of quasi-compact opens

Source: Stacks Project, More on Groupoids in Spaces, Tag 0APH,
`equation-sections-of-intersection`; Sheaves, Tags 0A32, 008F and 008N.
(blueprint: lem-sfb-qc-open-intersection-sections-colimit)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The diagram of module sections, with the original directed preorder as its index
and ordinary restrictions as its arrows. Source: Stacks Project, Tag 0APH,
`equation-sections-of-intersection`.
(blueprint: lem-sfb-qc-open-intersection-sections-colimit) -/
def qcOpenIntersectionSectionsDiagram (X : Scheme.{u}) (R : Type u) [CommRing R]
    (F : X.toTopCat.Sheaf (ModuleCat.{u} R)) {J : Type u} [Preorder J]
    (V : J → Opens X) (hV : Antitone V) : J ⥤ ModuleCat.{u} R :=
  ({ obj := fun j ↦ op (V j)
     map := fun {_j _k} f ↦ (homOfLE (hV (leOfHom f))).op
     map_id := fun _ ↦ Subsingleton.elim _ _
     map_comp := fun _ _ ↦ Subsingleton.elim _ _ } : J ⥤ (Opens X)ᵒᵖ) ⋙ F.obj

/-- Sections on the subspace intersection form the module colimit via the actual
inverse-image unit. Every section has a representative, and equality of two
representatives is detected at a common upper index.

Source: Stacks Project, Tag 0APH, `equation-sections-of-intersection`, and
Sheaves, Tags 0A32, 008F and 008N.
(blueprint: lem-sfb-qc-open-intersection-sections-colimit)

Proof:
1. Fix j₀ and pass to the upper tail j ≥ j₀. Directedness makes it cofinal and
   leaves the intersection unchanged; every pair of original stages maps into it.
2. Each stage is a quasi-compact open subscheme. The hypothesis on intersections
   makes it quasi-separated by the affine-cover criterion. Thus every stage,
   including the empty scheme, is spectral.
3. The inclusion of a later stage into an earlier one is spectral: the preimage
   of a compact open W is its intersection with the later compact open. The
   subspace intersection is the topological inverse limit. Compatible tuples
   have one common underlying point, and the topology is induced from j₀.
4. Apply fixed-sheaf spectral-limit section continuity (Tag 0A32) on V j₀.
   Inverse image along an open inclusion is ordinary restriction. Neighbourhoods
   intersected with V j₀ are cofinal, so the comparison with inverse image to E
   preserves the adjunction unit. This gives representatives and eventual
   equality on the upper tail, hence on the original directed preorder.
5. The induced scalar action makes the unit restrictions R-linear. For any
   compatible module cocone, send a section to the value of any representative.
   Eventual equality proves well-definedness. Common upper stages prove
   additivity and R-linearity, and representatives prove uniqueness. Therefore
   the canonical comparison from the chosen module colimit is an isomorphism.
   The argument also covers an empty intersection or an empty stage. -/
theorem qcOpenIntersection_sections_colimit (X : Scheme.{u})
    (hX : ∀ U W : Opens X, IsCompact (U : Set X) → IsCompact (W : Set X) →
      IsCompact ((U : Set X) ∩ (W : Set X)))
    (R : Type u) [CommRing R] (F : X.toTopCat.Sheaf (ModuleCat.{u} R))
    {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (V : J → Opens X) (hV : Antitone V) (hqc : ∀ j : J, IsCompact (V j : Set X)) :
    (∃ e : colimit (qcOpenIntersectionSectionsDiagram X R F V hV) ≅
        ((TopCat.Sheaf.pullback (ModuleCat.{u} R)
          (TopCat.Sheaf.subspaceInclusion {x : X | ∀ j : J, x ∈ V j})).obj F).obj.obj
            (op ⊤),
      ∀ j : J, colimit.ι (qcOpenIntersectionSectionsDiagram X R F V hV) j ≫ e.hom =
        TopCat.Sheaf.subspaceSectionMap (ModuleCat.{u} R)
          {x : X | ∀ k : J, x ∈ V k} F (V j) (fun _ hx ↦ hx j)) ∧
    (∀ s : ((TopCat.Sheaf.pullback (ModuleCat.{u} R)
        (TopCat.Sheaf.subspaceInclusion {x : X | ∀ j : J, x ∈ V j})).obj F).obj.obj
          (op ⊤),
      ∃ (j : J) (t : F.obj.obj (op (V j))),
        TopCat.Sheaf.subspaceSectionMap (ModuleCat.{u} R)
          {x : X | ∀ k : J, x ∈ V k} F (V j) (fun _ hx ↦ hx j) t = s) ∧
    (∀ (j k : J) (s : F.obj.obj (op (V j))) (t : F.obj.obj (op (V k))),
      TopCat.Sheaf.subspaceSectionMap (ModuleCat.{u} R)
          {x : X | ∀ l : J, x ∈ V l} F (V j) (fun _ hx ↦ hx j) s =
        TopCat.Sheaf.subspaceSectionMap (ModuleCat.{u} R)
          {x : X | ∀ l : J, x ∈ V l} F (V k) (fun _ hx ↦ hx k) t ↔
      ∃ (l : J) (hjl : j ≤ l) (hkl : k ≤ l),
        F.obj.map (homOfLE (hV hjl)).op s = F.obj.map (homOfLE (hV hkl)).op t) := by
  sorry

end AlgebraicGeometry.Scheme
