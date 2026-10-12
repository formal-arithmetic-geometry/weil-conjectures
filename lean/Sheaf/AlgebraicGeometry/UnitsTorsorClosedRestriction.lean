/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.ZariskiUnitsRestriction
public import WeilConjectures.CategoryTheory.Sites.Torsor
import Sheaf.CategoryTheory.Sites.TorsorExtensionPushforward
import Sheaf.CategoryTheory.Sites.TorsorH1BoundaryRepresentative
import Sheaf.Topology.ClosedPushforwardBoundaryNaturality

/-!
# Closed restriction of classes of units torsors

Source: Stacks Project, Tags 02FQ and 02UV, as used in Tag 09NY.
(blueprint: lem-sc-units-torsor-closed-restriction-class).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Direct image of a units torsor along a closed immersion, with the action evaluated
on inverse-image opens. Closedness supplies local sections also off the image.
Source: Stacks Project, Tags 02FQ and 02UV.
(blueprint: lem-sc-units-torsor-closed-restriction-class). -/
noncomputable def unitsTorsorClosedPushforward {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (Q : Sheaf.Torsor Z.unitsSheaf) :
    Sheaf.Torsor (((Opens.map i.base).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).obj Z.unitsSheaf) where
  sheaf := (TopCat.Sheaf.pushforward (Type u) i.base).obj Q.sheaf
  vadd U := Q.vadd ((Opens.map i.base).op.obj U)
  zero_vadd U := Q.zero_vadd ((Opens.map i.base).op.obj U)
  add_vadd U := Q.add_vadd ((Opens.map i.base).op.obj U)
  map_vadd f := Q.map_vadd ((Opens.map i.base).op.map f)
  bijective_vadd U := Q.bijective_vadd ((Opens.map i.base).op.obj U)
  nonemptySieve_mem U := by
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    have hi := i.isClosedEmbedding
    by_cases hxim : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hxim
      obtain ⟨V, f, ⟨s⟩, hz⟩ :=
        ((Opens.mem_grothendieckTopology Z).mp
          (Q.nonemptySieve_mem ((Opens.map i.base).obj U))) z hx
      let W : Opens X := ⟨U ∩ (i.base '' (V : Set Z)ᶜ)ᶜ,
        U.isOpen.inter (hi.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
      have hWU : W ≤ U := fun y hy ↦ hy.1
      have hWV : (Opens.map i.base).obj W ≤ V := by
        intro y hy
        by_contra hyV
        exact hy.2 ⟨y, hyV, rfl⟩
      refine ⟨W, homOfLE hWU, ⟨Q.sheaf.obj.map (homOfLE hWV).op s⟩, ?_⟩
      exact ⟨hx, fun ⟨y, hy, he⟩ ↦ hy (hi.isEmbedding.injective he ▸ hz)⟩
    · let W : Opens X := ⟨U ∩ (Set.range i.base)ᶜ,
        U.isOpen.inter hi.isClosed_range.isOpen_compl⟩
      have hWU : W ≤ U := fun y hy ↦ hy.1
      have he : (Opens.map i.base).obj W = ⊥ := by
        ext z
        change (i.base z ∈ U ∧ i.base z ∉ Set.range i.base) ↔ False
        exact ⟨fun hz ↦ hz.2 ⟨z, rfl⟩, False.elim⟩
      have ht := TopCat.Sheaf.isTerminalOfEqEmpty (X := Z.toTopCat) Q.sheaf he
      refine ⟨W, homOfLE hWU, ?_, hx, hxim⟩
      exact ⟨ht.from PUnit PUnit.unit⟩

/-- The canonical comparison sends the class of the explicitly constructed direct-image
torsor to the class of the original torsor.

Source: Stacks Project, Tag 02FQ, boundary-of-one construction; Tag 02UV, canonical
closed-immersion comparison; Tag 09NY, final sentence.

Edge cases: for i = identity this is invariance under the identity comparison. If Z is
empty, both Q and its direct image are trivial torsors, so both classes are zero.
No surjectivity of O_X^* to i_* O_Z^* is needed.
(blueprint: lem-sc-units-torsor-closed-restriction-class).

Proof:
1. Represent Q by an extension of the constant integer sheaf by O_Z^*, with fibre
Q above one. Its torsor class is the boundary of one, by the canonical torsor
classification and its boundary representative description in Tag 02FQ.
2. Apply exact closed direct image to this extension and pull back along the
restriction map from the constant integer sheaf on X to its direct image from Z.
The fibre above one is the direct image of Q: both its sections and its action
are the sections and action of Q on inverse-image opens. This is exactly the
explicit construction unitsTorsorClosedPushforward, so the boundary of one for
the pulled-back extension is its torsor class.
3. The canonical closed-immersion cohomology comparison of Tag 02UV commutes
with the connecting maps and identifies global sections on X with those on Z.
Its inverse is obtained by exact inverse image, the comparison of constant
integer sheaves, and the counit; this is unitsPushforwardCohomologyComparison.
The comparison therefore sends the boundary of one for the pulled-back image
extension to the original boundary of one, proving the equality. -/
theorem unitsTorsor_closed_restriction_class {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (Q : Sheaf.Torsor Z.unitsSheaf) :
    unitsPushforwardCohomologyComparison i 1
      (Sheaf.Torsor.classH1 _ isTerminalTop ⟦unitsTorsorClosedPushforward i Q⟧) =
      Sheaf.Torsor.classH1 Z.unitsSheaf isTerminalTop ⟦Q⟧ := by sorry

end AlgebraicGeometry.Scheme
