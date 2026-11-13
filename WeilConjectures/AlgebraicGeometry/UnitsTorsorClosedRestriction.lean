/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ZariskiUnitsRestriction
public import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPushforward
import WeilConjectures.CategoryTheory.Sites.TorsorH1BoundaryRepresentative
import WeilConjectures.AlgebraicGeometry.UnitsTorsorClosedRestrictionBoundary

/-!
# Closed restriction of classes of units torsors

## References

* [Stacks Project, Tag 02FQ](https://stacks.math.columbia.edu/tag/02FQ)
* [Stacks Project, Tag 02UV](https://stacks.math.columbia.edu/tag/02UV)
* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Direct image of a units torsor along a closed immersion, with the action evaluated
on inverse-image opens. Closedness supplies local sections also off the image. -/
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

Edge cases: for i = identity this is invariance under the identity comparison. If Z is
empty, both Q and its direct image are trivial torsors, so both classes are zero.
No surjectivity of O_X^* to i_* O_Z^* is needed. -/
theorem unitsTorsor_closed_restriction_class {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (Q : Sheaf.Torsor Z.unitsSheaf) :
    unitsPushforwardCohomologyComparison i 1
      (Sheaf.Torsor.classH1 _ isTerminalTop ⟦unitsTorsorClosedPushforward i Q⟧) =
      Sheaf.Torsor.classH1 Z.unitsSheaf isTerminalTop ⟦Q⟧ := by
  obtain ⟨⟨E, a, p, w, hS, hQ, hclass⟩, _⟩ :=
    CategoryTheory.Sheaf.torsor_h1_boundary_representative Z Z.unitsSheaf Q
  obtain ⟨_, r, hr, k, hkfst, hk, hP, e, _, hequiv⟩ :=
    Sheaf.Torsor.closedImmersion_extension_fibre_pushforward
      Z X i Z.unitsSheaf E a p w hS
  obtain ⟨q⟩ := hQ
  let eQ := (TopCat.Sheaf.pushforward (Type u) i.base).mapIso q.iso.symm
  let t : Sheaf.Torsor.Iso
      (Sheaf.Torsor.lifts isTerminalTop hP
        ((toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op ⊤) ⟨1⟩))
      (unitsTorsorClosedPushforward i Q) :=
    { iso := e ≪≫ eQ
      map_vadd := by
        intro U g s
        change q.iso.inv.hom.app ((Opens.map i.base).op.obj U)
          (e.hom.hom.app U (_)) = _
        exact (congrArg
          (q.iso.inv.hom.app ((Opens.map i.base).op.obj U))
          (hequiv U.unop g s)).trans
            (q.symm.map_vadd ((Opens.map i.base).op.obj U) g
              (e.hom.hom.app U s)) }
  have ht := @_root_.Quotient.sound _
    (Sheaf.Torsor.setoid
      (G := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj Z.unitsSheaf))
    _ _ ⟨t⟩
  rw [← ht, Sheaf.Torsor.classH1_lifts]
  exact (units_extension_pullback_boundary_comparison i E a p w hS
    r hr k hkfst hk hP).trans hclass.symm

end AlgebraicGeometry.Scheme
