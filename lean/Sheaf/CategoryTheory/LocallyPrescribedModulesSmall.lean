/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.ObjectProperty.Small
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing

/-!
# Smallness of module sheaves with prescribed local models

Source: Stacks Project, Sites, Tag 04TQ and Modules on Sites, Tag 03EM; the
Essentially small paragraph of the current blueprint's Brown hypotheses proof
(blueprint: lem-sfb-locally-prescribed-modules-small).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Module sheaves locally among prescribed small families are essentially small.

Source: Stacks Project, Sites, Tag 04TQ, Modules on Sites, Tag 03EM, and the
Essentially small paragraph of `sk-lem-brown-hypotheses-small.proof.md`
(blueprint: lem-sfb-locally-prescribed-modules-small).

The universe `u` is the fixed universe of the small site, section sets and local
model labels. The cover uses the original precoverage, not just its generated
covering sieves. `ObjectProperty.EssentiallySmall.exists_small_le` expresses the
conclusion as a small family of members representing all the isomorphism classes.

Proof: (1) On each slice, morphisms between two fixed modules inject into the
small product of component function sets. Linearity and naturality cut out a
subset, so morphisms and isomorphisms form small sets.
(2) Count codes consisting of an object support, one local-model label per
object in that support, and transition isomorphisms on all pairwise products.
The power set of the object set, small products and small unions give a small
set of codes; no cover or cocycle condition is needed for this upper bound.
(3) Each locally prescribed module realizes a code: choose one occurrence per
object of its witnessing cover and use its trivialization to form the transition
isomorphisms. Retain the original indexed cover, including repeated objects.
(4) Two realizations of the same code have local comparison maps obtained by
composing one trivialization with the inverse of the other. The common transition
maps imply equality on the entire overlap slice, also for the inverse maps.
(5) Apply `existsUnique_hom_of_cover` (lem-pur-sheaf-hom-cover-gluing) to these
maps and their inverses on the retained cover of the terminal object. Its
uniqueness makes the glued composites identities. Restriction to the terminal
object is the original sheaf, so the realizations are isomorphic.
(6) Restrict the small code set to realized codes and choose one realizing module
for each code. This set-indexed choice occurs in the ambient universe of sheaves
with small section sets. Every locally prescribed module is isomorphic to one of
these representatives. If there are no realizations, the empty family suffices.
These steps use the size convention, sectionwise module category and localized
ringed site of the statement dependencies; they do not assert arbitrary descent
data are effective. -/
theorem essentiallySmall_locally_prescribed
    {C : Type u} [Category.{u} C] [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (R : Cᵒᵖ ⥤ CommRingCat.{u})
    (hR : Presheaf.IsSheaf J.toGrothendieck (R ⋙ forget₂ CommRingCat RingCat.{u}))
    (I : C → Type u)
    (B : ∀ U : C, I U → ringedSiteModules.{u}
      (Sheaf.over (⟨R ⋙ forget₂ CommRingCat RingCat.{u}, hR⟩ :
        Sheaf J.toGrothendieck RingCat.{u}) U)) :
    ObjectProperty.EssentiallySmall.{u}
      (fun M : ringedSiteModules.{u} ⟨R ⋙ forget₂ CommRingCat RingCat.{u}, hR⟩ ↦
        ∃ (ι : Type u) (U : ι → C) (f : ∀ j : ι, U j ⟶ ⊤_ C),
          Presieve.ofArrows U f ∈ J (⊤_ C) ∧
            ∀ j : ι, ∃ t : I (U j),
              Nonempty
                (((overFunctor.{u} ⟨R ⋙ forget₂ CommRingCat RingCat.{u}, hR⟩
                  (U j)).obj M) ≅ B (U j) t)) := by
  sorry

end SheafOfModules
