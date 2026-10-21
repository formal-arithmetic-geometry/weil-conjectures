/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z7
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections

/-! # The structural tensor-section pullback formula

Source: Stacks Project, Tags 03P2, 03DR and 01FD.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

/-- A copy of a section morphism is uniquely determined by equality to that morphism.
Source: equality reflexivity and uniqueness.
(blueprint: lem-weil-pbc-qcoherent-pullback-sections-map)

Proof: Use the given map itself. Any map equal to it is that same map. -/
theorem existsUniqueSectionMapCopy {A B : Ab.{u}} (f : A ⟶ B) :
    ∃! k : A ⟶ B, k = f := by
  exact ⟨f, rfl, fun k hk ↦ hk⟩

/-- A uniquely specified copy keeps section maps stable under kernel conversion. -/
def sectionMapCopy {A B : Ab.{u}} (f : A ⟶ B) : A ⟶ B :=
  Classical.choose (existsUniqueSectionMapCopy f)

/-- Copying preserves the section morphism exactly.
Source: the defining unique equality.
(blueprint: lem-weil-pbc-qcoherent-pullback-sections-map)

Proof: The chosen map satisfies its defining equality to the original map. -/
theorem sectionMapCopy_eq {A B : Ab.{u}} (f : A ⟶ B) : sectionMapCopy f = f :=
  (Classical.choose_spec (existsUniqueSectionMapCopy f)).1

/-- Structural pullback of a tensor section across a square, followed by the module map.
Source: Stacks Project, Tags 03P2, 03DR and 01FD.
(blueprint: lem-weil-pbc-qcoherent-pullback-sections-map). -/
def qcoherentPullbackSection {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (ψ : (tensorPullback g).obj F ⟶ G)
    (U : X.Etale) (V : Y.Etale) (p : V.left ⟶ U.left)
    (h : p ≫ U.hom = V.hom ≫ g) :
    Γ((tensorPullback U.hom).obj F, ⊤) ⟶ Γ((tensorPullback V.hom).obj G, ⊤) :=
  sectionMapCopy (
  tensorSectionsUnit p ((tensorPullback U.hom).obj F) ≫
    ((tensorSectionsComp p U.hom).hom.app F).app ⊤ ≫
    (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) h)).app ⊤ ≫
    ((tensorSectionsComp V.hom g).inv.app F).app ⊤ ≫
    ((tensorPullback V.hom).map ψ).app ⊤)

end
end AlgebraicGeometry.Scheme.Modules
