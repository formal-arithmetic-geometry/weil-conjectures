/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.Cohomology.CechComparisonSystem
public import Sheaf.AlgebraicGeometry.Cohomology.CechInverseImageCochainMap

/-! # Degree-zero normalization under inverse image

Source: Stacks Project, Tag 01FD, section faces of Lemma 20.15.1;
Tag 01EQ, degree-zero restriction augmentation.
(blueprint: lem-pc-cech-inverse-image-degree-zero)
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- Degree-zero Čech pullback agrees with the constant-sheaf Ext pullback.

Source: Stacks Project, Tags 01FD and 01EQ, degree-zero section augmentations.
(blueprint: lem-pc-cech-inverse-image-degree-zero)

Proof: Express x as the restriction class of its unique global section s using
cechCohomologyZeroIso. In each V-member the explicit cochain map sends the
restriction of s to the restriction of the adjunction unit applied to s.
Naturality of the unit and composition of restriction maps prove this equality
of cochains, hence of their degree-zero classes. For Ext, write the degree-zero
class as mk₀ f for a morphism from the constant integer sheaf. Exact inverse
image sends this to mk₀ of the composite constIso.inv followed by the inverse
image of f. The definition of constIso as uniqueness of left adjoints identifies
its constant-sheaf adjunct with the inverse-image unit composed with f. Evaluating
at the integer 1 gives precisely the same pulled-back global section. Apply the
inverse global-section equivalence to conclude. This uses only degree zero and
no comparison system or positive-degree connecting map. If a cover is empty,
the covered scheme and its inverse image are empty and all sections are zero. -/
theorem cechInverseImage_degree_zero
    {X Y : Scheme.{u}} {ι : Type u} (g : Y ⟶ X)
    (U : ι → X.Opens) (V : ι → Y.Opens) (hcover : iSup U = ⊤)
    (hcover' : iSup V = ⊤)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (x : (TopCat.Sheaf.cechCohomologyFunctor U 0).obj F) :
    (((TopCat.Sheaf.cechCohomologyZeroIso V hcover').inv ≫
        (Sheaf.functorHZeroIso.{u} (Opens.grothendieckTopology Y) isTerminalTop).inv).app
        ((invImage g).obj F))
      (HomologicalComplex.homologyMap
        (cechInverseImageCochainMap g U V hinter F ((invImage g).obj F)
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
            F).hom) 0 x) =
      Sheaf.H.mapFunctor (invImage g) (constIso g).symm F 0
        ((((TopCat.Sheaf.cechCohomologyZeroIso U hcover).inv ≫
          (Sheaf.functorHZeroIso.{u} (Opens.grothendieckTopology X) isTerminalTop).inv).app F)
          x) := by sorry

end AlgebraicGeometry.Scheme.Modules
