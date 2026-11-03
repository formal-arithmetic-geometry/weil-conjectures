/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RelativeKunneth.CondensedRelativeKunneth
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit

/-!
# Data and canonical maps for compact Künneth on closed sections

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
  thm-pur-vector-bundle-thom.proof.md`, Steps 1 and 2
(blueprint: lem-pur-compact-kunneth-section-unit).

The source isomorphism is the closed direct-image exchange followed by the
compact-support projection formula and the coefficient unitors.  Its compact image is
then compared by the native relative Künneth isomorphism.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.CompactKunnethSectionUnit

/-- Proper comparison followed by the coherent compositor, compactification
comparison to the identity model, and the identity normalization. This fixes the
unit identification for a closed section; there is no chosen isomorphism.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 5.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
def sectionUnitIso (Λ : ScalarSixRing.{u}) {k : Type u} [Field k]
    (H : RelativeKunneth.CanonicalCompositionData Λ.X k)
    {B X : SepFinType k} (s : B ⟶ X) (f : X ⟶ B)
    [IsProper s.hom.left] (c : Compactification f.hom.left)
    (hs : s.hom.left ≫ f.hom.left = 𝟙 _) :
    (CompactificationReindexing.F Λ.X c).obj
      ((CompactificationReindexing.R Λ.X s.hom.left).obj (𝟙_ _)) ≅ 𝟙_ _ := by
  letI : IsProper (s.hom.left ≫ f.hom.left) := by rw [hs]; infer_instance
  let cs := Compactification.ofIsProper s.hom.left
  let e := Compactification.ofIsProper (s.hom.left ≫ f.hom.left)
  let eId := (Compactification.ofIsProper (𝟙 B.obj.left)).copy hs
  exact (CompactificationReindexing.F Λ.X c).mapIso
      ((properModelIso Λ s.hom.left).symm.app (𝟙_ _)) ≪≫
    (H.comp s f cs c e).app (localizingUnit Λ B) ≪≫
    (H.comparison (s ≫ f) e eId).app (localizingUnit Λ B) ≪≫
    (CompactSupportComposition.identity Λ.X B.obj.left).app (𝟙_ _)

end AlgebraicGeometry.ProEtale.CondensedRing.CompactKunnethSectionUnit
