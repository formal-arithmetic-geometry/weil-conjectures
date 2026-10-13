/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageRawTrianglePullback
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

/-! # Composition of raw triangle pullbacks with arbitrary coefficient maps

Source: Stacks Project, Tags 03CB and 09Z1, canonical inverse-image comparisons.
(blueprint: lem-sbc-raw-triangle-pullback-composition).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Raw triangle pullbacks compose when their coefficient maps are composed using
 the exact derived inverse-image comparison.

Source: Stacks Project, Tags 03CB and 09Z1; the source and shift factors of
lem-sbc-higher-image-raw-pullback-composition-formula, step 2.
(blueprint: lem-sbc-raw-triangle-pullback-composition).

Proof: Expand both triangle pullbacks as `rawTriangleMap`. Map the inner four
factors through the outer derived pullback, using functoriality. Naturality of
its single-functor comparison moves the inner source morphism to the left.
Composition of the single-functor comparisons identifies the source comparison
for the composite. Associativity of underived pullback composition identifies
its free-sheaf factor. Naturality of the derived composition isomorphism moves
it past the arbitrary class. Naturality of commShiftIso moves the inner
coefficient morphism past the outer shift comparison, and compatibility of the
derived composition isomorphism with shifts identifies the two shift factors.
The remaining shifted coefficient map is the composite displayed here.
This argument uses neither a single-complex presentation of K nor any condition
on the coefficient maps; zero objects, identity maps and negative degrees obey
exactly the same naturality and coherence identities. -/
theorem higherDirectImageRawTrianglePullback_comp
    (Λ : Type (u + 1)) [CommRing Λ] {X Y Z S : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (h : Z ⟶ S) (hy : Y ⟶ S) (hx : X ⟶ S)
    (wy : b ≫ h = hy) (wx : a ≫ hy = hx) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((b)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ L)
    (w : D+((a)^*[ModuleCat.{u + 1} Λ]).obj L ⟶ M)
    (U : S.Etale) (z : (higherDirectImagePresheaf Λ h q K).obj (op U)) :
    higherDirectImageRawTrianglePullback Λ (a ≫ b) h hx
        (by rw [Category.assoc, wy, wx]) q K M
        ((upperStarPlusComp (ModuleCat.{u + 1} Λ) a b).hom.app K ≫
          D+((a)^*[ModuleCat.{u + 1} Λ]).map v ≫ w) U z =
      higherDirectImageRawTrianglePullback Λ a hy hx wx q L M w U
        (higherDirectImageRawTrianglePullback Λ b h hy wy q K L v U z) := by
  sorry

end AlgebraicGeometry.Etale
