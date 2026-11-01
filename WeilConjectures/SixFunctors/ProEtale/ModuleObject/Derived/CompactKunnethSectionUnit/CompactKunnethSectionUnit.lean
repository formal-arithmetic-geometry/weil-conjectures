/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RelativeKunneth.CondensedRelativeKunneth
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-!
# Normalization of compact Künneth on closed sections

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

/-- The pullback lift of the closed section along the product projection.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, Step 1; this is the
base-change section `a : Z_s → P` with coordinates `(g ≫ s, 1)`.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
noncomputable def sectionMap {datum : WeilConjectures.FiniteFieldDatum.{u}}
    (d : RelativeKunneth.Diagram datum.k)
    (s : d.B ⟶ d.X) (_t : d.B ⟶ d.Y)
    (hs : s.hom.left ≫ d.f.hom.left = 𝟙 _) : d.Y ⟶ d.T :=
  SepFinType.homMk (Over.homMk
    (d.cartesian.lift (d.g.hom.left ≫ s.hom.left) (𝟙 _)
      (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp]))
    (by
      rw [← d.q.hom.w, ← Category.assoc, d.cartesian.lift_snd, Category.id_comp]))


/-- The first coordinate of the Cartesian lift a is gs.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 1.
Proof: apply the first projection identity of the Cartesian lift.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
theorem sectionMap_p {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ}
    [Fact ell.Prime] (I : Input datum ell) :
    (sectionMap I.d I.s I.t I.hs).hom.left ≫ I.d.p.hom.left =
      I.d.g.hom.left ≫ I.s.hom.left := by
  change I.d.cartesian.lift (I.d.g.hom.left ≫ I.s.hom.left) (𝟙 _) _ ≫
      I.d.p.hom.left = I.d.g.hom.left ≫ I.s.hom.left
  exact I.d.cartesian.lift_fst _ _ _

/-- The second coordinate of a is the identity.
Source: blueprint `lem-pur-compact-kunneth-section-unit`, proof Step 1.
Proof: apply the second projection identity of the Cartesian lift.
(blueprint: lem-pur-compact-kunneth-section-unit). -/
theorem sectionMap_q {datum : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ}
    [Fact ell.Prime] (I : Input datum ell) :
    (sectionMap I.d I.s I.t I.hs).hom.left ≫ I.d.q.hom.left = 𝟙 _ := by
  change I.d.cartesian.lift (I.d.g.hom.left ≫ I.s.hom.left) (𝟙 _) _ ≫
      I.d.q.hom.left = 𝟙 _
  exact I.d.cartesian.lift_snd _ _ _

end AlgebraicGeometry.ProEtale.CondensedRing.CompactKunnethSectionUnit
