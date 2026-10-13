/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.PicardTermwiseModels

/-! # Core counit composition calculation

Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: lem-sc-picard-termwise-composite-counit-core)

This is the two-morphism counit factorization on a complex. The general
compatibility equation additionally uses naturality at the fixed morphism
and the associativity law for three derived pullbacks.
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

attribute [local instance] Functor.additive_of_preserves_binary_products

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

/-- Composition of the termwise counits on a complex.

Source: Stacks Project, Tags 06YJ and 0D5S.
(blueprint: lem-sc-picard-termwise-composite-counit-core)

Proof: evaluate the defining left-derived-lift equation for the pinned comparison
at the homotopy class of P = overEquiv(U)(K). Whisker it with the quotient from
complexes. Naturality of quotientCompQhIso and mapHomotopyCategoryFactors rewrites
its three counits as picardTermwiseCounit. The ordinary tensor comparison becomes
the inverse of the termwise model restriction comparison. Precompose with the
inverse derived comparison and postcompose with the ordinary comparison to get
the displayed equation. Only these comparisons are canceled; no counit needs to
be invertible, so this works for zero complexes and empty schemes as well. -/
theorem picard_termwise_counit_composition
    (W : Scheme.{v}) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    {T T' : Scheme.{v}} (i : T' ⟶ T) (s : T ⟶ U.toScheme) :
    let c : ∀ {X Y Z : Scheme.{v}} (f : X ⟶ Y) (g : Y ⟶ Z),
        derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) :=
      fun f g ↦ Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) f g
    let P := ((Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K
    (c i s).inv.app (DerivedCategory.Q.obj P) ≫
        (derivedPullback i).map ((picardTermwiseCounit s).app P) ≫
          (picardTermwiseCounit i).app (picardTermwiseModel W U K s) =
      (picardTermwiseCounit (i ≫ s)).app P ≫
        DerivedCategory.Q.map
          (picardTermwiseModelRestrictionIso W U K i s (i ≫ s) rfl).hom := by sorry

end
end AlgebraicGeometry.Scheme
