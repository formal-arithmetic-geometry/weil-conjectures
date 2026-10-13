/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Sheaf.AlgebraicGeometry.TensorPullback

/-! # Nested open restriction of a single direct image
Source: Stacks Project, Tag 08FE (lemma-restrict-direct-image-open).
(blueprint: lem-pc-nested-open-single-direct-image-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u wX wS wW wY
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products

/-- Nested open restriction of a single direct image.
Source: Stacks Project, Tag 08FE (lemma-restrict-direct-image-open).
Proof: derive the sectionwise identity for open restriction using a K-injective
resolution. Restrict first along U.ι and then along V.ι; both restrictions are exact
and preserve K-injectives, and their composite is restriction along V.ι ≫ U.ι.
Identify the inverse-image open with the pullback of this composite open immersion,
using the unique projection-preserving isomorphism. Its exact coefficient restriction
is tensor pullback along the first projection. Exact functors commute with the single
functor. Compute both right-derived direct images on this restricted resolution.
Localization uniqueness intertwines Qh and hence Q, so the sectionwise comparison
holds for the supplied localization on X and the standard one on the pullback.
Finally apply the inverse exact overEquiv V. The unit and counit cancel the preceding
forward equivalence, yielding the displayed localized comparison. No flatness,
quasi-coherence, quasi-compactness or separatedness is needed. The construction
also applies to empty opens and zero modules.
(blueprint: lem-pc-nested-open-single-direct-image-comparison). -/
theorem nestedOpen_single_directImage_comparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (F : X.Modules) (U : S.Opens)
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (V : U.toScheme.Opens)
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))] :
  let dV := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  letI := dV
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
    (moduleRings (pullback f (V.ι ≫ U.ι)).toRingedSpace))
  Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings U.toScheme.toRingedSpace) V).mapDerivedCategory.obj
      ((schemeOpenRestriction S U).mapDerivedCategory.obj
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F))) ≅
    (@Functor.mapDerivedCategory _ _ _ dV _ _ _ _
      (Scheme.Modules.overEquiv V).inverse _ _ _).obj
      ((schemeDerivedDirectImage (pullback.snd f (V.ι ≫ U.ι))).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          (moduleRings (pullback f (V.ι ≫ U.ι)).toRingedSpace)) 0).obj
          (Scheme.Modules.tensorPullbackObj (pullback.fst f (V.ι ≫ U.ι)) F)))) := by
  sorry

end AlgebraicGeometry
