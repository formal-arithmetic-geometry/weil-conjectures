/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel
import Sheaf.AlgebraicGeometry.ProjectiveNoetherianDirectImagePerfect

/-! # Arbitrary base change for a projective Noetherian family

Source: Weil conjectures blueprint, sec-picard-framework/sk-thm-picard-semicon,
cor-pc-projective-noetherian-rf-perfect-base-change, order 674
(blueprint: cor-pc-projective-noetherian-rf-perfect-base-change).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical base-change map for a coherent relatively flat module on a projective
family over a locally Noetherian base is invertible, and its source and target are perfect.
No Noetherian condition is imposed on the new base T. The predicate on φ identifies the
canonical map, rather than an arbitrary isomorphism between its endpoints. Localization
instances choose derived-category models; additivity of tensor pullback is its usual
left-adjoint property, included to type the canonical-map predicate.
Source: Weil conjectures blueprint, sec-picard-framework/sk-thm-picard-semicon,
cor-pc-projective-noetherian-rf-perfect-base-change, order 674
(blueprint: cor-pc-projective-noetherian-rf-perfect-base-change).

Proof:
1. By def-pc-projective-morphism, f is quasi-compact and factors through a closed
   immersion into projective space. Projective space is proper by
   lemma-nagata-projective-space-base-change-proper; composition with the immersion is
   proper by lem-weil-pbc-closed-immersion-proper, hence separated by
   def-weil-proper-morphism. Coherence gives local finite presentations, and
   lem-weil-pbc-quasi-coherent-finite-type-affine gives quasi-coherence. Apply
   lem-pc-rf-base-change-flat-module to identify the canonical map of
   def-pc-derived-module-base-change-map as an isomorphism for arbitrary g.
2. Apply lem-pc-projective-noetherian-rf-perfect: Rf_*G is perfect. By
   def-pc-perfect-complex, locally it has a bounded finite-projective representative.
3. The local comparison lem-pc-localized-pullback-perfect-model and the computation
   lem-pc-flat-complex-derived-pullback identify its derived pullback with termwise
   tensor pullback. A finite-projective term is a retract of a finite free module;
   pulling back the splitting preserves that retract. Zero terms stay zero, so the
   pulled-back complex is strictly perfect. Inverse images of the original opens cover
   T, proving perfectness of the source; the isomorphism transfers it to the target. -/
theorem projectiveNoetherian_perfect_baseChange
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S T : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProjective f]
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hflat : Scheme.Modules.IsFlatOver G f) (g : T ⟶ S)
    [(Scheme.Modules.tensorPullback (pullback.fst f g)).Additive]
    [∀ U : T.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U))] :
    Scheme.IsPerfect T
      ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G))) ∧
    Scheme.IsPerfect T
      ((schemeDerivedDirectImage (pullback.snd f g)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))) ∧
    ∀ φ : (derivedPullback g).obj ((schemeDerivedDirectImage f).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)) ⟶
      (schemeDerivedDirectImage (pullback.snd f g)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G)),
      IsDerivedModuleBaseChangeMap f g G φ → IsIso φ := by
  sorry

end AlgebraicGeometry
