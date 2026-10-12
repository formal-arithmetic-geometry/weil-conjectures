/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.AffineAlternatingCechModel
public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.CechResolution
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections

/-! # The alternating Čech calculation for the pinned derived mate

Source: Stacks Project, Tags 02KH and 08HY; Steps 1--3 of
`lem-pc-affine-alternating-cech-base-change-factorization`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Compute the mate using precisely the family of counits that defines the
canonical derived composition and adjunction comparisons. This lemma makes no
assertion about a comparison supplied by a caller or a different counit.
Source: Stacks Project, Tags 02KH and 08HY; Steps 1--3 of
`lem-pc-affine-alternating-cech-base-change-factorization`.
(blueprint: lem-pc-affine-alternating-cech-pinned-mate).

Proof: Form the augmented increasing-tuple sheaf Čech complex. On each cover member
insert its index, sort with the permutation sign, and set repeated indices to zero;
the alternating face cancellation gives a contraction. Every intersection is affine
because f is separated over an affine base. The open pushforward of the restricted
quasi-coherent module is f_*-acyclic, so the acyclic resolution comparison identifies
Rf_*G[0] with the explicit sheafified section complex, giving e. Perform the same
construction on the pulled-back cover to compute the target direct image. On each
intersection the affine section-pullback isomorphism sends s tensor b to b times
the pulled-back section s. It commutes with restrictions and with the signed face
sums. Tensor commutes with the finite products in each degree, giving a complex
isomorphism after ordinary g-pullback. Compose its localization with the target
acyclic-resolution comparison to obtain t. Transpose the mate under the pinned
derived adjunction for the base-changed morphism. Evaluate its unit and counit on
the Čech augmentation; the naturality and triangle identities cancel the units.
The remaining maps on every intersection are the pure-tensor maps just described.
The pinned composition comparisons are defined by the same derived counits, so
the transposed equality descends to the displayed equality. There is no need to
invert the counit on K and no flatness hypothesis. An empty cover forces X empty,
and the same construction uses the zero complexes. -/
theorem affineAlternatingCech_pinned_mate
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [QuasiCompact f] [IsSeparated f] (g : Spec B ⟶ Spec A)
    {r : ℕ} (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i))
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback (pullback.fst f g)).Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G] :
    ∃ (e : (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≅
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (affineAlternatingCechModel f U G)))
        (t : DerivedCategory.Qh.obj (((show
          SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace) ⥤
          SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace) from
          Scheme.Modules.tensorPullback g).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (affineAlternatingCechModel f U G))) ≅
          (schemeDerivedDirectImage (pullback.snd f g)).obj ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
              ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))),
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
        (schemeDerivedDirectImage (pullback.snd f g)).map
          (((Classical.choose (Classical.choose_spec
              exists_derivedPullbackComposition.{u, w})) (pullback.fst f g)).app
            ((HomotopyCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
            DerivedCategory.Qh.map
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
                ((HomologicalComplex.singleMapHomologicalComplex
                  (Scheme.Modules.tensorPullback (pullback.fst f g))
                  (ComplexShape.up ℤ) 0).hom.app G))) =
          (derivedPullback g).map e.hom ≫
            ((Classical.choose (Classical.choose_spec
              exists_derivedPullbackComposition.{u, w})) g).app 
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
              (affineAlternatingCechModel f U G)) ≫ t.hom := by sorry

end AlgebraicGeometry
