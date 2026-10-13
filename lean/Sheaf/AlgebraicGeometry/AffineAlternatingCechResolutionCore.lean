/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module
public import Sheaf.AlgebraicGeometry.AffineAlternatingCechModel
public import Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.AffineOpenPushforwardAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections
import Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Core alternating Cech resolution data and the four comparison isomorphisms.
Source: Stacks Project, Tags 02KG and 02KH; the Cech resolution and acyclicity
paragraphs of `lem-pc-affine-alternating-cech-pinned-mate`.
(blueprint: lem-pc-s3-affine-alternating-cech-resolution-core).
Proof: In nonnegative degree k use one open pushforward of G restricted to each
strictly increasing (k+1)-tuple intersection of the cover, and the finite product
of these factors. In negative degrees and when there are no such tuples, use the
empty product, a zero object. The intersections are affine by separatedness over
the affine base, including the empty intersection opens. Enumerate each finite
index type by Fin n to obtain the asserted degreewise isomorphisms. The signed
restriction differential squares to zero by cancellation of the two ways of
deleting two indices; augment by the restriction maps from G. On each cover open,
insert its index, sort with sign, and send repetitions to zero. This contracts
the augmented complex; the same additive homotopy after pullback proves both
localized augmentations invertible without assuming tensor exactness.
The increasing tuple complex is contracted by insertion of a cover index. Every
intersection is affine, hence its open pushforward is right-acyclic; the bounded
below derived unit criterion and its compatibility transport the result to the
unbounded complex and to the pulled-back cover. The affine tilde comparison
identifies its pushforward with the displayed model: on each affine intersection
use the tilde-Gamma comparison and its naturality for restrictions, then take the
finite product. Choose D to be the homotopy quotient of this constructed complex,
so the representative isomorphism is reflexive. For an empty cover X is empty
and the zero complex supplies all the assertions. No witness is used to define
an arbitrary complex. -/
theorem affineAlternatingCech_resolution_core
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [QuasiCompact f] [IsSeparated f] (g : Spec B ⟶ Spec A)
    {r : ℕ} (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i))
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback (pullback.fst f g)).Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G] :
    ∃ (D : HomotopyCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
      (a : (HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G ⟶ D)
      (q : ((Scheme.Modules.pushforward f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj D ≅
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (affineAlternatingCechModel f U G)),
      IsIso (DerivedCategory.Qh.map a) ∧
      IsIso ((DerivedCategory.Qh (C := SheafOfModules.{u}
        (moduleRings (pullback f g).toRingedSpace))).map
        (((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomotopyCategory
          (ComplexShape.up ℤ)).map a)) ∧
      IsIso ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app D) ∧
      IsIso ((RingedSpace.moduleDirectImage
        (pullback.snd f g).toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj D)) ∧
      (∃ C : CochainComplex
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
        Nonempty (D ≅ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ∧
        ∀ k : ℤ, ∃ (n : ℕ) (W : Fin n → X.Opens),
          (∀ j, IsAffineOpen (W j)) ∧
          Nonempty (C.X k ≅ ∏ᶜ fun j : Fin n ↦
            (Scheme.Modules.pushforward (W j).ι).obj (G.restrict (W j).ι))) := by sorry
end AlgebraicGeometry
