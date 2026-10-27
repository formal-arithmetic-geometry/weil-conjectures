/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Ideal.Maps
import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-!
# Flat pullback and powers of quasi-coherent ideals

Source: blueprint, Nagata compactification, sketch of blow-ups, lemma
`lemma-nagata-flat-pullback-ideal-pow` (main-20261015).
(blueprint: lemma-nagata-flat-pullback-ideal-pow).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The image in the structure sheaf of the pullback of `I ^ n` is the `n`th power
of the extended ideal, for a flat scheme morphism.
Source: blueprint, Nagata compactification, sketch of blow-ups,
`lemma-nagata-flat-pullback-ideal-pow` (main-20261015).
(blueprint: lemma-nagata-flat-pullback-ideal-pow).

Proof:
1. The quasi-coherent ideal powers are constructed by def-sbc-ideal-sheaf-powers.
   For each power take its associated closed subscheme, using
   lem-weil-pbc-quasi-coherent-ideal-closed-subscheme.
2. By lem-pc-closed-subscheme-base-change-ideal-image, the ideal of the
   base-changed closed subscheme is the image of the pulled-back inclusion followed
   by the adjoint structure-sheaf map. By def-nagata-extended-ideal this is the
   extended ideal of that power; def-sbc-closed-immersion-ideal-sheaf makes it
   quasi-coherent. The normalized adjunction in def-pc-module-pullback supplies
   the canonical structure-sheaf map appearing in the statement.
3. Use lem-weil-pbc-affine-opens-basis to cover the source by affine opens V
   lying over affine opens U of the target. By lem-pc-ideal-sheaf-comap-affine-extension,
   the extended ideal of I^m has sections I(U)^m B, where B = O_Y(V).
   This computes the sheaf image, without asserting that sections preserve images.
4. Apply the general ring-map clause of lemma-nagata-localization-ideal-pow:
   (I(U)^n)B = (I(U)B)^n. The affine power formula identifies the right-hand side
   with the sections of (I O_Y)^n. At n = 0 both ideals are the unit ideal.
5. The same adapted affine opens cover every open subset of Y. Equality there
   gives both inclusions globally by local membership and sheaf gluing, since
   both ideals are subsheaves of the structure sheaf. This proves equality of
   subobjects. Flatness is retained as stated, although the image equality itself
   holds for any scheme morphism. -/
theorem image_tensorPullback_ideal_pow {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (g : Y ⟶ X) [Flat g] (n : ℕ) :
    imageSubobject
      ((Scheme.Modules.tensorPullback g).map (I ^ n).toModulesι ≫
        ((Scheme.Modules.tensorPullbackSectionAdjunction g).homEquiv
          (SheafOfModules.unit X.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf)).symm
            (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)) =
      Subobject.mk ((I.comap g) ^ n).toModulesι := by
  sorry

end AlgebraicGeometry
