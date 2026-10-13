/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
import Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Invertibility of the right-adjoint mate along an affine open

Source: Stacks Project, duality.tex, Remark 48.6.1 (Tag 0E9S).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical right-adjoint mate for base change along an affine open is invertible.
Source: Stacks Project, duality.tex, Lemma 48.12.2 (Tag 0E4J), part (2),
and Lemma 48.5.2 (Tag 0ATR).
(blueprint: lem-sc-right-adjoint-mate-affine-open-is-iso)

Proof: Identify the canonical pullback of f along V.ι with the restriction of f
using pullbackRestrictIsoRestrict. Open derived pullback is exact restriction.
The restricted direct images and their adjunctions agree under this identification
by direct-image composition and uniqueness of right adjoints. The canonical mate
is the sheafy map: apply a to the open unit, restrict to the inverse-image open,
and then apply the conjugate direct-image comparison and the open counit.
The last two factors are isomorphisms. The first factor is invertible by
proper_flat_rightAdjoint_restriction_open, since an affine open is quasi-compact.
The triangle identities identify this factorization with the fixed canonical mate,
so the mate is invertible. This holds for any supplied right adjoint and adjunction:
uniqueness transports the factorization compatibly with units and counits.
For the empty open both source and target are zero; for the total affine open
this is the identity-square mate, so both edge cases obey the same argument.
-/
theorem rightAdjoint_mate_affineOpen_isIso
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (V : Y.Opens) [IsAffine V.toScheme]
    (aV : schemeDerivedQCohCategory V.toScheme ⥤
      schemeDerivedQCohCategory (pullback f V.ι))
    (adjV : (schemeDerivedQCohProperty V.toScheme).lift
      ((schemeDerivedQCohProperty (pullback f V.ι)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f V.ι)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f V.ι)) _ _ _ _
          (pullback.snd f V.ι) _ _).fst E.obj E.property) ⊣ aV)
    (hβ₀ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f V.ι) V.ι
        (pullback.fst f V.ι) pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y) :
    IsIso ((schemeDerivedQCohProperty (pullback f V.ι)).ι.map
      (@dualityEquationBaseChangeMap _ X Y V.toScheme
        (QuasiCompact.compactSpace_of_compactSpace f)
        (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
        f V.ι a aV adjf adjV hβ₀ K)) := by sorry

end AlgebraicGeometry
