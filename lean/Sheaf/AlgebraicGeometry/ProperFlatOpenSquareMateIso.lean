/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen

import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction

/-! # Invertibility of the open-square mate

Source: Stacks Project, duality.tex, Lemma 48.12.2 (Tag 0E4J).
(blueprint: lem-sc-proper-flat-open-square-mate-isiso).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical right-adjoint mate of a proper-flat morphism along an affine
open immersion is invertible, for any supplied right adjoints and adjunctions.
Source: Stacks Project, duality.tex, Tag 0E4J (part (2)), and Tag 0A9L,
equation-sheafy; the identification with the base-change mate is Tag 0E9S.
(blueprint: lem-sc-proper-flat-open-square-mate-isiso)

Proof: Put U = f inverse(W). Exact restriction to W and U is derived pullback.
The square with U and W is cartesian; its pullback object is canonically isomorphic
to U by the projection equations. Both opens are quasi-compact: W is affine and
f is proper. Derived open direct image preserves quasi-coherent cohomology.
Apply proper_flat_rightAdjoint_restriction_open to the canonical lift of Rf_*
(and, for its second square, use the identity change of base). Its first clause
says that restriction to U of a applied to the open-unit K -> Rj_* j^* K is
invertible. The conjugate of ordinary open base change identifies a Rj_* with
Ri_* a', using the given adjunctions and the direct-image composition comparison.
Apply exact restriction to this identification. The open counit i^* Ri_* -> id
is invertible. Thus the unit, inverse conjugate, counit expression defining
this canonical mate is a composite of three invertible arrows. The projection
comparison transports this conclusion from U to the canonical pullback scheme.
Uniqueness of right adjoints transports it to the supplied a' and its adjunction.
This argument applies to all unbounded quasi-coherent objects and to the empty open;
it does not use global invertibility of proper-flat base change.
-/
theorem proper_flat_openSquare_mate_isIso
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (W : Y.Opens) [IsAffine W.toScheme]
    (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory W.toScheme ⥤ schemeDerivedQCohCategory (pullback f W.ι))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty W.toScheme).lift
      ((schemeDerivedQCohProperty (pullback f W.ι)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f W.ι)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f W.ι)) _ _ _ _
          (pullback.snd f W.ι) _ _).fst E.obj E.property) ⊣ a')
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f W.ι) W.ι (pullback.fst f W.ι)
        pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y) :
    IsIso (@dualityEquationBaseChangeMap _ X Y W.toScheme
      (QuasiCompact.compactSpace_of_compactSpace f)
      (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
      f W.ι a a' adjf adjf' hβ K) := by sorry

end AlgebraicGeometry
