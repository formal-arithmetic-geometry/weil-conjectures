/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-! Affine base change for the right adjoint of a proper flat morphism.

Source: Stacks Project, `duality.tex`, Tag 0AA8 (Lemma 48.6.2), case (1).
(blueprint: lem-sc-proper-flat-right-adjoint-affine-basechange).

The displayed morphism is the canonical mate-defined morphism recorded in
`dualityEquationBaseChangeMap`; the hypothesis `hβ` records the base-change
isomorphism used in that definition.
-/
/-- Affine base change for the right adjoint of a proper flat morphism.
Source: Stacks Project, duality.tex, Tag 0AA8 (Lemma 48.6.2), case (1).
(blueprint: lem-sc-proper-flat-right-adjoint-affine-basechange).

Proof plan: (1) write the affine schemes as spectra.  Flatness and the
flat-complex base-change lemma make the base-change transformation for
`Rf_*` an isomorphism, and flatness gives the required Tor-independence.
(2) Choose a perfect generator of `D_QCoh(X)`, pull it back along the affine
map `g_X`, and apply the proper-support perfect direct-image theorem to obtain
perfectness and arbitrary base change for its direct image.  (3) Apply the
flat-precomposition comparison to the canonical mate map; the pullback Hom
comparison, global Hom adjunctions, the perfect RHom base-change theorem, and
the inverse of the base-change isomorphism identify its image as an
isomorphism.  (4) The pulled-back perfect generator detects zero cones, so the
mate map is an isomorphism; this holds for every `K`.
-/
theorem proper_flat_rightAdjoint_affine_baseChange
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' : Scheme.{u}} [IsAffine Y] [IsAffine Y']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory Y' ⥤
      schemeDerivedQCohCategory (pullback f g))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
      (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y f).fst E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g))
      (fun E ↦ (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
        (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
        (pullback.snd f g) _ _).fst E.obj E.property) ⊣ a')
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y) :
    IsIso (dualityEquationBaseChangeMap f g a a' adjf adjf' hβ K) := by
  sorry

end AlgebraicGeometry
