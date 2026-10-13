/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.AffinePullbackPerfectDetectsIso
import Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective
import Sheaf.AlgebraicGeometry.DerivedOpenLocalization

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

Proof: Supply derived localizations on opens using
`nonempty_derivedOpenLocalization`. Since both base schemes are affine, g is affine,
and so is its base change. The theorem
`proper_flat_rightAdjoint_affine_baseChange_hom_bijective` gives bijectivity of
composition with the canonical mate map on all shifted Hom groups from affine
pullbacks of perfect complexes. Apply `affinePullbackPerfect_detects_iso`.
That theorem chooses a perfect generator, pulls it back, and proves directly by
exactness of Hom for a distinguished triangle that the cone is zero. The underlying
map is therefore invertible, and the fully faithful quasi-coherent inclusion reflects
this invertibility.
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
  classical
  let : ∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    Classical.choice (nonempty_derivedOpenLocalization X)
  have : QuasiSeparatedSpace (pullback f g : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)
  have : IsAffineHom g := inferInstance
  have : IsAffineHom (pullback.fst f g) := MorphismProperty.pullback_fst f g ‹_›
  apply affinePullbackPerfect_detects_iso (pullback.fst f g)
    (dualityEquationBaseChangeMap f g a a' adjf adjf' hβ K)
  intro M hM m n
  exact proper_flat_rightAdjoint_affine_baseChange_hom_bijective
    g f a a' adjf adjf' hβ K M hM m n

end AlgebraicGeometry
