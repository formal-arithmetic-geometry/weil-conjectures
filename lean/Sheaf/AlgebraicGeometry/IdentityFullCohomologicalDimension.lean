/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Full cohomological dimension of an identity

Source: blueprint `sk-thm-sf-global-duality/lem-sf-point.proof.md`, identity-adjunction
sentence, expanded in step 2 of `lem-sf-point-identity-admissibility`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

private theorem directImage_isEquivalence {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (A : Type u) [CommRing A] [Finite A] :
    (proEtaleConstantModuleDirectImage f A).IsEquivalence := by
  let EX := sfIntrinsicModuleEquivalence X A
  let EY := sfIntrinsicModuleEquivalence Y A
  let F := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f
  let G := proEtaleConstantModuleDirectImage f A
  let e : G ≅ EX.inverse ⋙ F ⋙ EY.functor :=
    (EX.invFunIdAssoc G).symm ≪≫
      Functor.isoWhiskerLeft EX.inverse (sfIntrinsicDirectImageComparison f A)
  exact Functor.isEquivalence_of_iso e.symm

private theorem positive_directImage_single {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A)) (r : ℤ) (hr : 0 < r) :
    IsZero ((DerivedCategory.homologyFunctor _ r).obj
      ((proEtaleConstantDerivedDirectImage f A).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  let G := proEtaleConstantModuleDirectImage f A
  have : G.IsEquivalence := directImage_isEquivalence f A
  let e : (proEtaleConstantDerivedDirectImage f A).obj
        ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      (DerivedCategory.singleFunctor _ 0).obj (G.obj F) :=
    G.rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
      (G.mapDerivedCategorySingleFunctor 0).app F
  exact ((DerivedCategory.isLE_iff _ 0).mp (by infer_instance) r hr).of_iso
    ((DerivedCategory.homologyFunctor _ r).mapIso e)

/-- Identity direct image has full cohomological dimension zero, on all module sheaves.

Source: blueprint `sk-thm-sf-global-duality/lem-sf-point.proof.md`, identity-adjunction
sentence; parent proof steps 1--2.
(blueprint: lem-sf-identity-full-cohomological-dimension).

Proof: on test objects, pullback along id identifies V ×_s s with V. This identifies
constant-module direct image along id with the identity exact functor, compatibly
with restriction and the constant-ring action. Its unbounded right derived functor
is therefore identity. Applied to a sheaf placed in degree zero it has zero
cohomology in every positive degree. For any pro-etale V over s, the projection
s ×_s V --> V is canonically an isomorphism; direct image along it is an exact
equivalence. The pulled-back sheaf is still placed in degree zero, so the same
vanishing proves the second clause. This works for every sheaf, arbitrary V,
non-Noetherian s, and even the zero coefficient ring. -/
theorem sfFullCohomologicalDimension_identity (s : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    sfFullCohomologicalDimension (𝟙 s) A 0 := by
  constructor
  · intro F r hr
    exact positive_directImage_single (𝟙 s) A F r hr
  · intro V F r hr
    exact positive_directImage_single (pullback.snd (𝟙 s) V.hom) A _ r hr

end AlgebraicGeometry.Scheme
