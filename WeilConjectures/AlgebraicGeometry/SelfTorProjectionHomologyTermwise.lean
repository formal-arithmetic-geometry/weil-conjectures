/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.KFlatSingleTensorRepresentative
import WeilConjectures.AlgebraicGeometry.ClosedStructureTensorComplexProjection
import WeilConjectures.AlgebraicGeometry.ClosedModulePushforwardHomology

/-!
# Termwise computation of self-Tor of a closed subscheme

For a closed immersion `i : Z ⟶ Y` and a K-flat resolution `P` of `i_* 𝒪_Z`, the homology of
`i_* 𝒪_Z ⊗^L i_* 𝒪_Z` is identified with the pushforward of the homology of `i^* P`.

## References

* [Stacks Project, Tag 06YH](https://stacks.math.columbia.edu/tag/06YH)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/--
The K-flat tensor representative and ordinary closed-immersion projection
comparison give an invertible arrow between the displayed homology objects.
-/
theorem exists_selfTor_projection_homology_termwise_arrow
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex Y.Modules ℤ)
    (a : P ⟶ (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hP : CochainComplex.IsKFlatTensorResolution (R := Y.sheaf) a)
    (k : ℤ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    ∃ f : ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj (S.obj B ⊗ S.obj B)) ⟶
      (Scheme.Modules.pushforward i).obj (T.homology k), IsIso f := by
  let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
  obtain ⟨e⟩ := nonempty_kFlat_single_tensor_representative Y B B P a hP
  obtain ⟨p⟩ := nonempty_closedStructure_tensor_complex_projection i P
  have : (Scheme.Modules.pushforward i).PreservesHomology :=
    closed_modulePushforward_preservesHomology i
  let q := e ≪≫ DerivedCategory.Q.mapIso p
  let h := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).mapIso q ≪≫
    (DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).app _ ≪≫
    (T.sc k).mapHomologyIso (Scheme.Modules.pushforward i)
  exact ⟨h.hom, inferInstance⟩

/-- The termwise representative form of the self-Tor projection computation: the `k`-th
homology of `i_* 𝒪_Z ⊗^L i_* 𝒪_Z` is isomorphic to the pushforward of the `k`-th homology
of `i^* P`.
-/
theorem nonempty_selfTor_projection_homology_termwise
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex Y.Modules ℤ)
    (a : P ⟶ (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hP : CochainComplex.IsKFlatTensorResolution (R := Y.sheaf) a)
    (k : ℤ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    Nonempty (((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj (S.obj B ⊗ S.obj B)) ≅
      (Scheme.Modules.pushforward i).obj (T.homology k)) := by
  dsimp
  obtain ⟨f, hIso⟩ := exists_selfTor_projection_homology_termwise_arrow i P a hP k
  let _ : IsIso f := hIso
  exact ⟨asIso f⟩

end AlgebraicGeometry
