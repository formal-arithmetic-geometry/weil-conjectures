/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.DerivedHomPushforwardKFlatModel
import WeilConjectures.AlgebraicGeometry.ClosedModulePushforwardHomology

/-! # Closed-immersion self-Ext on fixed resolution representatives

## References

* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- The self-Ext sheaf is the pushforward of the Hom-complex homology, for any
K-flat resolution of the pushed-forward structure sheaf and any K-injective
resolution of the structure sheaf on the closed subscheme. -/
theorem nonempty_selfExt_pushforward_homology
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex Y.Modules ℤ) (J : CochainComplex Z.Modules ℤ)
    (a : P ⟶ (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (b : (HomologicalComplex.single Z.Modules (.up ℤ) 0).obj
      (SheafOfModules.unit Z.ringCatSheaf) ⟶ J)
    (hP : CochainComplex.IsKFlatTensorResolution (R := Y.sheaf) a)
    (hb : QuasiIso b) (hJ : J.IsKInjective) (k : ℤ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    Nonempty (((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj
        (H.obj (op (S.obj B), S.obj B))) ≅
      (Scheme.Modules.pushforward i).obj ((homComplex (R := Z.sheaf) T J).homology k))
    := by
  let Q := DerivedCategory.Q (C :=
    SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let F := Scheme.Modules.pushforward i
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let B := F.obj (SheafOfModules.unit Z.ringCatSheaf)
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
  let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf
  let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
  let C : CochainComplex Z.Modules ℤ := homComplex (R := Z.sheaf) T J
  let : F.PreservesHomology := closed_modulePushforward_preservesHomology i
  let : QuasiIso a := hP.1
  let : QuasiIso b := hb
  have ha : IsIso (Q.map a) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) a).2 inferInstance
  have hf : IsIso (Q.map (Fc.map b)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (Fc.map b)).2 inferInstance
  let ea : Q.obj P ≅ S.obj B := asIso (Q.map a)
  let eb : S.obj B ≅ Q.obj (Fc.obj J) :=
    (Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app
        (SheafOfModules.unit Z.ringCatSheaf))).symm ≪≫
      asIso (Q.map (Fc.map b))
  obtain ⟨e⟩ := nonempty_derivedHom_pushforward_kFlat_model i P J hP.2 hJ
  let h := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k
  exact ⟨h.mapIso (H.mapIso (ea.op.prod eb) ≪≫ e) ≪≫
    (DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).app
      (Fc.obj (homComplex (R := Z.sheaf) T J)) ≪≫
    (C.sc k).mapHomologyIso F⟩

end AlgebraicGeometry
