/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing
import Sheaf.AlgebraicGeometry.ProperUpperShriekComposition
import Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Upper shriek of the differential sheaf between smooth proper curves

Source: Stacks Project, Tags 0BRT and 0ATX
(blueprint: lem-sc-smooth-curve-upper-shriek-differentials).
-/

@[expose] public section

universe u w wX wY

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (X : Scheme.{u})
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

private theorem qc_single (M : X.Modules) [M.IsQuasicoherent] :
    schemeDerivedQCohProperty X
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) := by
  intro n
  by_cases hn : n = 0
  · subst n
    let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).app M
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm ‹M.IsQuasicoherent›
  · let e := (DerivedCategory.homologyFunctorFactors
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).app
        ((CochainComplex.singleFunctor _ 0).obj M)
    have hz := HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.up ℤ) 0 M n hn
    have : IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) :=
      IsZero.of_iso hz e
    let F : SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
      SheafOfModules.free PEmpty.{u+1}
    have hf : IsZero F := by
      rw [IsZero.iff_id_eq_zero]
      apply Sigma.hom_ext
      intro i
      exact PEmpty.elim i
    have hF : F.IsQuasicoherent := inferInstance
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (hf.iso this) hF

private theorem qc_iso {A B : schemeDerivedCategory X} (e : A ≅ B)
    (hA : schemeDerivedQCohProperty X A) : schemeDerivedQCohProperty X B := by
  intro n
  have := hA n
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso e) (hA n)

private theorem qc_shift {A : schemeDerivedCategory X}
    (hA : schemeDerivedQCohProperty X A) (n : ℤ) :
    schemeDerivedQCohProperty X (A⟦n⟧) := by
  intro m
  have := hA (n + m)
  let e := ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).shiftIso n m (n + m) rfl).app A
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm (hA (n + m))

private instance qc_closed : (schemeDerivedQCohProperty X).IsClosedUnderIsomorphisms where
  of_iso e h := qc_iso X e h

private instance qc_stable (n : ℤ) : (schemeDerivedQCohProperty X).IsStableUnderShiftBy n where
  le_shift _A h := qc_shift X h n

private instance qc_stable_all : (schemeDerivedQCohProperty X).IsStableUnderShift ℤ where


/-- For a proper map between smooth proper curves over a field, upper shriek takes the
canonical differential sheaf of the target to that of the source, in degree zero.

Source: Stacks Project, Tags 0BRT and 0ATX
(blueprint: lem-sc-smooth-curve-upper-shriek-differentials).

Proof: Write g and h for the structure maps of Y and X to Spec k. Represent the
structure sheaf of Spec k by its single complex in D_QCoh. Choose the restrictions
of Rg_* and Rh_* to D_QCoh and their right adjoints, using the Noetherian right-adjoint
existence theorem. Smooth proper curve duality identifies their values on O_k with
Omega_Y[1] and Omega_X[1]. Upper-shriek composition identifies h^! with f^! g^!,
since f followed by g is h. The right adjoint f^! commutes with shifts (its left
adjoint is exact). Cancel the shift [1] to obtain f^! Omega_Y = Omega_X. The single
complex of the locally free Omega_Y is quasi-coherent, so it supplies K and eL.
Transport through the supplied comparison and adjunction by uniqueness of right
adjoints. This also treats empty curves; no separability of f is assumed. -/
theorem smoothCurve_upperShriek_differentials
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (comparison : R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X) (adj : R ⊣ a) :
    ∃ K : schemeDerivedQCohCategory Y,
      ∃ _eL : K.obj ≅ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          (Y ↘ Spec (.of k)).relativeDifferentials,
      Nonempty ((a.obj K).obj ≅ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (X ↘ Spec (.of k)).relativeDifferentials) := by
  classical
  let S := Spec (.of k)
  let g := Y ↘ S
  let h := f ≫ g
  have hh : h = X ↘ S := HomIsOver.comp_over (f := f) (S := S)
  have : SmoothOfRelativeDimension 1 h := by rw [hh]; infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ S)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ S)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ S)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ S)
  have : IsNoetherian X := ⟨⟩
  have : IsNoetherian Y := ⟨⟩
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings S.toRingedSpace))
  have := SheafOfModules.isQuasicoherent_unit (R := S.ringCatSheaf)
  let O : schemeDerivedQCohCategory S :=
    ⟨(DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf),
      qc_single S (SheafOfModules.unit S.ringCatSheaf)⟩
  obtain ⟨hg, hRg⟩ := noetherian_schemeDerivedDirectImage_has_rightAdjoint g
  let Rg := (schemeDerivedQCohProperty S).lift
    ((schemeDerivedQCohProperty Y).ι ⋙ schemeDerivedDirectImage g) hg
  let : Rg.IsLeftAdjoint := hRg
  let ug := Rg.rightAdjoint
  let ag : Rg ⊣ ug := Adjunction.ofIsLeftAdjoint Rg
  obtain ⟨hh', hRh⟩ := noetherian_schemeDerivedDirectImage_has_rightAdjoint h
  let Rh := (schemeDerivedQCohProperty S).lift
    ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage h) hh'
  let : Rh.IsLeftAdjoint := hRh
  let uh := Rh.rightAdjoint
  let ah : Rh ⊣ uh := Adjunction.ofIsLeftAdjoint Rh
  obtain ⟨βY⟩ := smoothProperCurve_dualizing k Y g Rg (Iso.refl _) ug ag O (Iso.refl _)
  obtain ⟨βX⟩ := smoothProperCurve_dualizing k X h Rh (Iso.refl _) uh ah O (Iso.refl _)
  obtain ⟨c, hc⟩ := RingedSpace.exists_derivedModuleDirectImageComposition
    f.toLRSHom.toShHom g.toLRSHom.toShHom
  obtain ⟨E, hE⟩ := exists_properUpperShriekComposition f g R comparison Rg (Iso.refl _)
    Rh (Iso.refl _) c hc a ug uh adj ag ah
  have := Scheme.Hom.isInvertible_relativeDifferentials (Y ↘ S)
  let K : schemeDerivedQCohCategory Y :=
    ⟨(DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        (Y ↘ S).relativeDifferentials,
      qc_single Y (Y ↘ S).relativeDifferentials⟩
  have : (schemeDerivedQCohProperty X).IsClosedUnderIsomorphisms := qc_closed X
  have : (schemeDerivedQCohProperty Y).IsClosedUnderIsomorphisms := qc_closed Y
  let : R.CommShift ℤ := Functor.CommShift.ofComp comparison ℤ
  let : a.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let δY : ug.obj O ≅ K⟦(1 : ℤ)⟧ :=
    (schemeDerivedQCohProperty Y).ι.preimageIso
      (βY ≪≫ ((schemeDerivedQCohProperty Y).ι.commShiftIso (1 : ℤ)).symm.app K)
  let δ : ((schemeDerivedQCohProperty X).ι.obj (a.obj K))⟦(1 : ℤ)⟧ ≅
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          h.relativeDifferentials)⟦(1 : ℤ)⟧ :=
    (((schemeDerivedQCohProperty X).ι.commShiftIso (1 : ℤ)).symm.app (a.obj K)) ≪≫
      (schemeDerivedQCohProperty X).ι.mapIso
        (((a.commShiftIso (1 : ℤ)).symm.app K) ≪≫
          a.mapIso δY.symm ≪≫ (E.app O).symm) ≪≫ βX
  refine ⟨K, Iso.refl _, ⟨?_⟩⟩
  have δ₀ := (shiftFunctor (schemeDerivedCategory X) (1 : ℤ)).preimageIso δ
  change (a.obj K).obj ≅ (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj h.relativeDifferentials at δ₀
  rw [hh] at δ₀
  exact δ₀


end AlgebraicGeometry
