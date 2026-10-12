/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint
import Sheaf.AlgebraicGeometry.SmoothDiagonalKoszulRegular
import Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation
import Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant


/-! # Diagonal evaluation with the shifted normal determinant

Source: Stacks Project, Tag 0BRT, the displayed chain in the proof of Lemma 48.15.7.
(blueprint: lem-sc-smooth-proper-dualizing-tensor-evaluation).
-/

@[expose] public section

universe u wX wS

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

private theorem qc_single (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : X.Modules) [M.IsQuasicoherent] :
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
    have : CategoryTheory.Limits.IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) :=
      CategoryTheory.Limits.IsZero.of_iso hz e
    let F : SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
      SheafOfModules.free PEmpty.{u+1}
    have hf : CategoryTheory.Limits.IsZero F := by
      rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
      apply CategoryTheory.Limits.Sigma.hom_ext
      intro i
      exact PEmpty.elim i
    have hF : F.IsQuasicoherent := inferInstance
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (hf.iso this) hF


/-- Diagonal evaluation identifies the tensor product of the relative dualizing object
with the shifted determinant of the dual of relative differentials with the derived unit.
Source: Stacks Project, Tag 0BRT, displayed chain in the proof of Lemma 48.15.7.
(blueprint: lem-sc-smooth-proper-dualizing-tensor-evaluation).

Proof: properness gives finite type, so X and P = X ×_S X are Noetherian. Choose
right adjoints to the quasi-coherent restrictions of the diagonal and second projection
pushforwards by the Noetherian adjoint theorem. The smooth diagonal is a Koszul-regular
closed immersion of codimension d, perfect and proper. Smoothness gives flatness, so
Tag 0E2Q identifies O_X with c(Lpr₁* a(O_S)). Apply the perfect-immersion tensor formula
of Tag 0A9U to identify this with LΔ* Lpr₁* a(O_S) ⊗ c(O_P). Since Δ ≫ pr₁ is the
identity, functoriality of derived pullback identifies the first factor with a(O_S).
Tag 0BR0 identifies the second factor with the normal determinant shifted by -d.
The diagonal conormal is relative differentials by Tag 08S2, and these differentials
are finite locally free of rank d. Hence the rank-stratified Koszul-dual object is the
constant shift displayed here. Transport the exterior power along the conormal
isomorphism and take the inverse of the resulting evaluation isomorphism. Finally
identify the single structure sheaf with the recorded derived tensor unit. Uniqueness
of right adjoints transports from the canonical restricted direct image to R via
comparison; hO transports from the degree-zero structure object to O. The two derived
universes are handled by equivalences between derived localizations, so no additional
same-universe assumption is needed. This proves the formula for the specified a, adj,
R and O. No determinant cancellation is used in this step. -/
theorem smoothProper_dualizing_tensor_evaluation
    (X S : Scheme.{u}) [CompactSpace S] [IsLocallyNoetherian S]
    (f : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory S)
    (comparison : R ⋙ (schemeDerivedQCohProperty S).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory X)
    (adj : R ⊣ a) (O : schemeDerivedQCohCategory S)
    (hO : O.obj ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings S.toRingedSpace))) :
    Nonempty (((a.obj O).obj ⊗
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (Scheme.Modules.exteriorSheaf
            (SheafOfModules.homObj (R := X.sheaf) f.relativeDifferentials
              (SheafOfModules.unit X.ringCatSheaf)) d))⟦-(d : ℤ)⟧) ≅
      𝟙_ (schemeDerivedCategory X)) := by
  classical
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : Flat f := inferInstance
  have : IsNoetherian S := ⟨⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  let P := CategoryTheory.Limits.pullback f f
  have : IsLocallyNoetherian P :=
    LocallyOfFiniteType.isLocallyNoetherian (CategoryTheory.Limits.pullback.fst f f)
  have : CompactSpace P :=
    QuasiCompact.compactSpace_of_compactSpace (CategoryTheory.Limits.pullback.fst f f)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings P.toRingedSpace))
  let (U : P.Opens) := HasDerivedCategory.standard
    (SheafOfModules.{u} ((moduleRings P.toRingedSpace).over U))
  obtain ⟨_, hperfect, _⟩ := smooth_diagonal_koszul_regular_perfect_proper d f
  obtain ⟨hRΔ, hleft⟩ := noetherian_schemeDerivedDirectImage_has_rightAdjoint
    (CategoryTheory.Limits.pullback.diagonal f)
  let RΔ := (schemeDerivedQCohProperty P).lift
    ((schemeDerivedQCohProperty X).ι ⋙
      schemeDerivedDirectImage (CategoryTheory.Limits.pullback.diagonal f)) hRΔ
  let : RΔ.IsLeftAdjoint := hleft
  let c := RΔ.rightAdjoint
  let adjC : RΔ ⊣ c := Adjunction.ofIsLeftAdjoint RΔ
  have := SheafOfModules.isQuasicoherent_unit (R := P.ringCatSheaf)
  let OP : schemeDerivedQCohCategory P :=
    ⟨(DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0).obj
        (SheafOfModules.unit P.ringCatSheaf),
      qc_single P (SheafOfModules.unit P.ringCatSheaf)⟩
  obtain ⟨e⟩ := perfectDiagonal_dualizing_evaluation X S f hperfect
    R comparison a adj O hO hRΔ c adjC OP (Iso.refl _)
  obtain ⟨n⟩ := smoothDiagonal_dualizing_determinant X S f d
    hRΔ c adjC OP (Iso.refl _)
  exact ⟨MonoidalCategory.tensorIso (Iso.refl (a.obj O).obj) n.symm ≪≫ e⟩

end AlgebraicGeometry
