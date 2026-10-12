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
import Sheaf.AlgebraicGeometry.DiagonalConormalDifferentials
import Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure
import Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing
import Sheaf.AlgebraicGeometry.NoetherianDerivedDirectImageRightAdjoint
import Sheaf.AlgebraicGeometry.SmoothDiagonalKoszulRegular
import Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula


/-! # Diagonal evaluation with the shifted normal determinant

Source: Stacks Project, Tag 0BRT, the displayed chain in the proof of Lemma 48.15.7.
(blueprint: lem-sc-smooth-proper-dualizing-tensor-evaluation).
-/

@[expose] public section

universe u wX wS

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

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
      𝟙_ (schemeDerivedCategory X)) := by sorry

end AlgebraicGeometry
