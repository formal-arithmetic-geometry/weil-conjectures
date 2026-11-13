/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Explicit nonnegative scalar cohomology models

## References

* Stacks Project, Cohomology, Tag 01DZ
* Stacks Project, Varieties, Tag 0BED
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {k : Type w} [Field k] {X : Scheme.{w}}

/-- A fixed injective resolution, using the recorded enough-injectives structure. -/
def picardScalarResolution (F : X.Modules) : InjectiveResolution F :=
  letI : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  injectiveResolution F

/-- Global sections of the fixed resolution with scalars restricted to `k`. -/
def picardScalarResolutionComplex (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) :
    CochainComplex (ModuleCat.{w} k) ℕ :=
  ((ModuleCat.restrictScalars (scalarMap f ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (RingedSpace.globalSectionsComplex (picardScalarResolution F))

/-- Extend the actual sections complex by zero to negative degrees. -/
def picardScalarModel (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) :
    CochainComplex (ModuleCat.{w} k) ℤ :=
  (picardScalarResolutionComplex f F).extend ComplexShape.embeddingUpNat

/-- The constructed model has zero terms in every negative degree. -/
theorem picardScalarModel_negative (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules)
    (p : ℤ) (hp : p < 0) : IsZero ((picardScalarModel f F).X p) := by
  apply HomologicalComplex.isZero_extend_X
  intro n hn
  change (n : ℤ) = p at hn
  omega

/-- The canonical comparison from the homology of the constructed model to scalar
cohomology. -/
def picardScalarModelEquiv (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) (p : ℕ) :
    (picardScalarModel f F).homology (p : ℤ) ≃ₗ[k] scalarCohomology f F p := by
  letI : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  letI := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let I := picardScalarResolution F
  let R := ModuleCat.restrictScalars (scalarMap f ⊤)
  let K := RingedSpace.globalSectionsComplex I
  let e := (picardScalarResolutionComplex f F).extendHomologyIso
    ComplexShape.embeddingUpNat (j := p) rfl
  let e' := (K.sc p).mapHomologyIso R
  let e'' := R.mapIso (I.isoRightDerivedObj
    (RingedSpace.globalSectionsFunctor X.toRingedSpace) p).symm
  exact (e ≪≫ e' ≪≫ e'').toLinearEquiv

end
end AlgebraicGeometry.Scheme.Modules
