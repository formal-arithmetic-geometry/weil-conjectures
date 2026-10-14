module
public import Sheaf.AlgebraicGeometry.AffineResidueCycleHomology
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.AlgebraicGeometry.PerfectComplex
@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- The geometric comparison reduces the residue fibre to homology of the
scalar extension of the section complex.  This is the derived-model part of
Tags 01IB, 064K, 06YJ and 010V; the explicit quotient comparison is separate.
(blueprint: new-picard-residue-source-model-homology) -/
theorem picard_residue_source_model_homology
    [∀ Y : Scheme.{v}, HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) :=
      SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
    letI : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
    let C := ((F ⋙ T).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    Nonempty (derivedFiberCohomology W E 1 w ≃ₗ[W.residueField w] C.homology 1) := by
  sorry
end AlgebraicGeometry.Scheme
