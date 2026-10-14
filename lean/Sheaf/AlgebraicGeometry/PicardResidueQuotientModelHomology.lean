module
public import Sheaf.AlgebraicGeometry.AffineResidueCycleHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- The explicit residue cycle quotient is additively the degree-one homology
of the scalar extension of sections.  This is the algebraic quotient step of
Tag 010V, independent of the geometric derived comparison.
(blueprint: new-picard-residue-quotient-model-homology) -/
theorem picard_residue_quotient_model_homology
    [∀ Y : Scheme.{v}, HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) :=
      SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
    letI : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
    let C := ((F ⋙ T).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    Nonempty (affineResidueCycleHomology W U p K ≃+ C.homology 1) := by
  sorry
end AlgebraicGeometry.Scheme
