module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESCore
import Sheaf.CategoryTheory.DerivedCategory.ConeDiagramSESPresentation

/-! # Construction component for the union SES presentation
(blueprint: new-single-complex-open-union-ses-objects). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option linter.unusedVariables false in
theorem singleComplexOpenComparison_union_ses_objects
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [IsAffine S] [IsAffine S']
    [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (hUqc : IsCompact (U : Set X)) (hVqc : IsCompact (V : Set X))
    (hUVqc : IsCompact ((U ⊓ V : X.Opens) : Set X)) :
    let a : X.Opens → Arrow (schemeDerivedCategory S') := fun Z ↦
      Arrow.mk (singleComplexOpenComparison f f' g g' sq.w K K' φ Z)
    ∃ (P P' : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ))
      (m : P ⟶ P')
      (e₁ : DerivedCategory.Q.obj P.X₁ ≅ (a (U ⊔ V)).left)
      (e₂ : DerivedCategory.Q.obj P.X₂ ≅ (a U).left ⊞ (a V).left)
      (e₃ : DerivedCategory.Q.obj P.X₃ ≅ (a (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ (a (U ⊔ V)).right)
      (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ (a U).right ⊞ (a V).right)
      (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ (a (U ⊓ V)).right),
      P.ShortExact ∧ P'.ShortExact := by
  dsimp only
  let a : X.Opens → Arrow (schemeDerivedCategory S') := fun Z ↦
    Arrow.mk (singleComplexOpenComparison f f' g g' sq.w K K' φ Z)
  obtain ⟨A, B, A', B', t, t', α, β, hc, e₁, e₂, e₃, e₁', e₂', e₃', _⟩ :=
    singleComplexOpenComparison_union_ses_core f f' g g' sq K hK K' hK' φ U V
      hUqc hVqc hUVqc
  obtain ⟨P, P', _m, _d₁, _d₂, _d₃, _d₁', _d₂', _d₃', hP, hP', _⟩ :=
    cone_diagram_ses_presentation A B A' B' t t' α β hc
  exact ⟨P, P', _m, _d₁ ≪≫ e₁, _d₂ ≪≫ e₂, _d₃ ≪≫ e₃,
    _d₁' ≪≫ e₁', _d₂' ≪≫ e₂', _d₃' ≪≫ e₃', hP, hP'⟩

end AlgebraicGeometry
