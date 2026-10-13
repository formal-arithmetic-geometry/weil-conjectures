module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-! # Compatibility component for the union SES presentation
(blueprint: new-single-complex-open-union-ses-compatibility). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Chain-level component split from the union SES presentation.

Using the restriction maps and the coefficient morphism in the K-injective
models, the induced map of short exact rows commutes degreewise.  Passing to
the derived category and conjugating by the six vertex isomorphisms gives the
three displayed equations; functoriality of pullback pasting and of the
mapping-cylinder construction identifies the middle component with the
biproduct map.  This is the compatibility component of the parent presentation
theorem; the proof is postponed to the corresponding DAG node.
(blueprint: new-single-complex-open-union-ses-compatibility). -/
theorem singleComplexOpenComparison_union_ses_compatibility
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
    (hUVqc : IsCompact ((U ⊓ V : X.Opens) : Set X)) 
    (a : X.Opens → Arrow (schemeDerivedCategory S'))
    (P P' : ShortComplex (CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ))
    (m : P ⟶ P')
    (e₁ : DerivedCategory.Q.obj P.X₁ ≅ (a (U ⊔ V)).left)
    (e₂ : DerivedCategory.Q.obj P.X₂ ≅ (a U).left ⊞ (a V).left)
    (e₃ : DerivedCategory.Q.obj P.X₃ ≅ (a (U ⊓ V)).left)
    (e₁' : DerivedCategory.Q.obj P'.X₁ ≅ (a (U ⊔ V)).right)
    (e₂' : DerivedCategory.Q.obj P'.X₂ ≅ (a U).right ⊞ (a V).right)
    (e₃' : DerivedCategory.Q.obj P'.X₃ ≅ (a (U ⊓ V)).right)
    (hP : P.ShortExact) (hP' : P'.ShortExact) :
    DerivedCategory.Q.map m.τ₁ ≫ e₁'.hom = e₁.hom ≫ (a (U ⊔ V)).hom ∧
    DerivedCategory.Q.map m.τ₂ ≫ e₂'.hom =
      e₂.hom ≫ biprod.map (a U).hom (a V).hom ∧
    DerivedCategory.Q.map m.τ₃ ≫ e₃'.hom = e₃.hom ≫ (a (U ⊓ V)).hom := by sorry

end AlgebraicGeometry
