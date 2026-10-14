module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Compatible strict chain models for a source-open union

Source: Stacks Project, Tags 08HZ, 08HY, 0DJ9 and 013N--013O.
(blueprint: new-single-complex-open-union-compatible-chain-data).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Compatible chain models before the short exact cylinder construction.

Source: Stacks Project, Tags 08HZ, 08HY and 0DJ9; Tags 013N--013O for
strictification of the resolved diagram.
(blueprint: new-single-complex-open-union-compatible-chain-data).

Proof: Resolve the two coefficients on the union and its inverse image by
injective-term K-injective complexes. For each two-open cover, the restriction
pair followed by the restriction difference is short exact: gluing identifies
the kernel and flasqueness of injectives gives surjectivity onto the overlap.
Resolve the finite diagrams for derived direct image and base pullback, using
K-flat resolutions for pullback. Transpose the coefficient map under the
pullback/direct-image adjunction and lift it to these resolutions. Naturality
of restriction gives a square of first differentials up to its specified chain
homotopy. Rectify this square with the functorial cylinder, transporting the
cone comparison along the induced homotopy equivalences, to obtain a strict
square tβ = αt'. The cone computes the overlap term by the restriction short
exact row. Identify the localized first, middle and cone objects with the
relative images, using exact open restriction and direct-image composition;
additivity identifies the middle vertex with the displayed biproduct.
Expand singleComplexOpenComparison as the base-change mate followed by the
restricted coefficient arrow. Pullback pasting, the composite counit identity
and the adjunction triangle identities identify the induced α, β and cone map
with the three specified arrows. Keep the homotopy term during rectification;
choosing zero maps or an arbitrary triangle completion would not suffice.
Empty opens and zero coefficients give zero complexes, while repeated or
contained opens give split rows. No invertibility of the coefficient arrow
is needed. The witnesses are only existential theorem data. -/
theorem singleComplexOpenComparison_union_compatible_chain_data
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
    ∃ (A B A' B' : CochainComplex
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
      (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
      (hc : t ≫ β = α ≫ t')
      (e₁ : DerivedCategory.Q.obj A ≅ (a (U ⊔ V)).left)
      (e₂ : DerivedCategory.Q.obj B ≅ (a U).left ⊞ (a V).left)
      (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅
        (a (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj A' ≅ (a (U ⊔ V)).right)
      (e₂' : DerivedCategory.Q.obj B' ≅ (a U).right ⊞ (a V).right)
      (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅
        (a (U ⊓ V)).right),
      DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ (a (U ⊔ V)).hom ∧
      DerivedCategory.Q.map β ≫ e₂'.hom =
        e₂.hom ≫ biprod.map (a U).hom (a V).hom ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.map t t' α β hc) ≫ e₃'.hom =
        e₃.hom ≫ (a (U ⊓ V)).hom := by sorry

end AlgebraicGeometry
