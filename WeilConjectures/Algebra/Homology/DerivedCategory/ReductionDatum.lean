/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Chain-level models of derived base change

Let `res : 𝒜' ⥤ 𝒜` be an exact, fully faithful functor between abelian categories (the
restriction of scalars along a surjective ring morphism `A ⟶ A'`) and `σ` an endomorphism of
the identity functor of `𝒜` (the multiplication by a generator `a` of the kernel). A
*reduction datum* (`CategoryTheory.Functor.ReductionDatum`) is a functor `Φ : 𝒜 ⥤ 𝒜'` (the
extension of scalars `- ⊗_A A'`) with a natural epimorphism `r : F ⟶ res Φ(F)` whose kernel is
the image of `σ`, such that `Φ` sends quasi-isomorphisms between K-flat complexes to
quasi-isomorphisms.

For a K-flat complex `P`, the reduction `Q P ⟶ res Q Φ(P)` is then a universal arrow from
`Q P` to the derived functor `res : D(𝒜') ⥤ D(𝒜)`
(`CategoryTheory.Functor.ReductionDatum.bijective_comp_map`): it exhibits `Φ(P)` as the
derived base change of `P`.

The proof is elementary. A morphism `Q P ⟶ res M` is a fraction `inv (Q s) ≫ Q g` with
`s : X ⟶ P` a quasi-isomorphism, which may be taken from a K-flat complex; then `g` factors
through the reduction of `X`, and `Φ(s)` is a quasi-isomorphism. A morphism
`h : Q Φ(P) ⟶ M` killed by the reduction is a fraction `Q w ≫ inv (Q s)`; pulling back the
reduction of `P` along `s` and resolving gives a K-flat complex `V` with a quasi-isomorphism to
`P` through which `h` becomes the image of a chain map that is null-homotopic after reduction,
and homotopies descend along the epimorphism `r`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {𝒜 𝒜' : Type*} [Category 𝒜] [Abelian 𝒜] [IsGrothendieckAbelian.{v} 𝒜]
  [MonoidalCategory 𝒜] [MonoidalPreadditive 𝒜] [MonoidalClosed 𝒜] [BraidedCategory 𝒜]
  [Abelian.HasFunctorialFlatResolution 𝒜] [HasDerivedCategory 𝒜]
  [Category 𝒜'] [Abelian 𝒜'] [HasDerivedCategory 𝒜']
  (res : 𝒜' ⥤ 𝒜) [res.Additive] [PreservesFiniteLimits res] [PreservesFiniteColimits res]
  (σ : 𝟭 𝒜 ⟶ 𝟭 𝒜)

/-- A chain-level model of derived base change along `res`: a functor `Φ : 𝒜 ⥤ 𝒜'` with a
natural epimorphism `r : F ⟶ res Φ(F)` whose kernel is the image of `σ`, such that `Φ` sends
quasi-isomorphisms between K-flat complexes to quasi-isomorphisms. -/
structure ReductionDatum where
  /-- The reduction functor. -/
  Φ : 𝒜 ⥤ 𝒜'
  [additive : Φ.Additive]
  /-- The reduction map `F ⟶ res Φ(F)`. -/
  r : 𝟭 𝒜 ⟶ Φ ⋙ res
  σ_comp_r (F : 𝒜) : σ.app F ≫ r.app F = 0
  epi_r (F : 𝒜) : Epi (r.app F)
  exact (F : 𝒜) : (ShortComplex.mk _ _ (σ_comp_r F)).Exact
  quasiIso_map {P₁ P₂ : CochainComplex 𝒜 ℤ} (φ : P₁ ⟶ P₂) [QuasiIso φ]
    (h₁ : (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P₁)
    (h₂ : (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P₂) :
    QuasiIso ((Φ.mapHomologicalComplex (.up ℤ)).map φ)

attribute [instance] ReductionDatum.additive

namespace ReductionDatum

variable {res σ} (D : ReductionDatum res σ)

/-- The reduction `P ⟶ res Φ(P)` of a complex. -/
@[simps]
def complexMap (P : CochainComplex 𝒜 ℤ) :
    P ⟶ (res.mapHomologicalComplex (.up ℤ)).obj ((D.Φ.mapHomologicalComplex (.up ℤ)).obj P) where
  f i := D.r.app (P.X i)
  comm' _ _ _ := (D.r.naturality _).symm

/-- Every morphism of complexes `P ⟶ res M` factors uniquely through the reduction of `P`. -/
lemma existsUnique_complexMap_comp [res.Full] [res.Faithful] {P : CochainComplex 𝒜 ℤ}
    {M : CochainComplex 𝒜' ℤ} (g : P ⟶ (res.mapHomologicalComplex (.up ℤ)).obj M) :
    ∃! g' : (D.Φ.mapHomologicalComplex (.up ℤ)).obj P ⟶ M,
      D.complexMap P ≫ (res.mapHomologicalComplex (.up ℤ)).map g' = g := by
  sorry

/-- **The reduction of a K-flat complex is its derived base change**: for a K-flat complex
`P`, every morphism `Q P ⟶ res M` in `D(𝒜)` factors uniquely through the reduction
`Q P ⟶ res Q Φ(P)`. -/
theorem bijective_comp_map [res.Full] [res.Faithful] (P : CochainComplex 𝒜 ℤ)
    (hP : (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P) (M : DerivedCategory 𝒜') :
    Function.Bijective fun g :
        DerivedCategory.Q.obj ((D.Φ.mapHomologicalComplex (.up ℤ)).obj P) ⟶ M ↦
      (DerivedCategory.Q.map (D.complexMap P) ≫
        res.mapDerivedCategoryFactors.inv.app ((D.Φ.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        res.mapDerivedCategory.map g := by
  sorry

end ReductionDatum

end CategoryTheory.Functor
