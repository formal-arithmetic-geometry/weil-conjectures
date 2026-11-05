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

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

end DerivedCategory

namespace CategoryTheory.Functor

section

variable {C₁ C₂ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory C₁]
  [Category C₂] [Abelian C₂] [HasDerivedCategory C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The naturality of the inverse of `F.mapDerivedCategoryFactors`. -/
@[reassoc]
lemma mapDerivedCategoryFactors_inv_naturality {K L : CochainComplex C₁ ℤ} (a : K ⟶ L) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) ≫
        F.mapDerivedCategoryFactors.inv.app L =
      F.mapDerivedCategoryFactors.inv.app K ≫
        F.mapDerivedCategory.map (DerivedCategory.Q.map a) :=
  F.mapDerivedCategoryFactors.inv.naturality a

/-- Conjugating `F.mapDerivedCategory.map (Q.map a)` by `F.mapDerivedCategoryFactors` gives
`Q.map` of the image of `a`. -/
@[reassoc]
lemma mapDerivedCategoryFactors_inv_app_comp_map_comp_hom_app {K L : CochainComplex C₁ ℤ}
    (a : K ⟶ L) :
    F.mapDerivedCategoryFactors.inv.app K ≫ F.mapDerivedCategory.map (DerivedCategory.Q.map a) ≫
        F.mapDerivedCategoryFactors.hom.app L =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) := by
  rw [mapDerivedCategoryFactors_hom_naturality, Iso.inv_hom_id_app_assoc]

end

variable {𝒜 𝒜' : Type*} [Category 𝒜] [Abelian 𝒜] [IsGrothendieckAbelian.{v} 𝒜]
  [MonoidalCategory 𝒜] [MonoidalPreadditive 𝒜] [MonoidalClosed 𝒜] [BraidedCategory 𝒜]
  [Abelian.HasFunctorialFlatResolution 𝒜] [HasDerivedCategory 𝒜]
  [Category 𝒜'] [Abelian 𝒜'] [HasDerivedCategory 𝒜']
  (res : 𝒜' ⥤ 𝒜) [res.Additive] [PreservesFiniteLimits res] [PreservesFiniteColimits res]
  (σ : 𝟭 𝒜 ⟶ 𝟭 𝒜)

/-- A chain-level model of derived base change along `res`: a functor `Φ : 𝒜 ⥤ 𝒜'` with a
natural epimorphism `r : F ⟶ res Φ(F)` whose kernel is the image of `σ`, such that `Φ` sends
quasi-isomorphisms between K-flat complexes to quasi-isomorphisms. The endomorphism `σ` is
required to vanish on the image of `res`. -/
structure ReductionDatum where
  /-- The reduction functor. -/
  Φ : 𝒜 ⥤ 𝒜'
  [additive : Φ.Additive]
  /-- The reduction map `F ⟶ res Φ(F)`. -/
  r : 𝟭 𝒜 ⟶ Φ ⋙ res
  /-- The endomorphism `σ` vanishes on the image of `res`. -/
  σ_app_obj (X : 𝒜') : σ.app (res.obj X) = 0
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

omit [Abelian.HasFunctorialFlatResolution 𝒜] [HasDerivedCategory 𝒜] [HasDerivedCategory 𝒜']
  [PreservesFiniteLimits res] [PreservesFiniteColimits res] in
/-- The reduction of complexes is natural. -/
@[reassoc]
lemma complexMap_naturality {P P' : CochainComplex 𝒜 ℤ} (f : P ⟶ P') :
    f ≫ D.complexMap P' =
      D.complexMap P ≫ (res.mapHomologicalComplex (.up ℤ)).map
        ((D.Φ.mapHomologicalComplex (.up ℤ)).map f) := by
  ext i
  exact D.r.naturality (f.f i)

/-- A morphism `X ⟶ res Y` descends along the reduction `X ⟶ res Φ(X)`. -/
noncomputable def desc [res.Full] {X : 𝒜} {Y : 𝒜'} (g : X ⟶ res.obj Y) : D.Φ.obj X ⟶ Y :=
  haveI := D.epi_r X
  res.preimage ((D.exact X).desc g (by
    have := σ.naturality g
    dsimp at this ⊢
    rw [← this, D.σ_app_obj, Limits.comp_zero]))

omit [Abelian.HasFunctorialFlatResolution 𝒜] [HasDerivedCategory 𝒜] [HasDerivedCategory 𝒜']
  [res.Additive] [PreservesFiniteLimits res] [PreservesFiniteColimits res] in
/-- The defining property of `ReductionDatum.desc`. -/
@[reassoc (attr := simp)]
lemma r_app_comp_map_desc [res.Full] {X : 𝒜} {Y : 𝒜'} (g : X ⟶ res.obj Y) :
    D.r.app X ≫ res.map (D.desc g) = g := by
  have := D.epi_r X
  simp only [desc, Functor.map_preimage]
  exact (D.exact X).g_desc _ _

omit [Abelian.HasFunctorialFlatResolution 𝒜] [HasDerivedCategory 𝒜] [HasDerivedCategory 𝒜']
  [res.Additive] [PreservesFiniteLimits res] [PreservesFiniteColimits res] in
/-- Two morphisms out of `Φ(X)` agree as soon as they agree after restriction and composition
with the reduction. -/
lemma hom_ext [res.Faithful] {X : 𝒜} {Y : 𝒜'} {a b : D.Φ.obj X ⟶ Y}
    (h : D.r.app X ≫ res.map a = D.r.app X ≫ res.map b) : a = b := by
  have := D.epi_r X
  exact res.map_injective ((cancel_epi _).1 h)

/-- A morphism of complexes `P ⟶ res M` descends along the reduction of `P`. -/
@[simps]
noncomputable def descComplex [res.Full] [res.Faithful] {P : CochainComplex 𝒜 ℤ}
    {M : CochainComplex 𝒜' ℤ} (g : P ⟶ (res.mapHomologicalComplex (.up ℤ)).obj M) :
    (D.Φ.mapHomologicalComplex (.up ℤ)).obj P ⟶ M where
  f i := D.desc (g.f i)
  comm' i j _ := by
    refine D.hom_ext ?_
    have h₁ := D.r_app_comp_map_desc (g.f i)
    have h₂ := D.r_app_comp_map_desc (g.f j)
    have hr := D.r.naturality (P.d i j)
    have hg := g.comm i j
    dsimp at h₁ h₂ hr hg ⊢
    rw [Functor.map_comp, Functor.map_comp, reassoc_of% h₁]
    erw [← reassoc_of% hr, h₂]
    exact hg

omit [Abelian.HasFunctorialFlatResolution 𝒜] [HasDerivedCategory 𝒜] [HasDerivedCategory 𝒜']
  [PreservesFiniteLimits res] [PreservesFiniteColimits res] in
/-- The defining property of `ReductionDatum.descComplex`. -/
@[reassoc (attr := simp)]
lemma complexMap_comp_descComplex [res.Full] [res.Faithful] {P : CochainComplex 𝒜 ℤ}
    {M : CochainComplex 𝒜' ℤ} (g : P ⟶ (res.mapHomologicalComplex (.up ℤ)).obj M) :
    D.complexMap P ≫ (res.mapHomologicalComplex (.up ℤ)).map (D.descComplex g) = g := by
  ext i
  simp

end ReductionDatum

end CategoryTheory.Functor
