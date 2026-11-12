/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.Functoriality
public import WeilConjectures.TraceFormula.Specialization.DeformationModel

/-!

# Functoriality of the morphisms of deformation models

The morphisms of deformation spaces `D_J X' ⟶ D_I X` compose for arbitrary morphisms of schemes
(`AlgebraicGeometry.Scheme.IdealSheafData.deformationSpaceMap_comp`, in
`WeilConjectures.AlgebraicGeometry.DeformationSpace.Functoriality`); hence so do the morphisms
of total spaces and of special fibres of the deformation models
(`ProEtale.CondensedRing.deformationTotalMap_comp`,
`ProEtale.CondensedRing.deformationSpecialFibreMap_comp`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace ProEtale.CondensedRing

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']
  {X Y Z : Over (Spec (.of k))} (f : X ⟶ Y) (g : Y ⟶ Z)
  {I₃ : Z.left.IdealSheafData} {I₂ : Y.left.IdealSheafData} {I₁ : X.left.IdealSheafData}
  (hf : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1), (I₂.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤
      I₁.siteIdeal U')
  (hg : ∀ ⦃U' : Y.left.AffineZariskiSite⦄ ⦃U : Z.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ g.left ⁻¹ᵁ U.1), (I₃.siteIdeal U).map (g.left.appLE U.1 U'.1 hU).hom ≤
      I₂.siteIdeal U')
  (hfg : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Z.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ (f ≫ g).left ⁻¹ᵁ U.1),
    (I₃.siteIdeal U).map ((f ≫ g).left.appLE U.1 U'.1 hU).hom ≤
      I₁.siteIdeal U')

/-- The morphisms of total spaces of deformation models compose. -/
lemma deformationTotalMap_comp :
    deformationTotalMap f hf k' ≫ deformationTotalMap g hg k' =
      deformationTotalMap (f ≫ g) hfg k' := by
  apply pullback.hom_ext
  · change _ ≫ deformationTotalToSpace _ _ k' = _ ≫ deformationTotalToSpace _ _ k'
    rw [Category.assoc, deformationTotalMap_toSpace, deformationTotalMap_toSpace_assoc,
      deformationTotalMap_toSpace]
    exact congrArg (deformationTotalToSpace X I₁ k' ≫ ·)
      (Scheme.IdealSheafData.deformationSpaceMap_comp f.left g.left hf hg hfg)
  · change _ ≫ deformationTotalToTrait _ _ k' = _ ≫ deformationTotalToTrait _ _ k'
    rw [Category.assoc, deformationTotalMap_toTrait, deformationTotalMap_toTrait,
      deformationTotalMap_toTrait]

/-- The morphisms of special fibres of deformation models compose. -/
lemma deformationSpecialFibreMap_comp :
    deformationSpecialFibreMap f hf k' ≫ deformationSpecialFibreMap g hg k' =
      deformationSpecialFibreMap (f ≫ g) hfg k' := by
  ext1
  apply pullback.hom_ext
  · change _ ≫ deformationSpecialToTotal _ _ k' = _ ≫ deformationSpecialToTotal _ _ k'
    rw [Over.comp_left, Category.assoc, deformationSpecialFibreMap_toTotal,
      deformationSpecialFibreMap_toTotal_assoc, deformationTotalMap_comp,
      deformationSpecialFibreMap_toTotal]
  · change _ ≫ (deformationSpecialFibre Z I₃ k').hom = _ ≫ (deformationSpecialFibre Z I₃ k').hom
    simp only [Over.w]

/-- The morphism of special fibres depends only on the underlying morphism. -/
lemma deformationSpecialFibreMap_eq_of_eq {f' : X ⟶ Y} (e : f = f')
    (hf' : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ f'.left ⁻¹ᵁ U.1), (I₂.siteIdeal U).map (f'.left.appLE U.1 U'.1 hU).hom ≤
        I₁.siteIdeal U') :
    deformationSpecialFibreMap f hf k' = deformationSpecialFibreMap f' hf' k' := by
  subst e
  rfl

end ProEtale.CondensedRing

end AlgebraicGeometry
