/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHypercover

/-!
# Continuity of étale cohomology at inverse limits

Let `(Xᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over a scheme `S`, with
affine transition maps and limit `X`, and let `F` be an étale sheaf of `Λ`-modules on `S`. Then
`Hᵠ(X, F|_X) = colimᵢ Hᵠ(Xᵢ, F|_{Xᵢ})` ([Stacks, Tag 09YQ], blueprint
`lemma-weil-pbc-etale-cohomology-continuity`). For `Λ = ℤ` these are abelian étale sheaves; no
torsion hypothesis is needed.

The statement is spelled out elementwise
(`AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_of_isLimit`,
`AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_zero_of_isLimit`): every class on `X`
comes from some `Xᵢ`, and a class on `Xᵢ` which dies on `X` dies on some `Xⱼ`.

The proof follows the blueprint: a class on `X` is the class of a cocycle on a qcqs hypercover of
`X` (`AlgebraicGeometry.Scheme.exists_cohomologyClass_eq_of_isQcqsHypercover`); the truncation of
the hypercover in degrees `≤ q + 1` descends to some `Xᵢ`
(blueprint `lemma-weil-pbc-finite-hypercover-descent`), and so do the cocycle and the cocycle
condition by continuity of sections (blueprint `lem-weil-pbc-etale-section-continuity`). For
injectivity one descends in the same way a refinement on which the cocycle becomes a coboundary
(`AlgebraicGeometry.Scheme.exists_isCoboundary_of_isQcqsHypercover`), the refinement map and the
primitive.

## Main definitions

- `AlgebraicGeometry.Etale.cohomologyRestrictOver`: for a morphism `f : Y ⟶ Z` of schemes over
  `S`, the restriction map `Hᵠ(Z, F|_Z) ⟶ Hᵠ(Y, F|_Y)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {S : Scheme.{u}}

/-- For a morphism `f : Y ⟶ Z` of schemes over `S` (with structure maps `pY`, `pZ`), the
restriction map `Hᵠ(Z, F|_Z) ⟶ Hᵠ(Y, F|_Y)` of the étale cohomology of the pullbacks of a sheaf
`F` on `S`: pullback along `f` followed by the identification `f^* (pZ^* F) ≅ pY^* F`. -/
noncomputable def cohomologyRestrictOver {Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S)
    (f : Y ⟶ Z) (hf : f ≫ pZ = pY) (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (q : ℕ) :
    Ext (SemiSimplicialObject.constSheaf Z.smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) pZ).obj F) q →+
      Ext (SemiSimplicialObject.constSheaf Y.smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) pY).obj F) q :=
  (Ext.mk₀ ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) f pZ pY hf.symm).inv.app F)).postcomp _
      (add_zero q) |>.comp (Etale.cohomologyRestrict Λ f _ q)

variable {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Over S)
  [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
  (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
  (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))

include hc

/-- **Continuity of étale cohomology, surjectivity** (blueprint
`lemma-weil-pbc-etale-cohomology-continuity`): every cohomology class of the pullback of `F` to
the limit `X = lim Xᵢ` comes from some `Xᵢ`. -/
@[stacks 09YQ]
theorem exists_cohomologyRestrictOver_eq_of_isLimit (q : ℕ)
    (x : Ext (SemiSimplicialObject.constSheaf c.pt.left.smallEtaleTopology Λ)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) c.pt.hom).obj F) q) :
    ∃ (i : I) (y : Ext (SemiSimplicialObject.constSheaf (D.obj i).left.smallEtaleTopology Λ)
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.obj i).hom).obj F) q),
      cohomologyRestrictOver Λ c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _) F q y = x :=
  sorry

/-- **Continuity of étale cohomology, injectivity** (blueprint
`lemma-weil-pbc-etale-cohomology-continuity`): a cohomology class of the pullback of `F` to some
`Xᵢ` which vanishes on the limit `X = lim Xᵢ` vanishes on some `Xⱼ`, `j ⟶ i`. -/
@[stacks 09YQ]
theorem exists_cohomologyRestrictOver_eq_zero_of_isLimit (q : ℕ) (i : I)
    (y : Ext (SemiSimplicialObject.constSheaf (D.obj i).left.smallEtaleTopology Λ)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.obj i).hom).obj F) q)
    (hy : cohomologyRestrictOver Λ c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _) F q y = 0) :
    ∃ (j : I) (φ : j ⟶ i),
      cohomologyRestrictOver Λ (D.obj j).hom (D.obj i).hom (D.map φ).left (Over.w _) F q y = 0 :=
  sorry

end AlgebraicGeometry.Etale
