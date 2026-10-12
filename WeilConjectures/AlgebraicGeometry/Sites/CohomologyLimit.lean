/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyLimitAux

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

/-- **Restriction of classes of hypercover cocycles.** Let `g : Y ⟶ Z` be a morphism over `S`,
`s` a `q`-cocycle of `F|_Z` on a hypercover `H` of `Z`, and `U` a hypercover of `Y` with morphisms
`μ_n : U_n ⟶ H_n` over `g` (`n ≤ q`) commuting with the face maps. Then the restriction to `Y` of
the class of `s` is the class of the restriction of `s` along `μ_q`. -/
theorem cohomologyRestrictOver_cohomologyClass {Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S)
    (g : Y ⟶ Z) (hg : g ≫ pZ = pY) (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (q : ℕ) {H : SemiSimplicialObject Z.Etale} (hH : H.IsHypercover Z.smallEtaleTopology)
    (s : ((Etale.upperStar (ModuleCat.{u + 1} Λ) pZ).obj F).obj.obj (op (H.obj q)))
    (hs : H.IsCocycle _ q s) {U : SemiSimplicialObject Y.Etale}
    (hU : U.IsHypercover Y.smallEtaleTopology) (μ : ∀ n, n ≤ q → ((U.obj n).left ⟶ (H.obj n).left))
    (hμ : ∀ n (h : n ≤ q), μ n h ≫ (H.obj n).hom = (U.obj n).hom ≫ g)
    (hμδ : ∀ n (h : n < q) (i : Fin (n + 2)),
      (U.δ n i).left ≫ μ n h.le = μ (n + 1) h ≫ (H.δ n i).left)
    (hs' : U.IsCocycle _ q
      (Etale.ModuleSheaf.restrictAlong pZ F g pY hg.symm (μ q le_rfl) (hμ q le_rfl) s)) :
    cohomologyRestrictOver Λ pY pZ g hg F q (hH.cohomologyClass _ q s hs) =
      hU.cohomologyClass _ q _ hs' := by
  let f (n : ℕ) (h : n ≤ q) : U.obj n ⟶ (H.baseChange g).obj n :=
    Etale.homToPullback g (μ n h) (hμ n h)
  have hf (n : ℕ) (h : n < q) (i : Fin (n + 2)) :
      f (n + 1) h ≫ (H.baseChange g).δ n i = U.δ n i ≫ f n h.le :=
    Etale.hom_ext_pullback _ (by simpa [f] using (hμδ n h i).symm)
  have key : Etale.ModuleSheaf.restrictAlong pZ F g pY hg.symm (μ q le_rfl) (hμ q le_rfl) s =
      (((Etale.upperStar (ModuleCat.{u + 1} Λ) pY).obj F).obj.map (f q le_rfl).op).hom
        (((Etale.upperStarComp (ModuleCat.{u + 1} Λ) g pZ pY hg.symm).inv.app F).hom.app _
          (Etale.pullbackSection Λ g _ (H.obj q) s)) := by
    exact Etale.ModuleSheaf.restrictAlong_comp_fst_eq pZ F g pY hg.symm (f q le_rfl) _ _
      (Etale.homToPullback_left_fst g (μ q le_rfl) (hμ q le_rfl)) s
  have hw : (H.baseChange g).IsCocycle ((Etale.upperStar (ModuleCat.{u + 1} Λ) pY).obj F) q
      (((Etale.upperStarComp (ModuleCat.{u + 1} Λ) g pZ pY hg.symm).inv.app F).hom.app _
        (Etale.pullbackSection Λ g _ (H.obj q) s)) :=
    SemiSimplicialObject.IsCocycle.map _
      (hs.map ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _))
  rw [hU.cohomologyClass_congr _ q key hs' (key ▸ hs'),
    (hH.baseChange g).cohomologyClass_restrict_of_le hU q f hf _ _ hw]
  refine Eq.trans ?_ ((hH.baseChange g).cohomologyClass_map
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) g pZ pY hg.symm).inv.app F) q _
    (hs.map ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _))).symm
  change (Etale.cohomologyRestrict Λ g _ q (hH.cohomologyClass _ q s hs)).comp (Ext.mk₀ _)
    (add_zero q) = _
  rw [Etale.cohomologyRestrict_cohomologyClass]
  rfl

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
