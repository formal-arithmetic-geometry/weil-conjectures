/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleRowIntegerSections

/-! # Sections comparison and extension by zero

Source: Stacks Project, Tags 015J and 015K.
-/

@[expose] public section

universe uNatural
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- Commuting sections with extension by zero respects any row comparison
(Stacks, Tags 015J and 015K). -/
theorem ceRowSectionsMap_extend {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    {J : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℕ}
    {J' : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℕ}
    (φ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J ⟶ J') :
    (J.mapExtendIso ComplexShape.embeddingUpNat
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).inv ≫
        ceIntegerSectionsMap f (ceExtendedRowMap f φ) =
      HomologicalComplex.extendMap
        ((NatTrans.mapHomologicalComplex (ceSectionsUnit f) (ComplexShape.up ℕ)).app J ≫
          ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
            (ComplexShape.up ℕ)).map φ)
        ComplexShape.embeddingUpNat ≫
      (J'.mapExtendIso ComplexShape.embeddingUpNat
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).inv := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : ∃ n : ℕ, (n : ℤ) = i
  · obtain ⟨n, rfl⟩ := hi
    dsimp only [ceIntegerSectionsMap, ceExtendedRowMap, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex,
      HomologicalComplex.mapExtendIso, HomologicalComplex.Hom.isoOfComponents]
    erw [HomologicalComplex.mapExtendX_hom_eq J
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
      (ComplexShape.embeddingUpNat.r_f n),
      HomologicalComplex.mapExtendX_hom_eq J
        (upperStar AddCommGrpCat.{uNatural + 1} f) (ComplexShape.embeddingUpNat.r_f n),
      HomologicalComplex.mapExtendX_hom_eq J'
        (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
        (ComplexShape.embeddingUpNat.r_f n)]
    erw [HomologicalComplex.extendMap_f _ _ (i := n) rfl,
      HomologicalComplex.extendMap_f _ _ (i := n) rfl]
    simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
      eqToIso, Functor.map_comp, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f]
    simp only [Category.assoc, eqToHom_map, eqToHom_trans]
    simp [HomologicalComplex.extend, HomologicalComplex.extend.X,
      show ComplexShape.embeddingUpNat.r (n : ℤ) = some n from
        ComplexShape.embeddingUpNat.r_f n]
  · apply IsZero.eq_of_src
    exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat i
      (by simpa using hi)

end AlgebraicGeometry.Etale
