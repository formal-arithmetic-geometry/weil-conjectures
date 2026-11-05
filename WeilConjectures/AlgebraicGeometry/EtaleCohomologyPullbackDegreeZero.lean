/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Single
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZeroAux

/-!
# Degree-zero étale cohomology and pullback

Source: Stacks Project, Tags 05TD and 01FA
(blueprint: lem-weil-pbc-cohomology-pullback-degree-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace AlgebraicGeometry.Etale

private theorem uliftZ_naturality {A B : AddCommGrpCat.{u + 1}}
    (f : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ A) (k : A ⟶ B) :
    AddCommGrpCat.uliftZMultiplesAddEquiv B (f ≫ k) =
      k (AddCommGrpCat.uliftZMultiplesAddEquiv A f) := by
  rfl

private theorem homEquiv_comparison {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R)
    (A : C) (B : D) (f : L.obj A ⟶ B) :
    adj'.homEquiv A B ((Adjunction.leftAdjointUniq adj adj').inv.app A ≫ f) =
      adj.homEquiv A B f := by
  rw [Adjunction.leftAdjointUniq_inv_app, adj'.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, adj.homEquiv_apply]

/-- Under the canonical degree-zero identification, pullback on étale cohomology is
pullback of a global section by the adjunction unit.
Source: Stacks Tag 01FA (blueprint: lem-weil-pbc-cohomology-pullback-degree-zero).

Proof: For resolutions `s : G[0] → I` and `r : u⁻¹I → J`, the pullback of `[s(g)]` is
`[r(η(s(g)))]`. Naturality of the inverse-image unit gives
`η(s(g)) = (u⁻¹s)(η(g))`, so this is `[t(η(g))]` for `t = r ∘ u⁻¹s`.
The preceding naturality computation permits every choice of K-injective resolution,
by cohomology-pullback-functorial and cohomology-resolution-independent. In the recorded
Ext encoding of cohomology-pullback, the same identity follows by the degree-zero Ext/Hom
identification and the constant-sheaf adjunction defining `Sheaf.H.equiv₀`. -/
theorem cohomologyMap_zero_eq_globalSectionsUpperStarMap {X Y : Scheme.{u}}
    (u : Y ⟶ X) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (g : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G) :
    cohomologyMap u G 0
      ((Sheaf.H.equiv₀ G terminalIsTerminal).symm
        ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app G g)) =
    (Sheaf.H.equiv₀ ((upperStar AddCommGrpCat.{u + 1} u).obj G) terminalIsTerminal).symm
      ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
        terminalIsTerminal).hom.app ((upperStar AddCommGrpCat.{u + 1} u).obj G)
        (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} u G g)) := by
  apply (Sheaf.H.equiv₀ _ terminalIsTerminal).injective
  simp only [AddEquiv.apply_symm_apply]
  rw [cohomologyMap_apply]
  simp only [Sheaf.H.equiv₀, AddEquiv.symm_trans_apply, AddEquiv.trans_apply]
  simp only [CategoryTheory.Abelian.Ext.addEquiv₀_symm_apply,
    CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀, CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
  rw [← CategoryTheory.Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  simp only [Adjunction.homAddEquiv_apply, Adjunction.homAddEquiv_symm_apply]
  simp only [Scheme.upperStarConstantSheafIso, Iso.app_hom, Iso.symm_hom]
  erw [homEquiv_comparison]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  let A := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let adjX := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal
  let f := (adjX.homEquiv A G).symm
    ((AddCommGrpCat.uliftZMultiplesAddEquiv _).symm
      ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app G g))
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
    (adjX.homEquiv A _ ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).homEquiv
      _ _ ((upperStar AddCommGrpCat.{u + 1} u).map f)) ≫
      (lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} u).hom.app _) = _
  erw [(upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).homEquiv_apply,
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).unit_naturality]
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  rw [uliftZ_naturality, uliftZ_naturality, AddEquiv.apply_symm_apply]
  simp only [globalSectionsUpperStarMap, lowerStarCompSheafSectionsTerminalIso,
    NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.symm_hom,
    ConcreteCategory.comp_apply]
  simp only [← ConcreteCategory.comp_apply, Category.assoc, Iso.inv_hom_id_app]
  rfl

end AlgebraicGeometry.Etale
