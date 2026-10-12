/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Sheaf.CategoryTheory.Sites.ContractedProductPresentation
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import Sheaf.CategoryTheory.Sites.EtaleInverseImageLiftingTorsor
import Sheaf.CategoryTheory.Sites.EtaleContractedProductExists

/-!
# Functoriality of the étale torsor classification of H¹

Source: Stacks Project, Cohomology on Sites, Lemma 03AJ and functoriality of its torsor
extension (blueprint: lem-sc-etale-torsor-h1-functoriality).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

/-- The canonical torsor class is compatible with scheme pullback and change of coefficients.
The inverse-image torsor is identified with the sheafified set inverse image, with its action
specified by equivariance on the sections pulled back by the adjunction units. The contracted
product is specified by its sheaf-quotient presentation, including the antidiagonal relation
and translation by the new group on the second factor.
Source: Stacks Project, Cohomology on Sites, Lemma 03AJ.
(blueprint: lem-sc-etale-torsor-h1-functoriality)

Proof:
1. Represent the class of T by the connecting image of 1 in the canonical extension
0 → G → E_T → ℤ → 0 (`lem-sc-torsor-h1`). Pullback identifies this extension with the
extension of the set inverse image, whose fibre over 1 is the inverse-image torsor
(`lem-sc-etale-torsor-inverse-image-extension`).
2. Pullback commutes with the connecting maps
(`lem-weil-pbc-pullback-cohomology-long-exact-ladder`, clause 3) and in degree zero pulls back
sections (`lem-weil-pbc-cohomology-pullback-degree-zero`), hence sends 1 to 1. The boundary
representative description gives the asserted equality of classes under scheme pullback.
3. Push E_T out along φ. Its fibre over 1 is the contracted product, with relation
(g +ᵥ t, h - φ(g)) ∼ (t,h) and G' translating h
(`lem-sc-etale-torsor-pushout-extension`).
4. The maps (φ, E_T → pushout, id_ℤ) form a morphism of short exact sequences. Connecting
maps are natural (`lem-weil-pbc-right-derived-universal-delta-functor`), so H¹(φ) sends the
boundary of 1 to the boundary of 1 for the pushout. The canonical classification identifies
these boundaries with the two torsor classes (`lem-sc-torsor-h1`), and the coefficient map
is that of `lem-weil-pbc-cohomology-pullback-functorial`. -/
theorem etale_torsor_h1_functoriality :
    (∀ (X Y : Scheme.{u}) (f : Y ⟶ X)
      (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (T : Torsor G),
      ∃ (T' : Torsor ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj G))
        (eT : (Scheme.etaleSetPullback f).obj T.sheaf ≅ T'.sheaf),
        (∀ (W : X.Etale) (g : G.obj.obj (op W)) (t : T.sheaf.obj.obj (op W)),
          eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
              (X.smallGrothendieckTopology @Etale)
              (Y.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W)
                (T.vadd (op W) g t)) =
          T'.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
            (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G).hom.app
              (op W) g)
            (eT.hom.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))
              (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
                (X.smallGrothendieckTopology @Etale)
                (Y.smallGrothendieckTopology @Etale)).unit.app T.sheaf).hom.app (op W) t))) ∧
        Etale.cohomologyMap f G 1 (classH1 G terminalIsTerminal ⟦T⟧) =
          classH1 ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj G) terminalIsTerminal ⟦T'⟧) ∧
    (∀ (S : Scheme.{u}) (G G' : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
      (φ : G ⟶ G') (T : Torsor G),
      ∃ T' : Torsor G', Nonempty (ContractedProductPresentation.{u, u} S φ T T') ∧
        H.map φ 1 (classH1 G terminalIsTerminal ⟦T⟧) =
          classH1 G' terminalIsTerminal ⟦T'⟧) := by
  constructor
  · intro X Y f G T
    let S := injectiveSequence G
    have hS := injectiveSequence_shortExact G
    obtain ⟨s, hs⟩ := exists_equiv_lifts terminalIsTerminal hS T
    let U := Etale.upperStar AddCommGrpCat.{u + 1} f
    have hY := hS.map_of_exact U
    let g := (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).inv.app S.X₃ s
    let s' := (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).hom.app (U.obj S.X₃)
      (Etale.globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f S.X₃ g)
    let T' := lifts terminalIsTerminal hY s'
    obtain ⟨eT, heT⟩ := etale_inverse_image_lifting_torsor X Y f S hS s T hs
    refine ⟨T', eT, heT, ?_⟩
    rw [_root_.Quotient.sound hs, classH1_lifts, classH1_lifts]
    rw [H.δ_apply, H.δ_apply, Etale.cohomologyMap_apply,
      Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_extClass]
    have hz := Etale.cohomologyMap_zero_eq_globalSectionsUpperStarMap f S.X₃ g
    have hg : (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
        terminalIsTerminal).hom.app S.X₃ g = s := by
      exact ConcreteCategory.congr_hom
        ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
          terminalIsTerminal).inv_hom_id_app S.X₃) s
    rw [hg, Etale.cohomologyMap_apply] at hz
    change _ = ((H.equiv₀ (U.obj S.X₃) terminalIsTerminal).symm s').comp hY.extClass _
    rw [← hz]
    exact (Abelian.Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (by omega)).symm
  · intro S G G' φ T
    obtain ⟨T', ⟨q⟩⟩ := etale_contracted_product_exists S φ T
    refine ⟨T', ⟨q⟩, ?_⟩
    apply (classH1_eq_map_of_equivariant terminalIsTerminal φ T T'
      (fun U t ↦ q.quotient U t 0) ?_ ?_).symm
    · intro U V f t
      simpa using q.quotient_natural f t 0
    · intro U a t
      have h := q.quotient_invariant U a t (φ.hom.app U a)
      calc
        q.quotient U (T.vadd U a t) 0 = q.quotient U t (φ.hom.app U a) := by
          simpa using h
        _ = T'.vadd U (φ.hom.app U a) (q.quotient U t 0) := by
          simpa using q.quotient_vadd U t 0 (φ.hom.app U a)

end CategoryTheory.Sheaf.Torsor
