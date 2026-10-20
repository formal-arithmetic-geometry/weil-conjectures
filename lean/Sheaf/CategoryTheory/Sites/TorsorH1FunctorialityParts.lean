module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Sheaf.Topology.ClosedImmersionPushforwardCohomology

/-! Intermediate clauses for torsor H¹ functoriality. -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
universe u v w
namespace CategoryTheory.Sheaf

/-- The contracted-product clause of torsor H¹ functoriality.
Source: Stacks Project, Cohomology, Lemma 02FQ.
The boundary-of-one representative and pushout-extension construction identify the
induced cohomology class with the contracted-product torsor class.
(blueprint: lem-sc-torsor-h1-functoriality-part-contract) -/
theorem torsor_h1_functoriality_contract
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{w})] [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
    {T : C} (_hT : IsTerminal T)
    (G G' : Sheaf J AddCommGrpCat.{w}) (φ : G ⟶ G')
    (eG : H G 1 ≃ _root_.Quotient (Torsor.setoid (G := G)))
    (eG' : H G' 1 ≃ _root_.Quotient (Torsor.setoid (G := G')))
    (hφ : H G 1 → H G' 1) (push : Torsor G → Torsor G') :
    ∀ P : Torsor G, eG' (hφ (eG.symm ⟦P⟧)) = ⟦push P⟧ := by
  sorry

/-- The closed-embedding direct-image clause of torsor H¹ functoriality.
Source: Stacks Project, Cohomology, Lemmas 02FQ and 02UV.
The closed-pushforward comparison transports the boundary of one to the pulled-back
boundary, whose fibre is the direct image torsor.
(blueprint: lem-sc-torsor-h1-functoriality-part-pushforward) -/
theorem torsor_h1_functoriality_pushforward
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{w})] [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
    {T : C} (_hT : IsTerminal T)
    (G G' : Sheaf J AddCommGrpCat.{w}) (φ : G ⟶ G')
    (eG : H G 1 ≃ _root_.Quotient (Torsor.setoid (G := G)))
    (eG' : H G' 1 ≃ _root_.Quotient (Torsor.setoid (G := G')))
    (hφ : H G 1 → H G' 1) (push : Torsor G → Torsor G')
    {Z X : TopCat.{u}} (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i)
    (F : TopCat.Sheaf AddCommGrpCat Z) (p : ℕ)
    (eF : @CategoryTheory.Sheaf.H' (Opens Z) _ (Opens.grothendieckTopology Z) _
      (HasExt.standard _) F p ⊤ ≃ _root_.Quotient (Torsor.setoid (G := F)))
    (eIF : @CategoryTheory.Sheaf.H' (Opens X) _ (Opens.grothendieckTopology X) _
      (HasExt.standard _) ((TopCat.Sheaf.pushforward AddCommGrpCat i).obj F) p ⊤ ≃
      _root_.Quotient (Torsor.setoid
        (G := (TopCat.Sheaf.pushforward AddCommGrpCat i).obj F)))
    (hI : @CategoryTheory.Sheaf.H' (Opens Z) _ (Opens.grothendieckTopology Z) _
      (HasExt.standard _) F p ⊤ →
      @CategoryTheory.Sheaf.H' (Opens X) _ (Opens.grothendieckTopology X) _
        (HasExt.standard _) ((TopCat.Sheaf.pushforward AddCommGrpCat i).obj F) p ⊤)
    (direct : Torsor F → Torsor ((TopCat.Sheaf.pushforward AddCommGrpCat i).obj F)) :
    ∀ P : Torsor F, eIF (hI (eF.symm ⟦P⟧)) = ⟦direct P⟧ := by
  sorry

end CategoryTheory.Sheaf
