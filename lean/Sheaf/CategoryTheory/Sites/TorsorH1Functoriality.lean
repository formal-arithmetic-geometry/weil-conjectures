module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Sheaf.Topology.ClosedImmersionPushforwardCohomology
import Sheaf.CategoryTheory.Sites.TorsorH1FunctorialityParts

/-! # Functoriality of the torsor description of H¹

Source: literature/stacks-project/cohomology.tex, Lemmas 02FQ and 02UV
(blueprint: lem-sc-torsor-h1-functoriality).

## Main statements

* `torsor_h1_functoriality` records the two naturality assertions for the
  canonical torsor description of first cohomology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace

universe u v w

namespace CategoryTheory.Sheaf

/-- Source: Stacks Project, Cohomology, Lemmas 02FQ and 02UV
(blueprint: lem-sc-torsor-h1-functoriality).

For a morphism of abelian sheaves, the canonical torsor description of first
cohomology is compatible with contracted product.  For a closed embedding of
topological spaces, it is compatible with direct image of torsors and the
cohomology comparison.  The proof uses the boundary-of-one description,
pushout of extensions, and naturality of the closed-embedding comparison.
-/
theorem torsor_h1_functoriality
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{w})] [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
    {T : C} (_hT : IsTerminal T)
    (G G' : Sheaf J AddCommGrpCat.{w})
    (φ : G ⟶ G')
    (eG : H G 1 ≃ _root_.Quotient (Torsor.setoid (G := G)))
    (eG' : H G' 1 ≃ _root_.Quotient (Torsor.setoid (G := G')))
    (hφ : H G 1 → H G' 1)
    (push : Torsor G → Torsor G')
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
    (direct : Torsor F →
      Torsor ((TopCat.Sheaf.pushforward AddCommGrpCat i).obj F)) :
    (∀ P : Torsor G, eG' (hφ (eG.symm ⟦P⟧)) = ⟦push P⟧) ∧
      (∀ P : Torsor F, eIF (hI (eF.symm ⟦P⟧)) = ⟦direct P⟧) := by
  constructor
  · exact torsor_h1_functoriality_contract _hT G G' φ eG eG' hφ push
  · exact torsor_h1_functoriality_pushforward _hT G G' φ eG eG' hφ push i hi F p eF eIF hI direct

end CategoryTheory.Sheaf
