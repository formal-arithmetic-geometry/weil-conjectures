/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module


public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Transport of closed monoidal comparisons through a monoidal square

Source: literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/
`thm-coef-finite-hom.md`, proof final sentence
(blueprint: lem-coef-monoidal-square-hom-transport).
-/

@[expose] public section

universe uCA vCA uCB vCB uDA vDA uDB vDB
universe uCC vCC uDC vDC

open CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace CategoryTheory

/-- The internal-Hom comparison obtained by transposing the image of evaluation along
`V`'s tensorator (blueprint: lem-coef-monoidal-square-hom-transport).
This is the map denoted `v_V` in the source statement.
Source: literature/blueprint/master/blueprint/sec-six-functors/
sk-prop-sf-biduality-general/thm-coef-finite-hom.md, proof final sentence. -/
noncomputable def internalHomComparison
    {C : Type uCA} [Category.{vCA} C] [MonoidalCategory C]
    {D : Type uCB} [Category.{vCB} D] [MonoidalCategory D]
    [MonoidalClosed C] [MonoidalClosed D]
    (V : C ⥤ D) [V.Monoidal] (K M : C) :
    V.obj (K ⟶[C] M) ⟶ (V.obj K ⟶[D] V.obj M) :=
  MonoidalClosed.curry (Functor.LaxMonoidal.μ V K (K ⟶[C] M) ≫
    V.map ((ihom.ev K).app M))

/-- The endpoint transport induced by a natural isomorphism of functors.
Source: literature/blueprint/master/blueprint/sec-six-functors/
sk-prop-sf-biduality-general/thm-coef-finite-hom.md, proof final sentence
(blueprint: lem-coef-monoidal-square-hom-transport). -/
noncomputable def internalHomTransport
    {C : Type uCA} [Category.{vCA} C] [MonoidalCategory C]
    {D : Type uCB} [Category.{vCB} D] [MonoidalCategory D]
    [MonoidalClosed C] [MonoidalClosed D]
    {V W : C ⥤ D} (e : V ≅ W) (K M : C) :
    (V.obj K ⟶[D] V.obj M) ⟶ (W.obj K ⟶[D] W.obj M) :=
  (MonoidalClosed.pre (e.inv.app K)).app (V.obj M) ≫
    (ihom (W.obj K)).map (e.hom.app M)

/-- The naturality, evaluation, transpose, and internal-Hom composition laws for the
comparison `v_V` (blueprint: lem-coef-monoidal-square-hom-transport).
The equations use Mathlib's canonical closed structure and monoidal tensorator.
This predicate does not include successive coefficient change; that law is stated
separately by `SuccessiveCoefficientHomTransport`.
Source: literature/blueprint/master/blueprint/sec-six-functors/
sk-prop-sf-biduality-general/thm-coef-finite-hom.md, proof final sentence. -/
def InternalHomComparisonLaws
    {C : Type uCA} [Category.{vCA} C] [MonoidalCategory C]
    {D : Type uCB} [Category.{vCB} D] [MonoidalCategory D]
    [MonoidalClosed C] [MonoidalClosed D]
    (V : C ⥤ D) [V.Monoidal] : Prop :=
  (∀ {K K' M M' : C} (a : K' ⟶ K) (b : M ⟶ M'),
    V.map ((MonoidalClosed.pre a).app M ≫ (ihom K').map b) ≫
        internalHomComparison V K' M' =
      internalHomComparison V K M ≫
        (MonoidalClosed.pre (V.map a)).app (V.obj M) ≫
        (ihom (V.obj K')).map (V.map b)) ∧
  (∀ (K M : C),
    MonoidalClosed.uncurry (internalHomComparison V K M) =
      Functor.LaxMonoidal.μ V K (K ⟶[C] M) ≫ V.map ((ihom.ev K).app M)) ∧
  (∀ {T K M : C} (t : T ⟶ (K ⟶[C] M)),
    V.map t ≫ internalHomComparison V K M =
      MonoidalClosed.curry (Functor.LaxMonoidal.μ V K T ≫ V.map
        (MonoidalClosed.uncurry t))) ∧
  (∀ (K L M : C),
    V.map (MonoidalClosed.comp K L M) ≫ internalHomComparison V K M =
      Functor.OplaxMonoidal.δ V (K ⟶[C] L) (L ⟶[C] M) ≫
        (internalHomComparison V K L ⊗ₘ internalHomComparison V L M) ≫
        MonoidalClosed.comp (V.obj K) (V.obj L) (V.obj M))

/-- Coherent successive coefficient change, including endpoint transports.
The composite identifications `fComp` and `gComp` are monoidal, as the node specifies
("specified monoidal composite identifications"); the assumed composition equation for
`v_F` is the hypothesis `_hFComp`.
Source: literature/blueprint/master/blueprint/sec-six-functors/
sk-prop-sf-biduality-general/thm-coef-finite-hom.md, proof final sentence
(blueprint: lem-coef-monoidal-square-hom-transport). -/
def SuccessiveCoefficientHomTransport
    {CA : Type uCA} [Category.{vCA} CA] [MonoidalCategory CA]
    [BraidedCategory CA]
    {CB : Type uCB} [Category.{vCB} CB] [MonoidalCategory CB]
    [BraidedCategory CB]
    {DA : Type uDA} [Category.{vDA} DA] [MonoidalCategory DA]
    [BraidedCategory DA]
    {DB : Type uDB} [Category.{vDB} DB] [MonoidalCategory DB]
    [BraidedCategory DB]
    [MonoidalClosed CA] [MonoidalClosed CB] [MonoidalClosed DA]
    [MonoidalClosed DB]
    (F : CA ⥤ CB) (G : DA ⥤ DB) (UA : CA ⥤ DA) (UB : CB ⥤ DB)
    [F.Monoidal] [G.Monoidal] [UA.Monoidal] [UB.Monoidal]
    (hAB : F ⋙ UB ≅ UA ⋙ G) [NatTrans.IsMonoidal hAB.hom] : Prop :=
  ∀ {CC : Type uCC} [Category.{vCC} CC] [MonoidalCategory CC]
    [BraidedCategory CC] {DC : Type uDC} [Category.{vDC} DC]
    [MonoidalCategory DC] [BraidedCategory DC]
    [MonoidalClosed CC] [MonoidalClosed DC]
    (FBC : CB ⥤ CC) (FAC : CA ⥤ CC) (GBC : DB ⥤ DC) (GAC : DA ⥤ DC)
    (UC : CC ⥤ DC)
    [FBC.Braided] [FAC.Braided] [GBC.Braided] [GAC.Braided] [UC.Braided]
    (hBC : FBC ⋙ UC ≅ UB ⋙ GBC) [NatTrans.IsMonoidal hBC.hom]
    (hAC : FAC ⋙ UC ≅ UA ⋙ GAC) [NatTrans.IsMonoidal hAC.hom]
    (fComp : FAC ≅ F ⋙ FBC) [NatTrans.IsMonoidal fComp.hom]
    (gComp : GAC ≅ G ⋙ GBC) [NatTrans.IsMonoidal gComp.hom]
    (_hCoherent : ∀ (X : CA),
      UC.map (fComp.hom.app X) ≫ hBC.hom.app (F.obj X) ≫
          GBC.map (hAB.hom.app X) ≫ gComp.inv.app (UA.obj X) =
        hAC.hom.app X),
    ∀ {K M : CA}
      [IsIso (internalHomComparison UA K M)]
      [IsIso (internalHomComparison UB (F.obj K) (F.obj M))]
      [IsIso (internalHomComparison UC (FAC.obj K) (FAC.obj M))],
      InternalHomComparisonLaws F →
      InternalHomComparisonLaws FBC →
      InternalHomComparisonLaws FAC →
      (_hFComp : internalHomComparison FAC K M ≫ internalHomTransport fComp K M =
        fComp.hom.app (K ⟶[CA] M) ≫ FBC.map (internalHomComparison F K M) ≫
          internalHomComparison FBC (F.obj K) (F.obj M)) →
      (GAC.map (internalHomComparison UA K M) ≫
          internalHomComparison GAC (UA.obj K) (UA.obj M) ≫
          internalHomTransport gComp (UA.obj K) (UA.obj M) =
        gComp.hom.app (UA.obj (K ⟶[CA] M)) ≫
          GBC.map (G.map (internalHomComparison UA K M)) ≫
          GBC.map (internalHomComparison G (UA.obj K) (UA.obj M)) ≫
          internalHomComparison GBC (G.obj (UA.obj K)) (G.obj (UA.obj M))) ∧
      (∀ (X Y : DA), internalHomComparison (𝟭 DA) X Y = 𝟙 _)

section ComparisonProofs

variable {C : Type uCA} [Category.{vCA} C] [MonoidalCategory C]
  {D : Type uCB} [Category.{vCB} D] [MonoidalCategory D]
  {E : Type uDA} [Category.{vDA} E] [MonoidalCategory E]
  [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]

open Category Functor.LaxMonoidal

end ComparisonProofs

end CategoryTheory
