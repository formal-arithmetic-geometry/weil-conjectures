/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfOpenClosedTriangleData
import WeilConjectures.AlgebraicGeometry.SfNormalizedRationalWeilSquares
import WeilConjectures.AlgebraicGeometry.CommonStageWeilIterate

/-! # The first two Frobenius squares of normalized common-stage recollement -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w₁
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]

attribute [local irreducible] rationalPullbackScalarComparison operationStageTransitionIso
  StageSystem.PairCategory.mkHom commonStagePullbackComparison
attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.stageCategory

private theorem transportHom {C : Type*} [Category C] {A B A' B' : C}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    eqToHom hA.symm ≫ f ≫ eqToHom hB = g := by
  subst A'
  subst B'
  simpa using eq_of_heq h

/-- Naturality of the existing finite-stage Frobenius comparison.
Source: blueprint common-stage passage in proof (1)
(blueprint: lem-sf-normalized-common-stage-recollement-weil-squares).
Proof: the common-stage pullback is defined on common-stage representatives by the
finite pullback and its scalar comparisons. Apply its prescribed map formula to a
same-stage arrow. Both sides are its finite pullback, with the identical inclusion
associators. Naturality of the equality comparisons gives the displayed identity. -/
private theorem stageSquare_naturality (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (L : Padic.FiniteCoefficientFields l Qbar)
    (K M : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) (D.geometricFiber Y₀).left)
    (f : K ⟶ M) :
    (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar).map
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).map f) ≫
      (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L M).hom =
    (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L K).hom ≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
        ((sfWeilFrobeniusPullback D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L)).map f) := by
  let := sfWeilPrimeInvertible D l hl Y₀
  let g := (D.geometricFrobenius Y₀).hom
  let R := rationalDerivedPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) g
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l Qbar
    (D.geometricFiber Y₀).left
  let c : R ⋙ S.T (le_refl L) ≅ S.T (le_refl L) ⋙ R :=
    isoWhiskerLeft R (operationStageTransitionIso l Qbar _ L L le_rfl) ≪≫
      rationalPullbackScalarComparison l _ _
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Qbar L L le_rfl) g ≪≫
      isoWhiskerRight (operationStageTransitionIso l Qbar _ L L le_rfl).symm R
  have hc : c.hom.app K ≫ R.map ((S.T (le_refl L)).map f) ≫ c.inv.app M =
      (S.T (le_refl L)).map (R.map f) := by
    have hn := c.hom.naturality f
    dsimp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn]
    simp
  have hm := (@commonStageDerivedPullback_existsUnique l _ Qbar _ _ _ _ _ g
    (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).exists.choose_spec
  have ht := transportHom (hm.1 ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K))
    (hm.1 ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj M)) _ _
    (hm.2 _ _ L le_rfl le_rfl ((S.T (le_refl L)).map f))
  have same :
      (commonStagePullbackComparison l Qbar g
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K) L le_rfl).hom ≫
          R.map ((S.T (le_refl L)).map f) ≫
        (commonStagePullbackComparison l Qbar g
          ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj M) L le_rfl).inv =
            (S.T (le_refl L)).map (R.map f) := by
    simpa only [commonStagePullbackComparison, commonStagePullbackObject,
      GeneralAlgebraicallyClosedCoefficients.inclusion, StageSystem.ι,
      StageSystem.PairCategory.toStage, Functor.comp_obj, c, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.comp_app] using hc
  have he := ht.trans (congrArg
    (GeneralAlgebraicallyClosedCoefficients.ofHom
      (commonStagePullbackObject l Qbar g
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj K))
      (commonStagePullbackObject l Qbar g
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj M)) L le_rfl le_rfl) same)
  apply (cancel_epi (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L K).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  dsimp only [sfWeilStagePullbackIdentification, sfCommonStageWeilFrobeniusPullback,
    sfWeilFrobeniusPullback, eqToIso,
    GeneralAlgebraicallyClosedCoefficients.inclusion, StageSystem.ι]
  unfold commonStageDerivedPullback
  simpa only [commonStagePullbackObject, R, S, g,
    GeneralAlgebraicallyClosedCoefficients.ofHom,
    GeneralAlgebraicallyClosedCoefficients.inclusion, StageSystem.ι] using he

/-- The existing stage comparison, bundled naturally for the fixed-pair transport.
Source: blueprint common-stage passage in proof (1)
(blueprint: lem-sf-normalized-common-stage-recollement-weil-squares). -/
private def stageSquare (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (L : Padic.FiniteCoefficientFields l Qbar) :
    GeneralAlgebraicallyClosedCoefficients.inclusion L ⋙
        sfCommonStageWeilFrobeniusPullback D l hl Y₀ Qbar ≅
      sfWeilFrobeniusPullback D l hl Y₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar L) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion L :=
  NatIso.ofComponents (sfWeilStagePullbackIdentification D l hl Y₀ Qbar L)
    (fun {K M} f ↦ stageSquare_naturality D l hl Qbar Y₀ L K M f)


private theorem squares_of_iso
    {C : Type w} [Category.{w₁} C]
    (P : SfRecollementPresentation C) (G : C ⥤ C)
    {N K : CategoryTheory.Endofunctor.IsoAlgebra G} (e : N ≅ K)
    (ac : (G.obj (P.openTerm.obj N.carrier) ≅ P.openTerm.obj N.carrier) ×
      (G.obj (P.closedTerm.obj N.carrier) ≅ P.closedTerm.obj N.carrier))
    (ha : G.map (P.counit.app N.carrier) ≫ N.str.hom =
      ac.1.hom ≫ P.counit.app N.carrier)
    (hc : G.map (P.unit.app N.carrier) ≫ ac.2.hom =
      N.str.hom ≫ P.unit.app N.carrier) :
    ∃ bc : (G.obj (P.openTerm.obj K.carrier) ≅ P.openTerm.obj K.carrier) ×
        (G.obj (P.closedTerm.obj K.carrier) ≅ P.closedTerm.obj K.carrier),
      G.map (P.counit.app K.carrier) ≫ K.str.hom =
        bc.1.hom ≫ P.counit.app K.carrier ∧
      G.map (P.unit.app K.carrier) ≫ bc.2.hom =
        K.str.hom ≫ P.unit.app K.carrier := by
  let e₀ : N.carrier ≅ K.carrier :=
    (CategoryTheory.Endofunctor.IsoAlgebra.forget G).mapIso e
  let a := P.openTerm.mapIso e₀
  let c := P.closedTerm.mapIso e₀
  refine ⟨⟨G.mapIso a.symm ≪≫ ac.1 ≪≫ a,
    G.mapIso c.symm ≪≫ ac.2 ≪≫ c⟩, ?_, ?_⟩
  · apply (cancel_epi (G.map a.hom)).mp
    have hn : a.hom ≫ P.counit.app K.carrier =
        P.counit.app N.carrier ≫ e₀.hom := P.counit.naturality e₀.hom
    have he : G.map e₀.hom ≫ K.str.hom = N.str.hom ≫ e₀.hom := e.hom.hom.h
    change G.map a.hom ≫ (G.map (P.counit.app K.carrier) ≫ K.str.hom) =
      G.map a.hom ≫ ((G.map a.inv ≫ ac.1.hom ≫ a.hom) ≫ P.counit.app K.carrier)
    calc
      _ = G.map (a.hom ≫ P.counit.app K.carrier) ≫ K.str.hom := by
        rw [G.map_comp, Category.assoc]
      _ = G.map (P.counit.app N.carrier ≫ e₀.hom) ≫ K.str.hom := by rw [hn]
      _ = G.map (P.counit.app N.carrier) ≫ N.str.hom ≫ e₀.hom := by
        rw [G.map_comp, Category.assoc, he, ← Category.assoc]
      _ = ac.1.hom ≫ a.hom ≫ P.counit.app K.carrier := by
        rw [← Category.assoc, ha, Category.assoc, ← hn]
      _ = _ := by
        simp only [← G.map_comp_assoc, Iso.hom_inv_id, G.map_id, Category.id_comp,
          Category.assoc]
  · apply (cancel_epi (G.map e₀.hom)).mp
    have hn : e₀.hom ≫ P.unit.app K.carrier =
        P.unit.app N.carrier ≫ c.hom := P.unit.naturality e₀.hom
    have he : G.map e₀.hom ≫ K.str.hom = N.str.hom ≫ e₀.hom := e.hom.hom.h
    change G.map e₀.hom ≫ (G.map (P.unit.app K.carrier) ≫
        (G.map c.inv ≫ ac.2.hom ≫ c.hom)) =
      G.map e₀.hom ≫ (K.str.hom ≫ P.unit.app K.carrier)
    calc
      _ = G.map (e₀.hom ≫ P.unit.app K.carrier) ≫
          G.map c.inv ≫ ac.2.hom ≫ c.hom := by rw [G.map_comp]; simp only [Category.assoc]
      _ = G.map (P.unit.app N.carrier) ≫ ac.2.hom ≫ c.hom := by
        rw [hn, G.map_comp]
        simp only [Category.assoc, ← G.map_comp_assoc, Iso.hom_inv_id, G.map_id,
          Category.id_comp]
      _ = N.str.hom ≫ e₀.hom ≫ P.unit.app K.carrier := by
        rw [← Category.assoc, hc, Category.assoc, hn]
      _ = _ := by rw [← Category.assoc, ← he, Category.assoc]

private theorem squares_of_inclusion
    {B : Type w} [Category.{w₁} B] {C : Type*} [Category C]
    (Q : SfRecollementPresentation B) (R : SfRecollementPresentation C)
    (F : B ⥤ C) (H : B ⥤ B) (G : C ⥤ C)
    (d : F ⋙ G ≅ H ⋙ F)
    (a : F ⋙ R.openTerm ≅ Q.openTerm ⋙ F)
    (c : F ⋙ R.closedTerm ≅ Q.closedTerm ⋙ F)
    (ha : ∀ N, a.hom.app N ≫ F.map (Q.counit.app N) = R.counit.app (F.obj N))
    (hc : ∀ N, R.unit.app (F.obj N) ≫ c.hom.app N = F.map (Q.unit.app N))
    (N : CategoryTheory.Endofunctor.IsoAlgebra H)
    (ac : (H.obj (Q.openTerm.obj N.carrier) ≅ Q.openTerm.obj N.carrier) ×
      (H.obj (Q.closedTerm.obj N.carrier) ≅ Q.closedTerm.obj N.carrier))
    (h₁ : H.map (Q.counit.app N.carrier) ≫ N.str.hom =
      ac.1.hom ≫ Q.counit.app N.carrier)
    (h₂ : H.map (Q.unit.app N.carrier) ≫ ac.2.hom =
      N.str.hom ≫ Q.unit.app N.carrier) :
    let K := (CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso d).obj N
    ∃ bc : (G.obj (R.openTerm.obj K.carrier) ≅ R.openTerm.obj K.carrier) ×
        (G.obj (R.closedTerm.obj K.carrier) ≅ R.closedTerm.obj K.carrier),
      G.map (R.counit.app K.carrier) ≫ K.str.hom =
        bc.1.hom ≫ R.counit.app K.carrier ∧
      G.map (R.unit.app K.carrier) ≫ bc.2.hom =
        K.str.hom ≫ R.unit.app K.carrier := by
  refine ⟨⟨G.mapIso (a.app N.carrier) ≪≫ d.app _ ≪≫ F.mapIso ac.1 ≪≫
    (a.app N.carrier).symm,
    G.mapIso (c.app N.carrier) ≪≫ d.app _ ≪≫ F.mapIso ac.2 ≪≫
      (c.app N.carrier).symm⟩, ?_, ?_⟩
  · change G.map (R.counit.app (F.obj N.carrier)) ≫
        (d.hom.app N.carrier ≫ F.map N.str.hom) =
      (G.map (a.hom.app N.carrier) ≫ d.hom.app _ ≫ F.map ac.1.hom ≫
        a.inv.app N.carrier) ≫ R.counit.app (F.obj N.carrier)
    have hd : G.map (F.map (Q.counit.app N.carrier)) ≫ d.hom.app N.carrier =
        d.hom.app _ ≫ F.map (H.map (Q.counit.app N.carrier)) :=
      d.hom.naturality (Q.counit.app N.carrier)
    have he : a.inv.app N.carrier ≫ R.counit.app (F.obj N.carrier) =
        F.map (Q.counit.app N.carrier) := by
      rw [← ha N.carrier, Iso.inv_hom_id_app_assoc]
    rw [← ha N.carrier, G.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (G.map (F.map (Q.counit.app N.carrier))), hd,
      Category.assoc, ← F.map_comp, h₁, F.map_comp]
    simp only [Iso.inv_hom_id_app_assoc]
  · change G.map (R.unit.app (F.obj N.carrier)) ≫
        (G.map (c.hom.app N.carrier) ≫ d.hom.app _ ≫ F.map ac.2.hom ≫
          c.inv.app N.carrier) =
      (d.hom.app N.carrier ≫ F.map N.str.hom) ≫ R.unit.app (F.obj N.carrier)
    apply (cancel_mono (c.hom.app N.carrier)).mp
    have hd : G.map (F.map (Q.unit.app N.carrier)) ≫ d.hom.app _ =
        d.hom.app N.carrier ≫ F.map (H.map (Q.unit.app N.carrier)) :=
      d.hom.naturality (Q.unit.app N.carrier)
    simp only [Category.assoc, Iso.inv_hom_id_app, hc]
    rw [← G.map_comp_assoc, hc]
    rw [reassoc_of% hd]
    erw [Category.comp_id]
    calc
      _ = d.hom.app N.carrier ≫
          (F.map (H.map (Q.unit.app N.carrier)) ≫ F.map ac.2.hom)  := by rfl
      _ = d.hom.app N.carrier ≫ F.map
          (H.map (Q.unit.app N.carrier) ≫ ac.2.hom) := by rw [F.map_comp]
      _ = d.hom.app N.carrier ≫ F.map
          (N.str.hom ≫ Q.unit.app N.carrier) := by rw [h₂]
      _ = _ := by rw [F.map_comp]

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The normalized common-stage counit and unit admit outer Frobenius isomorphisms.
This asserts the first two squares only, without a connecting arrow or uniqueness.
Source: current blueprint localization proof, Weil-structures paragraph and passage
from rational coefficients to common stages
(blueprint: lem-sf-normalized-common-stage-recollement-weil-squares).
Proof: take the complementary open of the closed immersion over the finite field.
Its geometric base change is the complementary open of i. At each finite coefficient
field use the normalized rational mate squares. The pullback, open-extension and
closed-image comparisons commute with scalar extension: their scalar comparisons
are the mates of the same pullback comparisons, so the unit and counit equations
paste with them. Descend these natural isomorphisms to the common-stage category.
The normalization isomorphisms identify their two operation vertices and their
unit/counit maps with R. Equivalently, represent a given middle Weil isomorphism
and its inverse at a common finite coefficient field and enlarge once to realize
both inverse equations. Apply the rational square theorem there, include its two
outer isomorphisms, and conjugate by the normalized stage comparisons and the
middle identification. Naturality of the counit and unit gives the two displayed
squares. Inverse squares supply inverse outer maps. Every finite diagram has a
common stage, so the construction applies to arbitrary common-stage Weil pairs,
including pairs whose structure map is not represented at their original stage.
Zero inputs and empty complements obey the same equations. No triangle or Hom
vanishing is used. -/
theorem sfNormalizedCommonStageRecollement_weil_squares
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X₀ Z₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (i₀ : Z₀ ⟶ X₀) [IsClosedImmersion i₀.left]
    (i : (D.geometricFiber Z₀).left ⟶ (D.geometricFiber X₀).left)
    [IsClosedImmersion i]
    (_hi : i = ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map i₀).left)
    (P : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      SfRecollementPresentation (sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (D.geometricFiber X₀).left))
    (Q : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      SfRecollementPresentation
        (GeneralAlgebraicallyClosedCoefficients.Stage l Ω (D.geometricFiber X₀).left L))
    (_hPQ : ∀ L, SfIntegralRecollementNormalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) i
        (sfRecollementGeometricNoetherian D X₀) (P L) ∧
      SfRationalRecollementNormalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
        (D.geometricFiber X₀).left (P L) (Q L))
    (R : SfRecollementPresentation
      (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X₀).left))
    (_hR : SfCommonStageRecollementNormalization l Ω (D.geometricFiber X₀).left Q R) :
    ∀ K : CategoryTheory.Endofunctor.IsoAlgebra
        (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω),
      ∃ ac : ((sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).obj
          (R.openTerm.obj K.carrier) ≅ R.openTerm.obj K.carrier) ×
        ((sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).obj
          (R.closedTerm.obj K.carrier) ≅ R.closedTerm.obj K.carrier),
        (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).map
            (R.counit.app K.carrier) ≫ K.str.hom = ac.1.hom ≫ R.counit.app K.carrier ∧
        (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω).map
            (R.unit.app K.carrier) ≫ ac.2.hom = K.str.hom ≫ R.unit.app K.carrier := by
  classical
  intro K
  let : Quiver.{0} Unit := ⟨fun _ _ ↦ PEmpty⟩
  let : ∀ a b : Unit, Finite (a ⟶ b) := fun _ _ ↦ inferInstanceAs (Finite PEmpty)
  let F : Unit ⥤q sfCommonStageWeilComplex D l hl X₀ Ω :=
    { obj := fun _ ↦ K, map := fun {a b} f ↦ PEmpty.elim f }
  obtain ⟨L, _, _, F₀, σ, _, _, _, _⟩ :=
    commonStageWeilFiniteRealization D l hl Ω X₀ Unit F PEmpty.{1}
      (fun r ↦ PEmpty.elim r) (fun r ↦ PEmpty.elim r)
      (fun r ↦ PEmpty.elim r) (fun r ↦ PEmpty.elim r)
      (fun r ↦ PEmpty.elim r) ∅
  obtain ⟨a, c, ha, hc⟩ := _hR.2 L
  obtain ⟨ac, h₁, h₂⟩ := sfNormalizedRationalRecollement_weil_squares l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) D hl X₀ Z₀ i₀ i _hi
    (P L) (Q L) (_hPQ L).1 (_hPQ L).2 (F₀.obj ())
  obtain ⟨bc, hb, hd⟩ := squares_of_inclusion (Q L) R
    (GeneralAlgebraicallyClosedCoefficients.inclusion L)
    (sfWeilFrobeniusPullback D l hl X₀
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
    (sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω)
    (stageSquare D l hl Ω X₀ L) a c ha hc (F₀.obj ()) ac h₁ h₂
  exact squares_of_iso R _ (σ ()) bc hb hd

end WeilConjectures
