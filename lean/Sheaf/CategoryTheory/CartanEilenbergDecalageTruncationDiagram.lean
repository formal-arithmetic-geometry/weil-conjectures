/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckComposablePair
public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import Sheaf.CategoryTheory.FilteredComplexDecalageComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Sheaf.CategoryTheory.CartanEilenbergDecalageInjectiveModel
import WeilConjectures.CategoryTheory.GrothendieckResolutionUnitComparison

/-! # The cohomology diagrams of the filtered injective comparison

Source: Stacks Project, Derived Categories, Tags 015X and 015N.
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false

private noncomputable def unitHomologyIso
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (G : B ⥤ C) [G.Additive] (T : CochainComplex.Plus B)
    [∀ m, Injective (T.obj.X m)] (n : ℤ) :
    (G.mapCochainComplexPlus.obj T).obj.homology n ≅
      (DerivedCategory.Plus.homologyFunctor C n).obj
        (G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj T)) :=
  (DerivedCategory.Plus.homologyFunctorObjQIso (G.mapCochainComplexPlus.obj T) n).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor C n).mapIso
      (asIso (G.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient B).obj T)))

private lemma unitHomologyMap_naturality
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (G : B ⥤ C) [G.Additive] {S T : CochainComplex.Plus B}
    (i : S ⟶ T) (n : ℤ) :
    HomologicalComplex.homologyMap (G.mapCochainComplexPlus.map i).hom n ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso (G.mapCochainComplexPlus.obj T) n).inv ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          (G.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient B).obj T)) =
      (DerivedCategory.Plus.homologyFunctorObjQIso (G.mapCochainComplexPlus.obj S) n).inv ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          (G.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient B).obj S)) ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map i)) := by
  have hQ := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality
    (G.mapCochainComplexPlus.map i) n
  have hU := congrArg ((DerivedCategory.Plus.homologyFunctor C n).map)
    (G.rightDerivedFunctorPlusUnit.naturality ((HomotopyCategory.Plus.quotient B).map i))
  simp only [Functor.map_comp] at hU
  apply (cancel_epi
    (DerivedCategory.Plus.homologyFunctorObjQIso (G.mapCochainComplexPlus.obj S) n).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← reassoc_of% hQ, Iso.hom_inv_id_assoc]
  exact hU

/-- A shifted cycle piece of a mapped Cartan--Eilenberg total computes the corresponding
canonical derived truncation, with its inclusion into the full derived object.
Source: Stacks Project, Derived Categories, Tag 015X, second filtration, and Tag 015N.
(blueprint: lem-sp-ce-decalage-truncation-diagram).

Proof. Write K = F(J), with J the prescribed injective resolution of P.X. Before
applying G, form the good horizontal truncation of I at q: retain horizontal
columns below q, replace column q by its horizontal cycles, and put zero above q.
The common augmentation induces an augmentation from tau_{<=q} K to this bicomplex.
Its vertical columns are resolutions: below q this is P.column_quasiIso, at q it is
P.horizontal_quasiIso for cycles, and above q both sides vanish. Its terms are
injective by P.term_injective and P.horizontal_injective. Both bicomplexes are
bounded below, so their totals give bounded below injective resolutions of K and
its good truncation. The finite diagonal inclusions identify the truncated total
with Dec(L)^(-q) before applying G: all columns below q occur in full, while the
last column is the kernel of the outgoing horizontal differential. G preserves
these kernels and finite sums, hence the identification persists after applying G.
The total inclusion commutes with the two augmentations. Naturality of the derived
unit and its invertibility on bounded below complexes of injectives give the
cohomology comparison isomorphisms e and d and their inclusion square. Transport
the source complexes by the canonical resolution identification RF(P.X) = Q(F(J));
canonical truncation is functorial for this identification. This identifies the two
targets with the indicated spectral-object terms. The normalization of the full
comparison follows from the defining equation of the acyclic-composite derived
isomorphism on the injective resolution J. Namely it carries the composite derived
unit to the unit of GF; taking homology and the extension-by-zero homology
comparison gives the second displayed equation. The component formula for a makes
it exactly the mapped total augmentation in this equation. The comparison holds
for every q >= 0 and every cohomology degree n; the caller only needs 0 <= q < n. -/
theorem cartanEilenberg_decalage_truncation_diagram
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (P : CartanEilenbergPresentation F)
    (L : DecreasingFiltration (P.total G))
    (hL : ∀ p m : ℤ, L.complexStep p m =
      ((((CartanEilenbergPresentation.mappedFunctor G).obj P.I).secondFiltration m).step p))
    (a : (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex).extend
        ComplexShape.embeddingUpNat ⟶ P.total G)
    (ha : (∀ n : ℕ, a.f (n : ℤ) =
      (HomologicalComplex.extendXIso
        (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex)
        ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom ≫
      G.map (F.map (P.J.cocomplex.extendXIso ComplexShape.embeddingUpNat
        (rfl : (n : ℤ) = n)).inv ≫ (P.e.f (n : ℤ)).f 0) ≫
      (HomologicalComplex.extendXIso
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (P.I.X (n : ℤ)))
        ComplexShape.embeddingUpNat (rfl : (0 : ℤ) = 0)).inv ≫
      HomologicalComplex₂.ιTotalOrZero
        ((CartanEilenbergPresentation.mappedFunctor G).obj P.I)
        (ComplexShape.up ℤ) (n : ℤ) 0 (n : ℤ)))
    (q : ℤ) (n : ℕ) (hq0 : 0 ≤ q) :
    ∃ (e : (P.total G).homology (n : ℤ) ≅
        ((F.grothendieckSpectralObject G P.X).H (n : ℤ)).obj
          (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))))
      (d : (L.decalageComplex (-q)).homology (n : ℤ) ≅
        ((F.grothendieckSpectralObject G P.X).H (n : ℤ)).obj
          (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((q + 1 : ℤ) : EInt))))),
      HomologicalComplex.homologyMap (L.decalageι (-q)) (n : ℤ) ≫ e.hom =
        d.hom ≫ ((F.grothendieckSpectralObject G P.X).H (n : ℤ)).map
          (twoδ₂Toδ₁' (⊥ : EInt) ((q + 1 : ℤ) : EInt) ⊤ bot_le le_top) ∧
      HomologicalComplex.homologyMap a (n : ℤ) ≫ e.hom ≫
          (F.grothendieckSpectralObjectHBotTopIso G hFG n).hom.app P.X =
        (HomologicalComplex.extendHomologyIso
          (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex)
          ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom ≫
          (P.J.isoRightDerivedObj (F ⋙ G) n).inv := by
  classical
  let K₀ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex
  let K : CochainComplex.Plus B :=
    ⟨K₀.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let R := G.rightDerivedFunctorPlus
  let H := DerivedCategory.Plus.homologyFunctor C (n : ℤ)
  let X := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj P.X)
  obtain ⟨T, S, b, i, r, c, d, hT, hS, hb, hri, hid, hba⟩ :=
    cartanEilenberg_decalage_injective_model F G P L hL a ha q hq0
  have : ∀ m, Injective (T.obj.X m) := hT
  have : ∀ m, Injective (S.obj.X m) := hS
  have : QuasiIso b.hom := hb
  have : IsIso (DerivedCategory.Plus.Q.map b) := by
    apply (DerivedCategory.Plus.isIso_iff _).mpr
    intro m
    have hQ := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality b m
    have : IsIso ((DerivedCategory.Plus.homologyFunctor B m).map
        (DerivedCategory.Plus.Q.map b) ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso T m).hom) := by
      rw [hQ]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (DerivedCategory.Plus.homologyFunctorObjQIso T m).hom
  let eb := asIso (DerivedCategory.Plus.Q.map b)
  obtain ⟨eF, heF, hcomp⟩ :=
    exists_grothendieck_resolution_unit_comparison F G hFG P.X P.J n
  let e₀ := (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (n : ℤ)).mapIso
      c.symm ≪≫ unitHomologyIso G T (n : ℤ) ≪≫ H.mapIso (R.mapIso eb.symm) ≪≫
        H.mapIso (R.mapIso eF.symm)
  let d₀ := (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (n : ℤ)).mapIso
      d.symm ≪≫ unitHomologyIso G S (n : ℤ) ≪≫ H.mapIso (R.mapIso r.symm) ≪≫
        H.mapIso (R.mapIso ((t.truncLT (q + 1)).mapIso eF.symm))
  refine ⟨e₀, d₀, ?_, ?_⟩
  · have hspec : ((F.grothendieckSpectralObject G P.X).H (n : ℤ)).map
        (twoδ₂Toδ₁' (⊥ : EInt) ((q + 1 : ℤ) : EInt) ⊤ bot_le le_top) =
        H.map (R.map ((t.truncLTι (q + 1)).app X)) := by
      change H.map (R.map _) = _
      congr 2
      dsimp [Triangulated.TStructure.spectralObjectFunctor,
        Triangulated.TStructure.spectralObject, Triangulated.TStructure.ω₁]
      simp [Triangulated.TStructure.eTruncLT,
        Triangulated.TStructure.eTruncGE, t, X]
      rfl
    rw [hspec]
    change HomologicalComplex.homologyMap (L.decalageι (-q)) (n : ℤ) ≫ e₀.hom =
      d₀.hom ≫ H.map (R.map ((t.truncLTι (q + 1)).app X))
    have hid' : L.decalageι (-q) ≫ c.inv =
        d.inv ≫ (G.mapCochainComplexPlus.map i).hom := by
      apply (cancel_epi d.hom).mp
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [← hid]
      simp
    have hr : DerivedCategory.Plus.Q.map i ≫ eb.inv =
        r.inv ≫ (t.truncLTι (q + 1)).app (DerivedCategory.Plus.Q.obj K) := by
      apply (cancel_epi r.hom).mp
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [hri]
      simp [eb, K, K₀, t]
    have hrt : DerivedCategory.Plus.Q.map i ≫ eb.inv ≫ eF.inv =
        r.inv ≫ (t.truncLT (q + 1)).map eF.inv ≫ (t.truncLTι (q + 1)).app X := by
      rw [← Category.assoc, hr, Category.assoc, (t.truncLTι (q + 1)).naturality]
      rfl
    let Hc := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (n : ℤ)
    dsimp only [e₀, d₀, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Category.assoc]
    change Hc.map (L.decalageι (-q)) ≫ Hc.map c.inv ≫
        (unitHomologyIso G T (n : ℤ)).hom ≫ H.map (R.map eb.inv) ≫
          H.map (R.map eF.inv) =
      Hc.map d.inv ≫ (unitHomologyIso G S (n : ℤ)).hom ≫ H.map (R.map r.inv) ≫
        H.map (R.map ((t.truncLT (q + 1)).map eF.inv)) ≫
          H.map (R.map ((t.truncLTι (q + 1)).app X))
    have hunit : Hc.map (G.mapCochainComplexPlus.map i).hom ≫
        (unitHomologyIso G T (n : ℤ)).hom =
        (unitHomologyIso G S (n : ℤ)).hom ≫ H.map (R.map (DerivedCategory.Plus.Q.map i)) :=
      by simpa [unitHomologyIso, Hc, H, R, Category.assoc] using
        unitHomologyMap_naturality G i (n : ℤ)
    rw [← Hc.map_comp_assoc, hid', Hc.map_comp, Category.assoc,
      reassoc_of% hunit]
    simp only [← Functor.map_comp, ← Category.assoc]
    simp only [Category.assoc]
    rw [hrt]
  · let Hc := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (n : ℤ)
    let m := HomologicalComplex.mapExtendIso K₀ ComplexShape.embeddingUpNat G
    let z := HomologicalComplex.extendHomologyIso
      (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex)
      ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)
    let U := G.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient B).obj K)
    let QG := DerivedCategory.Plus.homologyFunctorObjQIso (G.mapCochainComplexPlus.obj K)
      (n : ℤ)
    have hba' : a ≫ c.inv = m.inv ≫ (G.mapCochainComplexPlus.map b).hom := by
      apply (cancel_epi m.hom).mp
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [← hba]
      simp
    have hunit : Hc.map (G.mapCochainComplexPlus.map b).hom ≫
        (unitHomologyIso G T (n : ℤ)).hom =
        QG.inv ≫ H.map U ≫ H.map (R.map (DerivedCategory.Plus.Q.map b)) := by
      simpa [Hc, H, R, QG, U, unitHomologyIso, Category.assoc] using
        unitHomologyMap_naturality G b (n : ℤ)
    have hbase : Hc.map a ≫ Hc.map c.inv ≫ (unitHomologyIso G T (n : ℤ)).hom ≫
        H.map (R.map eb.inv) =
        z.hom ≫ (P.J.isoRightDerivedObj (F ⋙ G) n).inv ≫
          (F.grothendieckSpectralObjectHBotTopIso G hFG n).inv.app P.X ≫
            H.map (R.map eF.hom) := by
      rw [← Hc.map_comp_assoc, hba', Hc.map_comp, Category.assoc,
        reassoc_of% hunit]
      simp only [← Functor.map_comp, eb, asIso_inv, IsIso.hom_inv_id, Functor.map_id]
      erw [Category.comp_id]
      apply (cancel_epi z.inv).mp
      simp only [Iso.inv_hom_id_assoc]
      convert hcomp.symm using 1 <;> rfl
    change Hc.map a ≫ e₀.hom ≫
      (F.grothendieckSpectralObjectHBotTopIso G hFG n).hom.app P.X = _
    dsimp only [e₀, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Category.assoc]
    rw [reassoc_of% hbase]
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id,
      Functor.map_id]
    erw [H.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

end CategoryTheory
