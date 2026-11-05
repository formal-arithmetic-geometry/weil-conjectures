/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteDiagonal
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryForgetComparison
import WeilConjectures.SmoothPurity.OpenClosedIntegralSections
import all WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization
import all WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate

/-! # The ordinary supported finite source of a normalized diagonal -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings SpTowerShriek.tau lineModule
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem supported_integral_unit_epi (S : Scheme.{u}) :
    Epi (supportedIntegralUnit S) := by
  obtain ⟨L, t, ht, hT, η, hη, hηt⟩ :=
    AlgebraicGeometry.Etale.exists_integral_openClosed_sections
      (diagonalImmersion S) (diagonalImmersion S).openComplement rfl
  have : Epi (AlgebraicGeometry.Etale.supportedIntegralUnit (diagonalImmersion S)) :=
    hT.epi_g
  unfold supportedIntegralUnit
  infer_instance

/-- Fullness extracts an ordinary source map from the derived scalar adjunct. -/
private theorem scalar_adjunct_single
    {T : Scheme.{u}} (c : Chern l E T) (X : Systems T (Rrings l T))
    (N : Systems T (Arings l E T))
    (s : c.scalar.T.obj ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj X) ≅
      (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).obj N) :
    ∃ q : X ⟶ (WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj N,
      (c.scalar.adjunction.homEquiv _ _) s.hom ≫
        ((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N =
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map q := by
  let f := (c.scalar.adjunction.homEquiv _ _) s.hom ≫
    ((WeilConjectures.SemilinearSections.res
      (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N
  exact ⟨(DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).preimage f,
    ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map_preimage f).symm⟩

/-- Exact closed direct image reads the canonical derived geometric unit on singles. -/
private theorem exact_right_single_unit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions B]
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (ad : F ⊣ G) (X : A) :
    ad.mapDerivedCategoryRightDerivedAdjunction.unit.app
        ((DerivedCategory.singleFunctor A 0).obj X) ≫
      G.rightDerivedFunctor.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      G.singleFunctorCompRightDerivedFunctorIso.hom.app (F.obj X) =
    (DerivedCategory.singleFunctor A 0).map (ad.unit.app X) := by
  let K := (HomotopyCategory.quotient A (.up ℤ)).obj
    ((CochainComplex.singleFunctor A 0).obj X)
  let ae := CategoryTheory.exactLocalizationDerivedAdjunction ad
  have hm : ae.unit.app (DerivedCategory.Qh.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
    DerivedCategory.Qh.map ((ad.mapHomotopyCategory (.up ℤ)).unit.app K) := by
    dsimp only [K]
    rw [CategoryTheory.Adjunction.factorsh_complex F]
    change ae.unit.app (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor A 0).obj X)) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app
        ((CochainComplex.singleFunctor A 0).obj X)) ≫
      G.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient B (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj
            ((CochainComplex.singleFunctor A 0).obj X))) = _
    rw [CategoryTheory.Adjunction.factorsh_complex G]
    rw [CategoryTheory.exact_unit_app]
    simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc,
      Iso.inv_hom_id_app]
    erw [G.mapDerivedCategory.map_id]
    rw [Category.id_comp]
    erw [Iso.inv_hom_id_app, Category.comp_id]
    rw [ad.mapHomotopyCategory_unit_app_quotient (.up ℤ)]
    rfl
  have ht := CategoryTheory.Adjunction.single_unit_term F G ad X
  have hc : ae.unit.app (DerivedCategory.Qh.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) =
    (DerivedCategory.singleFunctor A 0).map (ad.unit.app X) ≫
      (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj X) ≫
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app X) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) :=
    (cancel_mono (G.mapDerivedCategoryFactorsh.hom.app
      ((F.mapHomotopyCategory (.up ℤ)).obj K))).mp
      (by simpa only [Functor.comp_obj, Functor.id_obj, K, Functor.map_comp,
        Category.assoc] using hm.trans ht.symm)
  have hu : ae.unit.app (DerivedCategory.Qh.obj K) =
    (DerivedCategory.singleFunctor A 0).map (ad.unit.app X) ≫
      (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj X) ≫
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app X) :=
    (cancel_mono (G.mapDerivedCategory.map
      (F.mapDerivedCategoryFactorsh.hom.app K))).mp
      (by simpa only [Category.assoc] using hc)
  have hv : ae.unit.app ((DerivedCategory.singleFunctor A 0).obj X) ≫
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) =
    (DerivedCategory.singleFunctor A 0).map (ad.unit.app X) := by
    change ae.unit.app (DerivedCategory.Qh.obj K) ≫ _ = _
    rw [hu]
    simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc,
      Iso.inv_hom_id_app]
    erw [G.mapDerivedCategory.map_id]
    rw [Category.id_comp, Iso.inv_hom_id_app]
    exact Category.comp_id _
  have he := AlgebraicGeometry.ProEtale.SemilinearProperOpen.Normalization.exact_adjunction_eq ad
  have he' := congrArg (fun a ↦ a.unit.app ((DerivedCategory.singleFunctor A 0).obj X)) he
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app] at he'
  simp only [Functor.singleFunctorCompRightDerivedFunctorIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  erw [G.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  rw [reassoc_of% he']
  exact hv

/-- The source-normalized geometric unit is the single of its ordinary adjunct. -/
private theorem coefficient_unit_single
    {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S))
    (p : CoefficientPullback l E b (diagonalImmersion S) g) :
    unitArrow l E p ≫ g.push.singleFunctorCompRightDerivedFunctorIso.hom.app
        (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))) =
      (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
        (Arings l E (diagonalSurface S))) 0).map
          ((g.ordinaryAdjunction.homEquiv _ _) p.iso.hom) := by
  let X := coefficient (diagonalSurface S) (Arings l E (diagonalSurface S))
  have h := exact_right_single_unit g.ordinaryAdjunction X
  unfold unitArrow CoefficientPullback.derivedIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  erw [g.push.singleFunctorCompRightDerivedFunctorIso.hom.naturality p.iso.hom]
  erw [reassoc_of% h]
  simp only [Functor.comp_map]
  erw [← Functor.map_comp, Adjunction.homEquiv_unit]
  rfl

/-- Two normalized adjunction transposes give the composite ordinary source map. -/
private theorem reduction_scalar_transpose
    {T : Scheme.{u}} (c : Chern l E T) (X : Ab T)
    (M : Systems T (Rrings l T)) (q₀ : X ⟶ c.reduction.forget.F.obj M)
    (N : Systems T (Arings l E T))
    (a : c.reduction.derived.obj ((DerivedCategory.singleFunctor (Ab T) 0).obj X) ≅
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        M)
    (ha : c.reduction.model.sourceNormalization a q₀)
    (s : c.scalar.T.obj
        ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
          M) ⟶
      (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).obj N)
    (q : M ⟶
      (WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj N)
    (hs : (c.scalar.adjunction.homEquiv _ _) s ≫
        ((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N =
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map q) :
    ((c.reduction.model.derivedAdjunction.comp c.scalar.adjunction).homEquiv _ _)
        (c.scalar.T.map a.hom ≫ s) ≫
      c.reduction.forget.F.mapDerivedCategory.map
        (((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N) ≫
      (c.reduction.forget.F.mapDerivedCategorySingleFunctor 0).hom.app
        ((WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj N) =
    (DerivedCategory.singleFunctor (Ab T) 0).map
      (q₀ ≫ c.reduction.forget.F.map q) := by
  rw [Adjunction.comp_homEquiv]
  change (c.reduction.model.derivedAdjunction.homEquiv _ _)
      ((c.scalar.adjunction.homEquiv _ _) (c.scalar.T.map a.hom ≫ s)) ≫ _ = _
  erw [c.scalar.adjunction.homEquiv_naturality_left,
    c.reduction.model.derivedAdjunction.homEquiv_naturality_right]
  simp only [Category.assoc, ← c.reduction.forget.F.mapDerivedCategory.map_comp_assoc]
  rw [hs]
  erw [(c.reduction.forget.F.mapDerivedCategorySingleFunctor 0).hom.naturality q]
  rw [← Category.assoc, ha]
  simp only [Functor.comp_map, Functor.map_comp]

/-- The composite coefficient unit has the prescribed ordinary integer generator. -/
private theorem coefficient_source_transpose
    {T : Scheme.{u}} (c : Chern l E T) (hc : c.Normalized l E) :
    let e := c.scalar.T.mapIso c.unitIso ≪≫ c.scalarUnit
    ((c.reduction.model.derivedAdjunction.comp c.scalar.adjunction).homEquiv _ _)
        e.hom ≫
      c.reduction.forget.F.mapDerivedCategory.map
        (((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app
            (coefficient T (Arings l E T))) ≫
      (c.reduction.forget.F.mapDerivedCategorySingleFunctor 0).hom.app
        ((WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj
          (coefficient T (Arings l E T))) =
    (DerivedCategory.singleFunctor (Ab T) 0).map
      (integerGenerator T (Rrings l T) c.reduction.forget ≫
        c.reduction.forget.F.map (scalarGenerator l E T)) := by
  exact reduction_scalar_transpose l E c (integers T) (coefficient T (Rrings l T))
    (integerGenerator T (Rrings l T) c.reduction.forget) (coefficient T (Arings l E T))
    c.unitIso hc.1 c.scalarUnit.hom (scalarGenerator l E T) hc.2.2

/-- The supplied geometric source equation remains exact after both adjunctions. -/
private theorem diagonal_source_transpose
    {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {c : Chern l E (diagonalSurface S)} (d : Diagonal l E b S c) :
    let k := (DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).map
      ((constant (diagonalSurface S)).map (supportedIntegralUnit S))
    let ad := c.reduction.model.derivedAdjunction.comp c.scalar.adjunction
    let e := c.scalar.T.mapIso c.unitIso ≪≫ c.scalarUnit
    k ≫ (ad.homEquiv _ _) d.sourceIso.hom =
      (ad.homEquiv _ _) (e.hom ≫ unitArrow l E d.coefficientPullback) := by
  dsimp only
  rw [← Adjunction.homEquiv_naturality_left]
  apply congrArg ((c.reduction.model.derivedAdjunction.comp
    c.scalar.adjunction).homEquiv _ _)
  rw [← d.source_normalization]
  unfold diagonalExtendedUnit
  simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc, ← c.scalar.T.map_comp_assoc,
    ]

set_option maxHeartbeats 1600000 in
-- The composite exact single comparisons need additional kernel checking time.
/-- Before finite evaluation, the extracted map already has the required ordinary
source equation after precomposition with the supported integral unit. -/
private theorem ordinary_source_precompose
    {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {c : Chern l E (diagonalSurface S)} (hc : c.Normalized l E)
    (d : Diagonal l E b S c)
    (a : c.reduction.derived.obj
        ((DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).obj
          ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))) ≅
      (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
        (Rrings l (diagonalSurface S))) 0).obj
        (c.reduction.ordinary.obj
          ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))))
    (ha : c.reduction.model.sourceNormalization a
      (c.reduction.model.adjunction.unit.app
        ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)))) :
    let X := (constant (diagonalSurface S)).obj (diagonalIntegralSource S)
    let N := d.geometry.push.obj
      (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
    let s := c.scalar.T.mapIso a.symm ≪≫ d.sourceIso ≪≫
      d.geometry.push.singleFunctorCompRightDerivedFunctorIso.app
        (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
    ∀ (q : c.reduction.ordinary.obj X ⟶
        (WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E (diagonalSurface S))).obj N),
      ((c.scalar.adjunction.homEquiv _ _) s.hom ≫
        ((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E (diagonalSurface S))).mapDerivedCategorySingleFunctor
            0).hom.app N =
        (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
          (Rrings l (diagonalSurface S))) 0).map q) →
    (constant (diagonalSurface S)).map (supportedIntegralUnit S) ≫
        c.reduction.model.adjunction.unit.app X ≫ c.reduction.forget.F.map q =
      integerGenerator (diagonalSurface S) (Rrings l (diagonalSurface S))
          c.reduction.forget ≫
        c.reduction.forget.F.map (scalarGenerator l E (diagonalSurface S) ≫
          (WeilConjectures.SemilinearSections.res
            (coefficientSystemMap l E (diagonalSurface S))).map
              ((d.geometry.ordinaryAdjunction.homEquiv _ _) d.coefficientPullback.iso.hom)) := by
  intro X N s q hq
  let G := c.reduction.forget.F
  let H := WeilConjectures.SemilinearSections.res
    (coefficientSystemMap l E (diagonalSurface S))
  let ad := c.reduction.model.derivedAdjunction.comp c.scalar.adjunction
  let κ := Functor.isoWhiskerRight (H.mapDerivedCategorySingleFunctor 0)
      G.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft H (G.mapDerivedCategorySingleFunctor 0)
  let t := (d.geometry.ordinaryAdjunction.homEquiv _ _) d.coefficientPullback.iso.hom
  let e := c.scalar.T.mapIso c.unitIso ≪≫ c.scalarUnit
  have hfactor : c.scalar.T.map a.hom ≫ s.hom =
      d.sourceIso.hom ≫ d.geometry.push.singleFunctorCompRightDerivedFunctorIso.hom.app
        (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))) := by
    dsimp only [s]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      ← c.scalar.T.map_comp_assoc, Iso.hom_inv_id]
    erw [c.scalar.T.map_id]
    exact Category.id_comp _
  have h₁ := reduction_scalar_transpose l E c X (c.reduction.ordinary.obj X)
    (c.reduction.model.adjunction.unit.app X) N a ha s.hom q hq
  rw [hfactor] at h₁
  have h₂ := coefficient_source_transpose l E c hc
  have ht := diagonal_source_transpose l E d
  have ht' :
      (DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).map
          ((constant (diagonalSurface S)).map (supportedIntegralUnit S)) ≫
        (ad.homEquiv _ _) (d.sourceIso.hom ≫
          d.geometry.push.singleFunctorCompRightDerivedFunctorIso.hom.app
            (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))) =
      (ad.homEquiv _ _) (e.hom ≫
        (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
          (Arings l E (diagonalSurface S))) 0).map t) := by
    rw [ad.homEquiv_naturality_right, ← Category.assoc, ht,
      ← ad.homEquiv_naturality_right]
    rw [Category.assoc, coefficient_unit_single]
    rfl
  apply (DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).map_injective
  rw [Functor.map_comp]
  rw [← h₁]
  rw [← Category.assoc, ← Category.assoc]
  erw [ht']
  rw [ad.homEquiv_naturality_right]
  have hκ : (ad.homEquiv _ _) e.hom ≫ κ.hom.app
      (coefficient (diagonalSurface S) (Arings l E (diagonalSurface S))) =
    (DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).map
      (integerGenerator (diagonalSurface S) (Rrings l (diagonalSurface S))
        c.reduction.forget ≫ G.map (scalarGenerator l E (diagonalSurface S))) := h₂
  have hκN (Y) : κ.hom.app Y = G.mapDerivedCategory.map
      ((H.mapDerivedCategorySingleFunctor 0).hom.app Y) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (H.obj Y) := rfl
  simp only [Category.assoc, Functor.comp_map]
  rw [← hκN]
  have hn' : G.mapDerivedCategory.map
      ((WeilConjectures.SemilinearSections.resD (coefficientSystemMap l E (diagonalSurface S))).map
        ((DerivedCategory.singleFunctor (Systems (diagonalSurface S)
          (Arings l E (diagonalSurface S))) 0).map t)) ≫ κ.hom.app N =
      κ.hom.app (coefficient (diagonalSurface S) (Arings l E (diagonalSurface S))) ≫
        (DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).map (G.map (H.map t)) :=
    κ.hom.naturality t
  rw [hn']
  rw [← Category.assoc, hκ]
  rw [← Functor.map_comp, Category.assoc, ← G.map_comp]

/-- The scalar adjunct of the supported comparison has precisely the canonical
supported integral quotient at every finite level.

Source: latest blueprint geometric classes proof (3), the supported source
normalization in the finite diagonal calculation.
(blueprint: lem-sp-tower-class-diagonal-finite-source).

Proof: compose the inverse reduction comparison, the supplied supported source
isomorphism and the exact geometric single comparison. Transpose this composite
through the scalar adjunction. Fullness of the single functor gives its unique
ordinary module map q. Naturality of the two adjunction units and the two
normalized coefficient-unit comparisons turn d.source_normalization into an
equality of the corresponding ordinary maps after restriction and evaluation.
The exact-right-adjoint single-unit equation identifies the geometric side with
the ordinary coefficient pullback adjunct. Its prescribed section formula sends
each coefficient integer to its residue times one on the base-changed chart.
The reduction and scalar generator section equations give the same formula on
the other side. The transported supported integral unit is epic: the etale
open/closed integral section sequence is short exact and exact inverse image
preserves its epimorphism; the two site comparisons are isomorphisms. Hence
precomposition with that unit detects equality of these ordinary sheaf maps.
The unique generator-normalized supported quotient is therefore exactly the
composite displayed below. All statements compare degree-zero sheaf maps;
no faithfulness of finite evaluation on arbitrary derived maps is used. -/
theorem exists_diagonalFiniteSource {b : SpTowerShriek.Base l E}
    {S : Scheme.{u}} [IsNoetherian S]
    {c : Chern l E (diagonalSurface S)} (hc : c.Normalized l E)
    (d : Diagonal l E b S c) :
    let X := (constant (diagonalSurface S)).obj (diagonalIntegralSource S)
    let N := d.geometry.push.obj
      (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
    ∀ (a : c.reduction.derived.obj
        ((DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).obj X) ≅
      (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
        (Rrings l (diagonalSurface S))) 0).obj (c.reduction.ordinary.obj X))
      (_ha : c.reduction.model.sourceNormalization a
        (c.reduction.model.adjunction.unit.app X)),
    let s := c.scalar.T.mapIso a.symm ≪≫ d.sourceIso ≪≫
      (d.geometry.push.singleFunctorCompRightDerivedFunctorIso).app
        (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
    ∃ q : c.reduction.ordinary.obj X ⟶
        (WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E (diagonalSurface S))).obj N,
      ((c.scalar.adjunction.homEquiv _ _) s.hom ≫
        ((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E (diagonalSurface S))).mapDerivedCategorySingleFunctor
            0).hom.app N =
        (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
          (Rrings l (diagonalSurface S))) 0).map q) ∧
      ∀ n : ℕ,
        (abEvaluation (diagonalSurface S) n).map
            (c.reduction.model.adjunction.unit.app X) ≫
          (c.reduction.forget.F ⋙ abEvaluation (diagonalSurface S) n).map q ≫
          (finiteScalarForgetIso l E c n).hom.app N =
        finiteSupportedQuotient l E d.geometry n := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses
