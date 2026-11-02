/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.MixedRepresentationNormalized
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat

/-! # Representative cancellation for the finite restriction square -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

private theorem mixed_representation_finite
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P Q : CochainComplex (FiniteModules A X) ℤ) :
    let F := ProEtale.upperStar (ModuleCat.{u + 1} A) j
    let a := F.mapDerivedCategoryFactors.hom
    let muX := Functor.LaxMonoidal.μ (DerivedCategory.Q (C := FiniteModules A X)) P Q
    let fc := F.mapHomologicalComplex (.up ℤ)
    let muU := Functor.LaxMonoidal.μ (DerivedCategory.Q (C := FiniteModules A U))
      (fc.obj P) (fc.obj Q)
    let c := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q
    let delta := ((ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso
      (ModuleCat.{u + 1} A) j).hom.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q)
    let n := a.app P ⊗ₘ (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app
      (DerivedCategory.Q.obj Q) ≫ a.app Q)
    delta ≫ F.mapDerivedCategory.map muX ≫ a.app (finiteTotal A X P Q) =
      n ≫ muU ≫ DerivedCategory.Q.map (inv c) := by
  let E : IsGrothendieckAbelian.{u + 1} (ModuleCat.{u + 1} A) → Prop :=
    fun h ↦
      letI : IsGrothendieckAbelian.{u + 1} (ModuleCat.{u + 1} A) := h
      let F := ProEtale.upperStar (ModuleCat.{u + 1} A) j
      let a := F.mapDerivedCategoryFactors.hom
      let muX := Functor.LaxMonoidal.μ (DerivedCategory.Q (C := FiniteModules A X)) P Q
      let fc := F.mapHomologicalComplex (.up ℤ)
      let muU := Functor.LaxMonoidal.μ (DerivedCategory.Q (C := FiniteModules A U))
        (fc.obj P) (fc.obj Q)
      let c := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q
      let delta := ((ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso
        (ModuleCat.{u + 1} A) j).hom.app (DerivedCategory.Q.obj P)).app
          (DerivedCategory.Q.obj Q)
      let n := a.app P ⊗ₘ (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app
        (DerivedCategory.Q.obj Q) ≫ a.app Q)
      delta ≫ F.mapDerivedCategory.map muX ≫ a.app (HomologicalComplex.mapBifunctor P Q
        (curriedTensor (FiniteModules A X)) (.up ℤ)) =
        n ≫ muU ≫ DerivedCategory.Q.map (inv c)
  have hn : E (instIsGrothendieckAbelianModuleCat A) := by
    exact mixed_representation_normalized A j P Q
  have he : E (instIsGrothendieckAbelianModuleCat A) =
      E (ModuleCat.isGrothendieckAbelian_of_commRing A) :=
    congrArg E (proof_irrel _ _)
  exact he.mp hn

private theorem resolving_of_iso {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {P Q : CochainComplex (Mod R) ℤ} (a : P ≅ Q) (hQ : resolving R Q) :
    resolving R P := by
  let := SheafOfModules.monoidalCategory R
  constructor
  · intro F hF
    exact HomologicalComplex.Acyclic.of_iso (hQ.1 F hF)
      ((total R).mapIso (Iso.prod (Iso.refl F) a.symm))
  · intro n
    have hcat : exactFunctor _ _ (tensorRight (Q.X n)) :=
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (Q.X n)) (hQ.2 n)
    have hcat' : exactFunctor _ _ (tensorRight (P.X n)) :=
      (exactFunctor _ _).prop_of_iso
        ((curriedTensor (Mod R)).flip.mapIso
          ((HomologicalComplex.eval _ _ n).mapIso a.symm)) hcat
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X n)).symm hcat'

/-- Cancellation of the cochain model equations on resolving finite pairs.
Source: Stacks 07A4 and 0GL1; steps 1, 3 and 4 of
lem-sf-finite-tensor-restriction-coherence.

Proof: transport resolving through the ordinary open pin; restriction preserves
resolving by the supplied TensorComparison.preserves. Apply the two tensor pins'
model equations to these pairs and the restriction part of the exact open pin.
The published mixed representative equation writes delta followed by the native
localization tensorator as the total comparison followed by that tensorator.
Each native tensorator on these resolving pairs is invertible: its realized
image is a composite of the isomorphisms in FiniteTensorModel, and realization
reflects isomorphisms. Postcompose the proposed square with the realization and
restriction factor isomorphisms. Substitute the ringed tensor comparison's stored
representative equation, and use its naturality to move the ordinary open pin
across the representative isomorphisms. Cancel those isomorphisms and the native
tensorators. The remaining equality is Q applied to h_total at P,Q. Reverse the
cancellations to obtain the displayed representative square.
(blueprint: lem-sf-finite-restriction-representative-square) -/
theorem finite_restriction_representative_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o)
    (h_total :
    let R := (finiteInput A gU j' j g sq).R
    letI : (restrict .ordinary j R).Additive := (restriction_exact .ordinary j R).1
    let fc := (ProEtale.upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)
    let h := (restrict .ordinary j R).mapHomologicalComplex (.up ℤ)
    let v := NatTrans.mapHomologicalComplex e.open_pin.star.hom (.up ℤ)
    ∀ P Q : CochainComplex (FiniteModules A X) ℤ,
      (finiteComplexRealization e.realizeU).map
          (inv (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
            (ProEtale.upperStar (ModuleCat.{u + 1} A) j)).app P).app Q)) ≫
        v.app (finiteTotal A X P Q) ≫
        h.map (e.tensorX_pin.totalIso P Q).hom =
      (e.tensorU_pin.totalIso (fc.obj P) (fc.obj Q)).hom ≫
        (total (restrictRing .ordinary j R)).map
          (Prod.mkHom (v.app P) (v.app Q)) ≫
        totalMap o.tensorX o.tensorU (restrict .ordinary j R) o.restrictionTensor
          o.tensorComparison.comm ((finiteComplexRealization e.realizeX).obj P)
            ((finiteComplexRealization e.realizeX).obj Q))
    (P Q : CochainComplex (FiniteModules A X) ℤ)
    (hp : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj P))
    (hq : resolving (finiteInput A gU j' j g sq).R
      ((finiteComplexRealization e.realizeX).obj Q)) :
    let r := Functor.isoWhiskerRight
      (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory.symm
      e.realizeU.derived ≪≫ e.openPull
    let M := DerivedCategory.Q.obj P
    let N := DerivedCategory.Q.obj Q
    e.realizeU.derived.map
          (((ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso
            (ModuleCat.{u + 1} A) j).hom.app M).app N) ≫
        r.hom.app ((finiteTensor A X).obj (M, N)) ≫
        o.opens.jStar.map (e.tensorX.hom.app (M, N)) =
      e.tensorU.hom.app ((finitePull A j).obj M,
          (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj N) ≫
        o.tensorU.functor.map
          (CategoryTheory.Prod.mkHom (r.hom.app M) (e.openPull.hom.app N)) ≫
        o.tensorComparison.comparison.inv.app
          (e.realizeX.derived.obj M, e.realizeX.derived.obj N) := by
  -- Use an invertible ringed suffix; the native tensorators need not be inverted.
  dsimp only
  let R := (finiteInput A gU j' j g sq).R
  let S := restrictRing .ordinary j R
  let F := ProEtale.upperStar (ModuleCat.{u + 1} A) j
  let L := restrict .ordinary j R
  let : L.Additive := (restriction_exact .ordinary j R).1
  let EX := e.realizeX.equivalence.functor
  let EU := e.realizeU.equivalence.functor
  let xc := finiteComplexRealization e.realizeX
  let uc := finiteComplexRealization e.realizeU
  let fc := F.mapHomologicalComplex (.up ℤ)
  let lc := L.mapHomologicalComplex (.up ℤ)
  let v := NatTrans.mapHomologicalComplex e.open_pin.star.hom (.up ℤ)
  let vi := NatIso.mapHomologicalComplex e.open_pin.star (.up ℤ)
  have hpL := o.tensorComparison.preserves (xc.obj P) hp
  have hqL := o.tensorComparison.preserves (xc.obj Q) hq
  have hpU : resolving S (uc.obj (fc.obj P)) :=
    resolving_of_iso S (vi.app P) hpL
  have hqU : resolving S (uc.obj (fc.obj Q)) :=
    resolving_of_iso S (vi.app Q) hqL
  have hx := eq_of_heq (e.tensorX_pin.model P Q hp hq)
  have hu := eq_of_heq (e.tensorU_pin.model (fc.obj P) (fc.obj Q) hpU hqU)
  have hr := e.open_pin.models.2
  have hrep := o.tensorComparison.representative (xc.obj P) (xc.obj Q) hp hq
  have hm' := mixed_representation_finite A j P Q
  let r := Functor.isoWhiskerRight F.leftDerivedFunctorIsoMapDerivedCategory.symm
    e.realizeU.derived ≪≫ e.openPull
  let x := EX.mapDerivedCategoryFactors.hom
  let y := EU.mapDerivedCategoryFactors.hom
  let a := F.mapDerivedCategoryFactors.hom
  let b := L.mapDerivedCategoryFactors.hom
  let tx := o.tensorX.representative.app (⟨xc.obj P, hp⟩, ⟨xc.obj Q, hq⟩)
  let tu := o.tensorU.representative.app
    (⟨uc.obj (fc.obj P), hpU⟩, ⟨uc.obj (fc.obj Q), hqU⟩)
  let tl := o.tensorU.representative.app
    (⟨lc.obj (xc.obj P), hpL⟩, ⟨lc.obj (xc.obj Q), hqL⟩)
  let w := totalMap o.tensorX o.tensorU L o.restrictionTensor o.tensorComparison.comm
    (xc.obj P) (xc.obj Q)
  let k := o.opens.jStar.map
      (o.tensorX.functor.map (Prod.mkHom (x.app P) (x.app Q)) ≫ tx.inv) ≫
    b.app ((total R).obj (xc.obj P, xc.obj Q))
  let ki := o.opens.jStar.mapIso
      (o.tensorX.functor.mapIso
        (Iso.prod (EX.mapDerivedCategoryFactors.app P) (EX.mapDerivedCategoryFactors.app Q)) ≪≫
          tx.symm) ≪≫ L.mapDerivedCategoryFactors.app ((total R).obj (xc.obj P, xc.obj Q))
  have hk : IsIso k := by
    change IsIso ki.hom
    infer_instance
  have hc :
      o.tensorComparison.comparison.inv.app
          (DerivedCategory.Q.obj (xc.obj P), DerivedCategory.Q.obj (xc.obj Q)) ≫
        o.opens.jStar.map tx.inv ≫ b.app ((total R).obj (xc.obj P, xc.obj Q)) =
      o.tensorU.functor.map (Prod.mkHom (b.app (xc.obj P)) (b.app (xc.obj Q))) ≫
        tl.inv ≫ DerivedCategory.Q.map w := by
    change o.opens.jStar.map tx.hom ≫
      o.tensorComparison.comparison.hom.app
          (DerivedCategory.Q.obj (xc.obj P), DerivedCategory.Q.obj (xc.obj Q)) ≫
        o.tensorU.functor.map (Prod.mkHom (b.app (xc.obj P)) (b.app (xc.obj Q))) ≫
        tl.inv ≫ DerivedCategory.Q.map w =
      b.app ((total R).obj (xc.obj P, xc.obj Q)) at hrep
    apply (cancel_epi (o.tensorComparison.comparison.hom.app
      (DerivedCategory.Q.obj (xc.obj P), DerivedCategory.Q.obj (xc.obj Q)))).1
    apply (cancel_epi (o.opens.jStar.map tx.hom)).1
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact hrep.symm
  have hv :
      tu.hom ≫ o.tensorU.functor.map
          (Prod.mkHom (DerivedCategory.Q.map (v.app P)) (DerivedCategory.Q.map (v.app Q))) ≫
        tl.inv =
      DerivedCategory.Q.map ((total S).map (Prod.mkHom (v.app P) (v.app Q))) := by
    have hv := o.tensorU.representative.hom.naturality
      (Prod.mkHom
        (show (⟨uc.obj (fc.obj P), hpU⟩ : (resolving S).FullSubcategory) ⟶
          ⟨lc.obj (xc.obj P), hpL⟩ from ObjectProperty.homMk (v.app P))
        (show (⟨uc.obj (fc.obj Q), hqU⟩ : (resolving S).FullSubcategory) ⟶
          ⟨lc.obj (xc.obj Q), hqL⟩ from ObjectProperty.homMk (v.app Q)))
    change DerivedCategory.Q.map ((total S).map (Prod.mkHom (v.app P) (v.app Q))) ≫
        tl.hom = tu.hom ≫ o.tensorU.functor.map
          (Prod.mkHom (DerivedCategory.Q.map (v.app P)) (DerivedCategory.Q.map (v.app Q))) at hv
    apply (cancel_mono tl.hom).1
    simp only [Category.assoc]
    erw [tl.inv_hom_id, Category.comp_id]
    exact hv.symm
  have hx' :
      e.tensorX.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          o.tensorX.functor.map (Prod.mkHom (x.app P) (x.app Q)) ≫ tx.inv =
        e.realizeX.derived.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          x.app (finiteTotal A X P Q) ≫
          DerivedCategory.Q.map (e.tensorX_pin.totalIso P Q).hom := by
    change e.realizeX.derived.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      x.app (finiteTotal A X P Q) ≫
        DerivedCategory.Q.map (e.tensorX_pin.totalIso P Q).hom ≫ tx.hom =
      e.tensorX.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        o.tensorX.functor.map (Prod.mkHom (x.app P) (x.app Q)) at hx
    rw [← Category.assoc, ← hx]
    simp only [Category.assoc]
    erw [tx.hom_inv_id, Category.comp_id]
  have hu' :
      e.tensorU.hom.app (DerivedCategory.Q.obj (fc.obj P),
          DerivedCategory.Q.obj (fc.obj Q)) ≫
        o.tensorU.functor.map (Prod.mkHom (y.app (fc.obj P)) (y.app (fc.obj Q))) =
      e.realizeU.derived.map
          (Functor.LaxMonoidal.μ DerivedCategory.Q (fc.obj P) (fc.obj Q)) ≫
        y.app (finiteTotal A U (fc.obj P) (fc.obj Q)) ≫
        DerivedCategory.Q.map (e.tensorU_pin.totalIso (fc.obj P) (fc.obj Q)).hom ≫
        tu.hom := hu.symm
  let muX := Functor.LaxMonoidal.μ (DerivedCategory.Q (C := FiniteModules A X)) P Q
  let muU := Functor.LaxMonoidal.μ (DerivedCategory.Q (C := FiniteModules A U))
    (fc.obj P) (fc.obj Q)
  let c := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q
  let delta := ((ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso
    (ModuleCat.{u + 1} A) j).hom.app (DerivedCategory.Q.obj P)).app
      (DerivedCategory.Q.obj Q)
  let n := a.app P ⊗ₘ (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app
    (DerivedCategory.Q.obj Q) ≫ a.app Q)
  have hr' (H : CochainComplex (FiniteModules A X) ℤ) :
      r.hom.app (DerivedCategory.Q.obj H) ≫ o.opens.jStar.map (x.app H) ≫
          b.app (xc.obj H) =
        e.realizeU.derived.map (a.app H) ≫ y.app (fc.obj H) ≫
          DerivedCategory.Q.map (v.app H) := hr H
  have hl :
      e.realizeU.derived.map delta ≫
        r.hom.app ((finiteTensor A X).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
        o.opens.jStar.map
          (e.tensorX.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫ k =
      e.realizeU.derived.map (n ≫ muU) ≫
        y.app (finiteTotal A U (fc.obj P) (fc.obj Q)) ≫
        DerivedCategory.Q.map
          (uc.map (inv c) ≫ v.app (finiteTotal A X P Q) ≫
            lc.map (e.tensorX_pin.totalIso P Q).hom) := by
    calc
      _ = e.realizeU.derived.map delta ≫
          r.hom.app ((finiteTensor A X).obj
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
          o.opens.jStar.map
            (e.tensorX.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              o.tensorX.functor.map (Prod.mkHom (x.app P) (x.app Q)) ≫ tx.inv) ≫
          b.app ((total R).obj (xc.obj P, xc.obj Q)) := by
        simp only [k, Functor.map_comp, Category.assoc]
      _ = e.realizeU.derived.map delta ≫
          r.hom.app ((finiteTensor A X).obj
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
          o.opens.jStar.map (e.realizeX.derived.map muX ≫
            x.app (finiteTotal A X P Q) ≫
              DerivedCategory.Q.map (e.tensorX_pin.totalIso P Q).hom) ≫
          b.app ((total R).obj (xc.obj P, xc.obj Q)) := by rw [hx']
      _ = e.realizeU.derived.map
          (delta ≫ F.mapDerivedCategory.map muX ≫ a.app (finiteTotal A X P Q)) ≫
          y.app (fc.obj (finiteTotal A X P Q)) ≫
          DerivedCategory.Q.map (v.app (finiteTotal A X P Q) ≫
            lc.map (e.tensorX_pin.totalIso P Q).hom) := by
        simp only [Functor.map_comp, Category.assoc]
        erw [b.naturality (e.tensorX_pin.totalIso P Q).hom]
        erw [← reassoc_of% (r.hom.naturality muX)]
        erw [reassoc_of% (hr' (finiteTotal A X P Q))]
        rfl
      _ = _ := by
        dsimp only at hm'
        erw [hm']
        simp only [Functor.map_comp, Category.assoc]
        erw [reassoc_of% (y.naturality (inv c))]
        rfl
  have hrhs :
      e.tensorU.hom.app ((finitePull A j).obj (DerivedCategory.Q.obj P),
          F.leftDerivedFunctor.obj (DerivedCategory.Q.obj Q)) ≫
        o.tensorU.functor.map
          (Prod.mkHom (r.hom.app (DerivedCategory.Q.obj P))
            (e.openPull.hom.app (DerivedCategory.Q.obj Q))) ≫
        o.tensorComparison.comparison.inv.app
          (e.realizeX.derived.obj (DerivedCategory.Q.obj P),
            e.realizeX.derived.obj (DerivedCategory.Q.obj Q)) ≫ k =
      e.realizeU.derived.map (n ≫ muU) ≫
        y.app (finiteTotal A U (fc.obj P) (fc.obj Q)) ≫
        DerivedCategory.Q.map
          ((e.tensorU_pin.totalIso (fc.obj P) (fc.obj Q)).hom ≫
            (total S).map (Prod.mkHom (v.app P) (v.app Q)) ≫ w) := by
    simp only [k, Functor.map_comp, Category.assoc]
    erw [← reassoc_of% (o.tensorComparison.comparison.inv.naturality
      (Prod.mkHom (x.app P) (x.app Q)))]
    erw [hc]
    have hq' :
        e.openPull.hom.app (DerivedCategory.Q.obj Q) ≫ o.opens.jStar.map (x.app Q) ≫
            b.app (xc.obj Q) =
          e.realizeU.derived.map
              (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj Q) ≫
                a.app Q) ≫ y.app (fc.obj Q) ≫ DerivedCategory.Q.map (v.app Q) := by
      have he : e.openPull.hom.app (DerivedCategory.Q.obj Q) =
          e.realizeU.derived.map
              (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj Q)) ≫
            r.hom.app (DerivedCategory.Q.obj Q) := by
        simp [r, ← Functor.map_comp_assoc]
      erw [he]
      simp only [Functor.map_comp, Category.assoc]
      erw [hr' Q]
    have hpair :
        Prod.mkHom (r.hom.app (DerivedCategory.Q.obj P))
            (e.openPull.hom.app (DerivedCategory.Q.obj Q)) ≫
          Prod.mkHom (o.opens.jStar.map (x.app P)) (o.opens.jStar.map (x.app Q)) ≫
          Prod.mkHom (b.app (xc.obj P)) (b.app (xc.obj Q)) =
        Prod.mkHom (e.realizeU.derived.map (a.app P))
            (e.realizeU.derived.map
              (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj Q) ≫
                a.app Q)) ≫
          Prod.mkHom (y.app (fc.obj P)) (y.app (fc.obj Q)) ≫
          Prod.mkHom (DerivedCategory.Q.map (v.app P)) (DerivedCategory.Q.map (v.app Q)) := by
      apply Prod.ext
      · exact hr' P
      · exact hq'
    have hn :
        e.tensorU.hom.app ((finitePull A j).obj (DerivedCategory.Q.obj P),
            F.leftDerivedFunctor.obj (DerivedCategory.Q.obj Q)) ≫
          o.tensorU.functor.map
            (Prod.mkHom (e.realizeU.derived.map (a.app P))
              (e.realizeU.derived.map
                (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj Q) ≫
                  a.app Q))) =
        e.realizeU.derived.map n ≫ e.tensorU.hom.app
          (DerivedCategory.Q.obj (fc.obj P), DerivedCategory.Q.obj (fc.obj Q)) := by
      exact (e.tensorU.hom.naturality
        (Prod.mkHom (a.app P)
          (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj Q) ≫
            a.app Q))).symm
    simp only [← o.tensorU.functor.map_comp_assoc]
    erw [hpair]
    simp only [o.tensorU.functor.map_comp, Category.assoc]
    erw [reassoc_of% hn, reassoc_of% hu', reassoc_of% hv]
  apply (cancel_mono k).1
  have htotal := congrArg
    (fun z ↦ e.realizeU.derived.map (n ≫ muU) ≫
      y.app (finiteTotal A U (fc.obj P) (fc.obj Q)) ≫ DerivedCategory.Q.map z)
    (h_total P Q)
  simpa only [Category.assoc] using hl.trans (htotal.trans hrhs.symm)

end SheafOfModules.OpenTensorNormalization
