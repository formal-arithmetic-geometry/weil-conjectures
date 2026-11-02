/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin
import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothProQuotientTransport
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCompactQuotientCocycle
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import all WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingCompactSupportIdentity

/-! # Coherence of normalized finite-stage comparisons

Source: current blueprint reduction-exceptional and field-extension towers,
parent node proof step 7 (projection cocycle and mate pasting).
(blueprint: lem-pur-finite-stage-normalized-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints
attribute [local irreducible] etaleUpper etaleAdjunction ProEtale.pbcFixedScalarExtension
  ProEtale.pbcFixedScalarExtensionComp ProEtale.normalizedOriginScalarUnit
  ProEtale.compactSupportSiteComparison ProEtale.derivedComparisonAdjunction

private def coherenceOrigin (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K : (ctf A T).FullSubcategory) :
    Scheme.FixedEtaleOriginWitness T A ⟨K.obj, K.property.plus⟩ where
  complex := ⟨(rnu A T).obj K.obj,
    ProEtale.plus_rightDerivedFunctor_comparisonLowerStar_obj K.property.plus⟩
  iso :=
    have := (ProEtale.DerivedCategory.plusEtaleOrigin_iff K.obj).mp
      K.property.plusEtaleOrigin |>.2
    asIso ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.app K.obj)

private def originFunctor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    (ctf A T).FullSubcategory ⥤
      DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) where
  obj K := (coherenceOrigin A T K).complex
  map a := ObjectProperty.homMk ((rnu A T).map a.hom)

private def originRealization (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    originFunctor A T ⋙ DerivedCategory.Plus.ι ⋙ nu A T ≅ (ctf A T).ι :=
  NatIso.ofComponents (fun K ↦ (coherenceOrigin A T K).iso) (fun a ↦ by
    exact (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) T).counit.naturality
      a.hom)

private def etaleRefinement (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d) :
    DerivedCategory.Plus.ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      DerivedCategory.Plus.ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d :=
  (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).symm
      DerivedCategory.Plus.ι ≪≫
    Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) d

private def lowerRealization (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (ctf A X).ι ⋙ lower A c ≅ originFunctor A X ⋙ DerivedCategory.Plus.ι ⋙
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙ nu A Y :=
  Functor.isoWhiskerRight (originRealization A X).symm (lower A c) ≪≫
    Functor.isoWhiskerLeft (originFunctor A X) (ProEtale.compactSupportSiteComparison A c)

private def lowerRefinementIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d) :
    (ctf A X).ι ⋙ lower A c ≅ (ctf A X).ι ⋙ lower A d :=
  lowerRealization A c ≪≫
    Functor.isoWhiskerLeft (originFunctor A X)
      (Functor.isoWhiskerRight (etaleRefinement A r) (nu A Y)) ≪≫
    (lowerRealization A d).symm

private theorem lowerRefinement_normalization
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (K : (ctf A X).FullSubcategory)
    (w : Scheme.FixedEtaleOriginWitness X A ⟨K.obj, K.property.plus⟩) :
    (lowerRefinementIso A r).hom.app K = refinementAtWitness r K w := by
  with_unfolding_all
    let e := (coherenceOrigin A X K).iso
    obtain ⟨a, ha⟩ := (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
      w.complex.obj (coherenceOrigin A X K).complex.obj
      (coherenceOrigin A X K).complex.property).surjective (w.iso.hom ≫ e.inv)
    let t := (ProEtale.compactSupportSiteComparison A c) ≪≫
      Functor.isoWhiskerRight (etaleRefinement A r) (nu A Y) ≪≫
      (ProEtale.compactSupportSiteComparison A d).symm
    have hn := t.hom.naturality (ObjectProperty.homMk a)
    change (lower A c).map ((nu A X).map a) ≫ t.hom.app (coherenceOrigin A X K).complex =
      t.hom.app w.complex ≫ (lower A d).map ((nu A X).map a) at hn
    change (nu A X).map a = w.iso.hom ≫ e.inv at ha
    erw [ha] at hn
    have hw : refinementAtWitness r K w =
        (lower A c).map w.iso.inv ≫ t.hom.app w.complex ≫
          (lower A d).map w.iso.hom := by
      simp only [refinementAtWitness, t, etaleRefinement, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
        Functor.map_comp, Category.assoc]
    erw [hw]
    apply (cancel_epi ((lower A c).map w.iso.hom)).1
    have hcan : (lowerRefinementIso A r).hom.app K =
        (lower A c).map e.inv ≫ t.hom.app (coherenceOrigin A X K).complex ≫
          (lower A d).map e.hom := by
      simp only [lowerRefinementIso, lowerRealization, originRealization, e, t,
        Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents_hom_app,
        NatIso.ofComponents_inv_app, originFunctor, Category.assoc]
    rw [hcan]
    calc
      _ = ((lower A c).map (w.iso.hom ≫ e.inv) ≫
          t.hom.app (coherenceOrigin A X K).complex) ≫
          (lower A d).map e.hom := by simp only [Functor.map_comp, Category.assoc]
      _ = (t.hom.app w.complex ≫ (lower A d).map (w.iso.hom ≫ e.inv)) ≫
          (lower A d).map e.hom := by erw [hn]
      _ = t.hom.app w.complex ≫ (lower A d).map w.iso.hom := by
        erw [Category.assoc, ← (lower A d).map_comp]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      _ = _ := by
        simp only [← (lower A c).map_comp_assoc, Iso.hom_inv_id,
          CategoryTheory.Functor.map_id, Category.id_comp]

private theorem counit_injective
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} (d : AdjointDatum A c)
    (K : (ctf A X).FullSubcategory) (L : (ctf A Y).FullSubcategory)
    (a b : K.obj ⟶ (upper A c).obj L.obj)
    (h : (lower A c).map a ≫ d.counit L = (lower A c).map b ≫ d.counit L) :
    a = b := by
  with_unfolding_all
    have h' : (d.adjunction.homEquiv K L).symm (ObjectProperty.homMk a) =
        (d.adjunction.homEquiv K L).symm (ObjectProperty.homMk b) := by
      apply ObjectProperty.hom_ext
      exact h
    exact congrArg InducedCategory.Hom.hom ((d.adjunction.homEquiv K L).symm.injective h')

private def lowerRefinementRestricted
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (dc : AdjointDatum A c) (dd : AdjointDatum A d) :
    restrict (lower A c) dc.lower_preserves ≅ restrict (lower A d) dd.lower_preserves :=
  NatIso.ofComponents (fun K ↦ (ctf A Y).isoMk ((lowerRefinementIso A r).app K))
    (fun a ↦ by
      apply ObjectProperty.hom_ext
      exact (lowerRefinementIso A r).hom.naturality a)

private def canonicalRefinement
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (dc : AdjointDatum A c) (dd : AdjointDatum A d) : RefinementDatum r dc dd where
  lowerIso := lowerRefinementIso A r
  upperIso := Functor.isoWhiskerRight
    (conjugateIsoEquiv dd.adjunction dc.adjunction (lowerRefinementRestricted r dc dd))
    (ctf A X).ι
  lower_normalization := lowerRefinement_normalization r
  upper_normalization K := by
    with_unfolding_all
      exact congrArg InducedCategory.Hom.hom
        (conjugateEquiv_counit dd.adjunction dc.adjunction
          (lowerRefinementRestricted r dc dd).hom K)

private theorem refinement_unique
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} {r : c.Refinement d}
    {dc : AdjointDatum A c} {dd : AdjointDatum A d}
    (a b : RefinementDatum r dc dd) : a = b := by
  with_unfolding_all
    have hl : a.lowerIso = b.lowerIso := by
      apply Iso.ext
      ext K
      exact (a.lower_normalization K (coherenceOrigin A X K)).trans
        (b.lower_normalization K (coherenceOrigin A X K)).symm
    have hu : a.upperIso = b.upperIso := by
      apply Iso.ext
      ext K
      apply counit_injective dc
        ⟨(upper A d).obj K.obj, dd.upper_preserves K.obj K.property⟩ K
      erw [a.upper_normalization, b.upper_normalization, hl]
    cases a
    cases b
    cases hl
    cases hu
    rfl

private theorem projection_transport
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f}
    (dA : AdjointDatum A c) (dB : AdjointDatum B c)
    (φ : A →+* B) (q : Change φ c dA dB)
    (K : (ctf A X).FullSubcategory) :
    q.projection.hom.app K =
      (tensor φ Y).map ((lowerRealization A c).hom.app K) ≫
        Etale.FiniteSmoothPurity.transportedCoefficient φ X Y
          (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
          (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c)
          (Etale.ExceptionalCoefficients.compactSupportMap φ c) K.obj ≫
        (lowerRealization B c).inv.app
          ⟨(tensor φ X).obj K.obj, q.tensor_preserves_X K.obj K.property⟩ := by
  with_unfolding_all
    let KB : (ctf B X).FullSubcategory :=
      ⟨(tensor φ X).obj K.obj, q.tensor_preserves_X K.obj K.property⟩
    let w := coherenceOrigin A X K
    let wB := coherenceOrigin B X KB
    let θ := Etale.FiniteSmoothPurity.originReductionMap φ X K.obj
    let LB : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
      ⟨(Etale.scalarExtension φ X).obj w.complex.obj, q.etale_tensor_bound K w⟩
    have hn := (ProEtale.compactSupportSiteComparison B c).inv.naturality
      (ObjectProperty.homMk θ : LB ⟶ wB.complex)
    change (nu B Y).map
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map θ) ≫
        (ProEtale.compactSupportSiteComparison B c).inv.app wB.complex =
      (ProEtale.compactSupportSiteComparison B c).inv.app LB ≫
        (lower B c).map ((nu B X).map θ) at hn
    have hc := Etale.FiniteSmoothPurity.originReductionCounit φ X K.obj
    change (nu B X).map θ ≫ wB.iso.hom =
      (ProEtale.pbcComparisonReduction X φ).inv.app w.complex.obj ≫
        (tensor φ X).map w.iso.hom at hc
    have hA : (lowerRealization A c).hom.app K =
        (lower A c).map w.iso.inv ≫
          (ProEtale.compactSupportSiteComparison A c).hom.app w.complex := rfl
    have hB : (lowerRealization B c).inv.app KB =
        (ProEtale.compactSupportSiteComparison B c).inv.app wB.complex ≫
          (lower B c).map wB.iso.hom := rfl
    rw [q.projection_normalization K w, hA, hB]
    simp only [Etale.FiniteSmoothPurity.transportedCoefficient, Functor.map_comp,
      Category.assoc]
    erw [reassoc_of% hn, ← (lower B c).map_comp, hc, Functor.map_comp]
    simp only [projectionAtWitness, Etale.ExceptionalCoefficients.compactSupportMap,
      Functor.map_comp, Category.assoc]
    rfl

private theorem projection_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f}
    (dA : AdjointDatum A c) (dB : AdjointDatum B c) (dC : AdjointDatum C c)
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (qab : Change φ c dA dB) (qbc : Change ψ c dB dC) (qac : Change χ c dA dC)
    (K : (ctf A X).FullSubcategory) :
    (tensor ψ Y).map (qab.projection.hom.app K) ≫
        qbc.projection.hom.app
          ⟨(tensor φ X).obj K.obj, qab.tensor_preserves_X K.obj K.property⟩ ≫
        (lower C c).map ((ProEtale.pbcFixedScalarExtensionComp
          (Scheme.ProEt.topology X) φ ψ χ hχ).hom.app K.obj) =
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y) φ ψ χ hχ).hom.app
        ((lower A c).obj K.obj) ≫ qac.projection.hom.app K := by
  with_unfolding_all
    let FA := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let FB := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
    let FC := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c
    let KB : (ctf B X).FullSubcategory :=
      ⟨(tensor φ X).obj K.obj, qab.tensor_preserves_X K.obj K.property⟩
    let KBC : (ctf C X).FullSubcategory :=
      ⟨(tensor ψ X).obj KB.obj, qbc.tensor_preserves_X KB.obj KB.property⟩
    let KC : (ctf C X).FullSubcategory :=
      ⟨(tensor χ X).obj K.obj, qac.tensor_preserves_X K.obj K.property⟩
    let αX := ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X) φ ψ χ hχ
    let αY := ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y) φ ψ χ hχ
    have ho := Etale.FiniteSmoothPurity.originTransport_cocycle
      (rnu A X) (rnu B X) (rnu C X) (nu A Y) (nu B Y) (nu C Y)
      (Etale.scalarExtension φ X) (Etale.scalarExtension ψ X) (Etale.scalarExtension χ X)
      (Etale.scalarExtension φ Y) (Etale.scalarExtension ψ Y) (Etale.scalarExtension χ Y)
      (tensor φ X) (tensor ψ X) (tensor χ X)
      (tensor φ Y) (tensor ψ Y) (tensor χ Y)
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ hχ)
      (ProEtale.pbcFixedScalarExtensionComp Y.smallEtaleTopology φ ψ χ hχ)
      αX αY FA FB FC
      (ProEtale.pbcComparisonReduction Y φ) (ProEtale.pbcComparisonReduction Y ψ)
      (ProEtale.pbcComparisonReduction Y χ)
      (Etale.FiniteSmoothPurity.originReductionMap φ X)
      (Etale.FiniteSmoothPurity.originReductionMap ψ X)
      (Etale.FiniteSmoothPurity.originReductionMap χ X)
      (Etale.ExceptionalCoefficients.compactSupportMap φ c)
      (Etale.ExceptionalCoefficients.compactSupportMap ψ c)
      (Etale.ExceptionalCoefficients.compactSupportMap χ c)
      (fun {J L} v ↦ Etale.compactScalarMap_naturality ψ c v)
      (Etale.FiniteSmoothPurity.siteScalarComp Y φ ψ χ hχ) K.obj
      (Etale.FiniteSmoothPurity.originReductionComp X φ ψ χ hχ K.obj)
      (Etale.FiniteSmoothPurity.compact_chain φ ψ χ hχ c ((rnu A X).obj K.obj)).symm
    have he := (lowerRealization C c).inv.naturality
      (ObjectProperty.homMk (αX.hom.app K.obj) : KBC ⟶ KC)
    change (nu C Y).map (FC.map ((rnu C X).map (αX.hom.app K.obj))) ≫
        (lowerRealization C c).inv.app KC =
      (lowerRealization C c).inv.app KBC ≫
        (lower C c).map (αX.hom.app K.obj) at he
    rw [projection_transport dA dB φ qab K,
      projection_transport dB dC ψ qbc KB, projection_transport dA dC χ qac K]
    exact Etale.FiniteSmoothPurity.conjugateCocycle
      (tensor φ X) (tensor ψ X) (tensor χ X)
      (tensor φ Y) (tensor ψ Y) (tensor χ Y) αX αY
      (rnu A X ⋙ FA ⋙ nu A Y) (lower A c)
      (rnu B X ⋙ FB ⋙ nu B Y) (lower B c)
      (rnu C X ⋙ FC ⋙ nu C Y) (lower C c)
      (Etale.FiniteSmoothPurity.transportedCoefficient φ X Y FA FB
        (Etale.ExceptionalCoefficients.compactSupportMap φ c))
      (Etale.FiniteSmoothPurity.transportedCoefficient ψ X Y FB FC
        (Etale.ExceptionalCoefficients.compactSupportMap ψ c))
      (Etale.FiniteSmoothPurity.transportedCoefficient χ X Y FA FC
        (Etale.ExceptionalCoefficients.compactSupportMap χ c)) K.obj
      ((lowerRealization A c).hom.app K)
      ((lowerRealization B c).inv.app KB) ((lowerRealization B c).hom.app KB)
      ((lowerRealization C c).inv.app KBC) ((lowerRealization C c).inv.app KC)
      ((lowerRealization B c).inv_hom_id_app KB) he.symm ho

private theorem etaleRefinement_eq
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d) :
    etaleRefinement A r = Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      (Etale.rightDerivedLowerShriekOfCompactificationIso A c d) := by
  with_unfolding_all
    apply Iso.ext
    ext K
    have hp := Etale.rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso
      A (Compactification.Refinement.id c) r
    simp only [Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso_id,
      Iso.refl_trans] at hp
    have h := Etale.unboundedEtaleCompactSupport_comparison_plus A f c d K
    rw [hp] at h
    apply (cancel_epi
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).hom.app K)).1
    simpa only [etaleRefinement, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Category.assoc, Iso.hom_inv_id_app_assoc] using h

private theorem projection_refinement
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (Ac : AdjointDatum A c) (Ad : AdjointDatum A d)
    (Bc : AdjointDatum B c) (Bd : AdjointDatum B d)
    (φ : A →+* B) (qc : Change φ c Ac Bc) (qd : Change φ d Ad Bd)
    (K : (ctf A X).FullSubcategory) :
    (tensor φ Y).map ((canonicalRefinement r Ac Ad).lowerIso.hom.app K) ≫
        qd.projection.hom.app K =
      qc.projection.hom.app K ≫ (canonicalRefinement r Bc Bd).lowerIso.hom.app
        ⟨(tensor φ X).obj K.obj, qc.tensor_preserves_X K.obj K.property⟩ := by
  with_unfolding_all
    let KB : (ctf B X).FullSubcategory :=
      ⟨(tensor φ X).obj K.obj, qc.tensor_preserves_X K.obj K.property⟩
    let FA := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let GA := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d
    let FB := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c
    let GB := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d
    let α := Etale.rightDerivedLowerShriekOfCompactificationIso A c d
    let β := Etale.rightDerivedLowerShriekOfCompactificationIso B c d
    let O := (rnu A X).obj K.obj
    let θ := Etale.FiniteSmoothPurity.originReductionMap φ X K.obj
    have hs := (Etale.etaleCompactScalarCoherence φ f c).2.2 d
      (coherenceOrigin A X K).complex
      ⟨⟨(Etale.scalarExtension φ X).obj O,
        qc.etale_tensor_bound K (coherenceOrigin A X K)⟩, rfl⟩
    change (Etale.scalarExtension φ Y).map (α.hom.app O) ≫
        Etale.ExceptionalCoefficients.compactSupportMap φ d O =
      Etale.ExceptionalCoefficients.compactSupportMap φ c O ≫
        β.hom.app ((Etale.scalarExtension φ X).obj O) at hs
    have ht := (ProEtale.pbcComparisonReduction Y φ).hom.naturality (α.hom.app O)
    change (tensor φ Y).map ((nu A Y).map (α.hom.app O)) ≫
        (ProEtale.pbcComparisonReduction Y φ).hom.app (GA.obj O) =
      (ProEtale.pbcComparisonReduction Y φ).hom.app (FA.obj O) ≫
        (nu B Y).map ((Etale.scalarExtension φ Y).map (α.hom.app O)) at ht
    have hb := β.hom.naturality θ
    have hmid :
        (tensor φ Y).map ((nu A Y).map (α.hom.app O)) ≫
          Etale.FiniteSmoothPurity.transportedCoefficient φ X Y GA GB
            (Etale.ExceptionalCoefficients.compactSupportMap φ d) K.obj =
        Etale.FiniteSmoothPurity.transportedCoefficient φ X Y FA FB
            (Etale.ExceptionalCoefficients.compactSupportMap φ c) K.obj ≫
          (nu B Y).map (β.hom.app ((rnu B X).obj KB.obj)) := by
      simp only [Etale.FiniteSmoothPurity.transportedCoefficient, Functor.map_comp,
        Category.assoc]
      erw [reassoc_of% ht, ← (nu B Y).map_comp_assoc, hs, (nu B Y).map_comp]
      simp only [Category.assoc]
      erw [← (nu B Y).map_comp, ← hb, (nu B Y).map_comp]
      simp only [Functor.map_comp, Category.assoc]
      rfl
    rw [projection_transport Ac Bc φ qc K, projection_transport Ad Bd φ qd K]
    change (tensor φ Y).map ((lowerRefinementIso A r).hom.app K) ≫ _ =
      _ ≫ (lowerRefinementIso B r).hom.app KB
    simp only [lowerRefinementIso, etaleRefinement_eq r, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.map_comp, Category.assoc]
    erw [← (tensor φ Y).map_comp_assoc
      ((lowerRealization A d).inv.app K) ((lowerRealization A d).hom.app K),
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    erw [Iso.inv_hom_id_app_assoc]
    simpa only [Category.assoc, FA, FB, GA, GB, α, β, O, originFunctor,
      coherenceOrigin, ObjectProperty.ι_obj] using congrArg
      (fun v ↦ (tensor φ Y).map ((lowerRealization A c).hom.app K) ≫ v ≫
        (lowerRealization B d).inv.app KB) hmid

private theorem projection_identity
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f} (d : AdjointDatum A c)
    (φ : A →+* A) (hφ : φ = RingHom.id A) (q : Change φ c d d)
    (K : (ctf A X).FullSubcategory) :
    q.projection.hom.app K ≫ (lower A c).map
        ((ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology X) φ hφ).hom.app
          K.obj) =
      (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology Y) φ hφ).hom.app
        ((lower A c).obj K.obj) := by
  with_unfolding_all
    subst φ
    let SX := tensor (RingHom.id A) X
    let SY := tensor (RingHom.id A) Y
    let UX := ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology X)
      (RingHom.id A) rfl
    let UY := ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology Y)
      (RingHom.id A) rfl
    let L : (ctf A X).FullSubcategory :=
      ⟨SX.obj K.obj, q.tensor_preserves_X K.obj K.property⟩
    have hx : UX.hom.app (SX.obj K.obj) = SX.map (UX.hom.app K.obj) := by
      apply (cancel_mono (UX.hom.app K.obj)).1
      exact (UX.hom.naturality (UX.hom.app K.obj)).symm
    have hn := q.projection.hom.naturality
      (ObjectProperty.homMk (UX.hom.app K.obj) : L ⟶ K)
    change SY.map ((lower A c).map (UX.hom.app K.obj)) ≫ q.projection.hom.app K =
      q.projection.hom.app L ≫ (lower A c).map (SX.map (UX.hom.app K.obj)) at hn
    have hp := projection_comp d d d (RingHom.id A) (RingHom.id A)
      (RingHom.id A) (by ext; rfl) q q q K
    rw [WeilConjectures.scalar_comp_unit, WeilConjectures.scalar_comp_unit] at hp
    dsimp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.comp_obj,
      Functor.id_obj] at hp
    erw [Category.comp_id, Category.comp_id] at hp
    change SY.map (q.projection.hom.app K) ≫ q.projection.hom.app L ≫
        (lower A c).map (UX.hom.app (SX.obj K.obj)) =
      UY.hom.app (SY.obj ((lower A c).obj K.obj)) ≫ q.projection.hom.app K at hp
    rw [hx, ← hn, ← SY.map_comp_assoc] at hp
    have hc := (cancel_mono (q.projection.hom.app K)).1 hp
    have hu := UY.hom.naturality
      (q.projection.hom.app K ≫ (lower A c).map (UX.hom.app K.obj))
    change SY.map (q.projection.hom.app K ≫ (lower A c).map (UX.hom.app K.obj)) ≫
        UY.hom.app ((lower A c).obj K.obj) =
      UY.hom.app (SY.obj ((lower A c).obj K.obj)) ≫
        (q.projection.hom.app K ≫ (lower A c).map (UX.hom.app K.obj)) at hu
    rw [hc] at hu
    exact ((cancel_epi (UY.hom.app (SY.obj ((lower A c).obj K.obj)))).1 hu).symm

private theorem mate_unit_of_projection
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f}
    (d : AdjointDatum A c) (φ : A →+* A) (hφ : φ = RingHom.id A)
    (q : Change φ c d d)
    (hp : ∀ L : (ctf A X).FullSubcategory,
      q.projection.hom.app L ≫ (lower A c).map
          ((ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology X) φ hφ).hom.app
            L.obj) =
        (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology Y) φ hφ).hom.app
          ((lower A c).obj L.obj))
    (K : (ctf A Y).FullSubcategory) :
    q.mate.hom.app K ≫ (upper A c).map
        ((ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology Y) φ hφ).hom.app
          K.obj) =
      (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology X) φ hφ).hom.app
        ((upper A c).obj K.obj) := by
  with_unfolding_all
    let UX := ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology X) φ hφ
    let UY := ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology Y) φ hφ
    let L : (ctf A X).FullSubcategory :=
      ⟨(upper A c).obj K.obj, d.upper_preserves K.obj K.property⟩
    have hi : q.projection.inv.app L ≫ UY.hom.app ((lower A c).obj L.obj) =
        (lower A c).map (UX.hom.app L.obj) := by
      erw [← hp L, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    apply counit_injective d
      ⟨(tensor φ X).obj L.obj, q.tensor_preserves_X L.obj L.property⟩ K
    simp only [Functor.map_comp, Category.assoc]
    have hn := d.adjunction.counit.naturality
      (ObjectProperty.homMk (UY.hom.app K.obj) :
        ⟨(tensor φ Y).obj K.obj, q.tensor_preserves_Y K.obj K.property⟩ ⟶ K)
    have hn' := congrArg InducedCategory.Hom.hom hn
    change (lower A c).map ((upper A c).map (UY.hom.app K.obj)) ≫ d.counit K =
      d.counit ⟨(tensor φ Y).obj K.obj, q.tensor_preserves_Y K.obj K.property⟩ ≫
        UY.hom.app K.obj at hn'
    erw [hn', reassoc_of% (q.counit_equation K)]
    have hu := UY.hom.naturality (d.counit K)
    change (tensor φ Y).map (d.counit K) ≫ UY.hom.app K.obj =
      UY.hom.app ((lower A c).obj L.obj) ≫ d.counit K at hu
    erw [hu, reassoc_of% hi]
    rfl

private theorem mate_refinement_of_projection
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (Ac : AdjointDatum A c) (Ad : AdjointDatum A d)
    (Bc : AdjointDatum B c) (Bd : AdjointDatum B d)
    (φ : A →+* B) (qc : Change φ c Ac Bc) (qd : Change φ d Ad Bd)
    (ra : RefinementDatum r Ac Ad) (rb : RefinementDatum r Bc Bd)
    (hp : ∀ L : (ctf A X).FullSubcategory,
      (tensor φ Y).map (ra.lowerIso.hom.app L) ≫ qd.projection.hom.app L =
        qc.projection.hom.app L ≫ rb.lowerIso.hom.app
          ⟨(tensor φ X).obj L.obj, qc.tensor_preserves_X L.obj L.property⟩)
    (K : (ctf A Y).FullSubcategory) :
    (tensor φ X).map (ra.upperIso.hom.app K) ≫ qc.mate.hom.app K =
      qd.mate.hom.app K ≫ rb.upperIso.hom.app
        ⟨(tensor φ Y).obj K.obj, qc.tensor_preserves_Y K.obj K.property⟩ := by
  with_unfolding_all
    let L : (ctf A X).FullSubcategory :=
      ⟨(upper A d).obj K.obj, Ad.upper_preserves K.obj K.property⟩
    let M : (ctf A X).FullSubcategory :=
      ⟨(upper A c).obj K.obj, Ac.upper_preserves K.obj K.property⟩
    let N : (ctf B Y).FullSubcategory :=
      ⟨(tensor φ Y).obj K.obj, qc.tensor_preserves_Y K.obj K.property⟩
    have hi : qc.projection.inv.app L ≫ (tensor φ Y).map (ra.lowerIso.hom.app L) =
        rb.lowerIso.hom.app
          ⟨(tensor φ X).obj L.obj, qc.tensor_preserves_X L.obj L.property⟩ ≫
            qd.projection.inv.app L := by
      apply (cancel_mono (qd.projection.hom.app L)).1
      simp only [Category.assoc, Iso.inv_hom_id_app]
      erw [hp L, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
      erw [Category.comp_id]
    apply counit_injective Bc
      ⟨(tensor φ X).obj L.obj, qd.tensor_preserves_X L.obj L.property⟩ N
    simp only [Functor.map_comp, Category.assoc]
    erw [qc.counit_equation, rb.upper_normalization]
    have hq := qc.projection.inv.naturality
      (ObjectProperty.homMk (ra.upperIso.hom.app K) : L ⟶ M)
    dsimp only [Functor.comp_map, ObjectProperty.ι_map] at hq
    erw [reassoc_of% hq, ← (tensor φ Y).map_comp, ra.upper_normalization]
    simp only [Functor.map_comp]
    erw [reassoc_of% hi]
    have hr := rb.lowerIso.hom.naturality
      (ObjectProperty.homMk (qd.mate.hom.app K) :
        ⟨(tensor φ X).obj L.obj, qd.tensor_preserves_X L.obj L.property⟩ ⟶
          ⟨(upper B d).obj N.obj, Bd.upper_preserves N.obj N.property⟩)
    dsimp only [Functor.comp_map, ObjectProperty.ι_map] at hr
    erw [reassoc_of% hr, qd.counit_equation]

private theorem mate_comp_of_projection
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c : Compactification f}
    (dA : AdjointDatum A c) (dB : AdjointDatum B c) (dC : AdjointDatum C c)
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (qab : Change φ c dA dB) (qbc : Change ψ c dB dC) (qac : Change χ c dA dC)
    (hp : ∀ L : (ctf A X).FullSubcategory,
      (tensor ψ Y).map (qab.projection.hom.app L) ≫
        qbc.projection.hom.app
          ⟨(tensor φ X).obj L.obj, qab.tensor_preserves_X L.obj L.property⟩ ≫
        (lower C c).map ((ProEtale.pbcFixedScalarExtensionComp
          (Scheme.ProEt.topology X) φ ψ χ hχ).hom.app L.obj) =
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y) φ ψ χ hχ).hom.app
        ((lower A c).obj L.obj) ≫ qac.projection.hom.app L)
    (K : (ctf A Y).FullSubcategory) :
    (tensor ψ X).map (qab.mate.hom.app K) ≫
        qbc.mate.hom.app
          ⟨(tensor φ Y).obj K.obj, qab.tensor_preserves_Y K.obj K.property⟩ ≫
        (upper C c).map ((ProEtale.pbcFixedScalarExtensionComp
          (Scheme.ProEt.topology Y) φ ψ χ hχ).hom.app K.obj) =
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X) φ ψ χ hχ).hom.app
        ((upper A c).obj K.obj) ≫ qac.mate.hom.app K := by
  with_unfolding_all
    let SX := ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X) φ ψ χ hχ
    let SY := ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y) φ ψ χ hχ
    let L : (ctf A X).FullSubcategory :=
      ⟨(upper A c).obj K.obj, dA.upper_preserves K.obj K.property⟩
    let LB : (ctf B X).FullSubcategory :=
      ⟨(tensor φ X).obj L.obj, qab.tensor_preserves_X L.obj L.property⟩
    let KB : (ctf B Y).FullSubcategory :=
      ⟨(tensor φ Y).obj K.obj, qab.tensor_preserves_Y K.obj K.property⟩
    let LC : (ctf C X).FullSubcategory :=
      ⟨(tensor ψ X).obj LB.obj, qbc.tensor_preserves_X LB.obj LB.property⟩
    let KC : (ctf C Y).FullSubcategory :=
      ⟨(tensor χ Y).obj K.obj, qac.tensor_preserves_Y K.obj K.property⟩
    have hi : qbc.projection.inv.app LB ≫
        (tensor ψ Y).map (qab.projection.inv.app L) ≫
          SY.hom.app ((lower A c).obj L.obj) =
        (lower C c).map (SX.hom.app L.obj) ≫ qac.projection.inv.app L := by
      apply (cancel_mono (qac.projection.hom.app L)).1
      simp only [Category.assoc, Iso.inv_hom_id_app]
      erw [← (hp L)]
      erw [← (tensor ψ Y).map_comp_assoc, Iso.inv_hom_id_app,
        CategoryTheory.Functor.map_id, Category.id_comp]
      erw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp, Category.comp_id]
    apply counit_injective dC LC KC
    simp only [Functor.map_comp, Category.assoc]
    have hn := dC.adjunction.counit.naturality
      (ObjectProperty.homMk (SY.hom.app K.obj) :
        ⟨(tensor ψ Y).obj KB.obj, qbc.tensor_preserves_Y KB.obj KB.property⟩ ⟶ KC)
    have hn' := congrArg InducedCategory.Hom.hom hn
    change (lower C c).map ((upper C c).map (SY.hom.app K.obj)) ≫ dC.counit KC =
      dC.counit ⟨(tensor ψ Y).obj KB.obj,
        qbc.tensor_preserves_Y KB.obj KB.property⟩ ≫ SY.hom.app K.obj at hn'
    erw [hn', reassoc_of% (qbc.counit_equation KB),
      qac.counit_equation K]
    have hq := qbc.projection.inv.naturality
      (ObjectProperty.homMk (qab.mate.hom.app K) : LB ⟶
        ⟨(upper B c).obj KB.obj, dB.upper_preserves KB.obj KB.property⟩)
    change (lower C c).map ((tensor ψ X).map (qab.mate.hom.app K)) ≫
        qbc.projection.inv.app
          ⟨(upper B c).obj KB.obj, dB.upper_preserves KB.obj KB.property⟩ =
      qbc.projection.inv.app LB ≫
        (tensor ψ Y).map ((lower B c).map (qab.mate.hom.app K)) at hq
    erw [reassoc_of% hq, ← (tensor ψ Y).map_comp_assoc, qab.counit_equation]
    simp only [Functor.map_comp, Category.assoc]
    have hs := SY.hom.naturality (dA.counit K)
    change (tensor ψ Y).map ((tensor φ Y).map (dA.counit K)) ≫ SY.hom.app K.obj =
      SY.hom.app ((lower A c).obj L.obj) ≫ (tensor χ Y).map (dA.counit K) at hs
    erw [hs, reassoc_of% hi]
    rfl

/-- Normalized individual adjunctions and coefficient comparisons satisfy composition,
identity, and compactification-refinement coherence.

Source: current blueprint reduction-exceptional and field-extension towers;
parent lem-pur-finite-coefficient-adjoint-comparisons, proof step 7.
(blueprint: lem-pur-finite-stage-normalized-coherence).

Proof: on a retained etale witness expand both coefficient composites using
projection_normalization. Naturality moves the witness isomorphisms through the
functors. The site/coefficient square cancels the middle site comparisons, and the
ringed coefficient projection cocycle identifies both remaining maps with the
extension to the composite coefficient ring of the same evaluation counit.
Open extension gives the same equation termwise by tensor balancing. This proves
projection_comp with the canonical scalar associators; the identity case gives
projection_id with normalizedOriginScalarUnit. Define the refinement lower iso by
transporting the specified ordinary etale proper/open refinement iso through the
site comparison. Naturality shows its value is refinementAtWitness, independently
of the witness. Its right-adjoint conjugate is the unique map with the stated
upper_normalization, hence an iso. The site/coefficient refinement square proves
projection_refinement. For mate_comp transpose the two proposed composites under
the final adjunction: substitute each Change.counit_equation and then use the
projection cocycle; both transposes are the scalar-extended initial counit preceded
by the inverse composite projection. Injectivity gives mate_comp. The same
argument with the scalar unit proves mate_id, and with the lower refinement
square proves mate_refinement. Normalized projection and conjugate counit fix both
refinement isomorphisms uniquely; proof irrelevance fixes their proof fields.
No compatibility hypotheses on the input families are required, since every
Change and AdjointDatum already carries the specified normalization. -/
theorem finite_stage_normalized_coherence
    (k : Type u) [Field k] (p l : ℕ) [CharP k p] (hp : 0 < p)
    [Fact l.Prime] (hlp : l ≠ p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    letI := finiteTypeNoetherian k X
    letI := finiteTypeNoetherian k Y
    letI := (finiteTypeMorphismProperties k f).1
    letI := (finiteTypeMorphismProperties k f).2.1
    letI := (finiteTypeMorphismProperties k f).2.2
    ∀ (datum : ∀ (s : Stage l E) (c : Compactification f), AdjointDatum s.ring c)
      (change : ∀ {s t : Stage l E} (a : Arrow s t) (c : Compactification f),
    Change a.ringMap c (datum s c) (datum t c)),
      ∃! refinement : ∀ (s : Stage l E) {c d : Compactification f} (r : c.Refinement d),
    RefinementDatum r (datum s c) (datum s d),
        (∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v)
    (ab : Arrow s v) (h : ab.embedding = b.embedding.comp a.embedding)
    (c : Compactification f) (K : (ctf s.ring X).FullSubcategory),
    (tensor b.ringMap Y).map ((change a c).projection.hom.app K) ≫
        (change b c).projection.hom.app
          ⟨(tensor a.ringMap X).obj K.obj,
            (change a c).tensor_preserves_X K.obj K.property⟩ ≫
        (lower v.ring c).map
          ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
            a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app K.obj) =
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
          a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app
            ((lower s.ring c).obj K.obj) ≫
        (change ab c).projection.hom.app K) ∧
        (∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v)
    (ab : Arrow s v) (h : ab.embedding = b.embedding.comp a.embedding)
    (c : Compactification f) (K : (ctf s.ring Y).FullSubcategory),
    (tensor b.ringMap X).map ((change a c).mate.hom.app K) ≫
        (change b c).mate.hom.app
          ⟨(tensor a.ringMap Y).obj K.obj,
            (change a c).tensor_preserves_Y K.obj K.property⟩ ≫
        (upper v.ring c).map
          ((ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology Y)
            a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app K.obj) =
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
          a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)).hom.app
            ((upper s.ring c).obj K.obj) ≫
        (change ab c).mate.hom.app K) ∧
        (∀ (s : Stage l E) (a : Arrow s s)
    (h : a.embedding = AlgHom.id (Padic l) s.field)
    (c : Compactification f) (K : (ctf s.ring X).FullSubcategory),
    (change a c).projection.hom.app K ≫
        (lower s.ring c).map ((ProEtale.normalizedOriginScalarUnit
          (Scheme.ProEt.topology X) a.ringMap (Arrow.ringMap_id a h)).hom.app K.obj) =
      (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology Y)
        a.ringMap (Arrow.ringMap_id a h)).hom.app ((lower s.ring c).obj K.obj)) ∧
        (∀ (s : Stage l E) (a : Arrow s s)
    (h : a.embedding = AlgHom.id (Padic l) s.field)
    (c : Compactification f) (K : (ctf s.ring Y).FullSubcategory),
    (change a c).mate.hom.app K ≫
        (upper s.ring c).map ((ProEtale.normalizedOriginScalarUnit
          (Scheme.ProEt.topology Y) a.ringMap (Arrow.ringMap_id a h)).hom.app K.obj) =
      (ProEtale.normalizedOriginScalarUnit (Scheme.ProEt.topology X)
        a.ringMap (Arrow.ringMap_id a h)).hom.app ((upper s.ring c).obj K.obj)) ∧
        (∀ {s t : Stage l E} (a : Arrow s t)
    {c d : Compactification f} (r : c.Refinement d) (K : (ctf s.ring X).FullSubcategory),
    (tensor a.ringMap Y).map ((refinement s r).lowerIso.hom.app K) ≫
        (change a d).projection.hom.app K =
      (change a c).projection.hom.app K ≫
        (refinement t r).lowerIso.hom.app
          ⟨(tensor a.ringMap X).obj K.obj, (change a c).tensor_preserves_X K.obj K.property⟩) ∧
        (∀ {s t : Stage l E} (a : Arrow s t)
    {c d : Compactification f} (r : c.Refinement d) (K : (ctf s.ring Y).FullSubcategory),
    (tensor a.ringMap X).map ((refinement s r).upperIso.hom.app K) ≫
        (change a c).mate.hom.app K =
      (change a d).mate.hom.app K ≫
        (refinement t r).upperIso.hom.app
          ⟨(tensor a.ringMap Y).obj K.obj,
            (change a c).tensor_preserves_Y K.obj K.property⟩) := by
  classical
  have _ := hp
  have _ := hlp
  let := finiteTypeNoetherian k X
  let := finiteTypeNoetherian k Y
  let := (finiteTypeMorphismProperties k f).1
  let := (finiteTypeMorphismProperties k f).2.1
  let := (finiteTypeMorphismProperties k f).2.2
  intro datum change
  let refinement : ∀ (s : Stage l E) {c d : Compactification f} (r : c.Refinement d),
      RefinementDatum r (datum s c) (datum s d) :=
    fun s _ _ r ↦ canonicalRefinement r (datum s _) (datum s _)
  refine ⟨refinement, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro s t v a b ab h c K
      exact projection_comp (datum s c) (datum t c) (datum v c)
        a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)
        (change a c) (change b c) (change ab c) K
    · intro s t v a b ab h c K
      exact mate_comp_of_projection (datum s c) (datum t c) (datum v c)
        a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)
        (change a c) (change b c) (change ab c)
        (projection_comp (datum s c) (datum t c) (datum v c)
          a.ringMap b.ringMap ab.ringMap (Arrow.ringMap_comp a b ab h)
          (change a c) (change b c) (change ab c)) K
    · intro s a h c K
      exact projection_identity (datum s c) a.ringMap (Arrow.ringMap_id a h) (change a c) K
    · intro s a h c K
      exact mate_unit_of_projection (datum s c) a.ringMap (Arrow.ringMap_id a h) (change a c)
        (projection_identity (datum s c) a.ringMap (Arrow.ringMap_id a h) (change a c)) K
    · intro s t a c d r K
      exact projection_refinement r (datum s c) (datum s d) (datum t c) (datum t d)
        a.ringMap (change a c) (change a d) K
    · intro s t a c d r K
      exact mate_refinement_of_projection r (datum s c) (datum s d)
        (datum t c) (datum t d) a.ringMap (change a c) (change a d)
        (refinement s r) (refinement t r)
        (projection_refinement r (datum s c) (datum s d) (datum t c) (datum t d)
          a.ringMap (change a c) (change a d)) K
  · intro other _
    funext s c d r
    exact refinement_unique (other s r) (refinement s r)

end AlgebraicGeometry.FiniteCoefficientAdjoints
