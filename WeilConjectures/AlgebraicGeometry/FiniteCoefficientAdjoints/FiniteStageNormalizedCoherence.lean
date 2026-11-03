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

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

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
    have hs := (Etale.compactScalarMap_coherence φ f c).2.2 d
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

end AlgebraicGeometry.FiniteCoefficientAdjoints
