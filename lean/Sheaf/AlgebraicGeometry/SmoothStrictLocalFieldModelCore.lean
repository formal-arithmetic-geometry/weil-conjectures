/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension

import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationRegular
import WeilConjectures.RingTheory.StrictHenselizationDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.PointCount
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization

import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale
import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale

/-! # The geometric core of a smooth strict localization

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc/thm-sc-affine-torsion-cd,
local calculation in dimension d; Stacks Tags 04HX, 04GP, 06LN, 06LK and 04GG.
(blueprint: lem-sc-smooth-strict-local-field-model-core)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 800000 in
-- The nested small-model, affine-chart, and triple diagrams require extra elaboration.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine-chart presentation with its point prime and structural map.
Source: Stacks Tag 04HX and the localized-triples lemma. The canonical affine
colimit is compared with the triples colimit; its leg equations preserve the
structural map, so the localized-triples theorem applies to the stated ring. -/
private theorem smooth_chart_local_presentation
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (R : CommRingCat.{u}) (i : Spec R ⟶ S) [IsOpenImmersion i]
    (xR : Spec (.of Ω) ⟶ Spec R) :
    let q := (SpecToEquivOfField Ω (Spec R) xR).1.asIdeal
    ∃ (K : Type u) (_ : Field K)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) K)
      (_ : IsScalarTower (Localization.AtPrime q)
        (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) (strictHenselizationRing (xR ≫ i)))
      (b : R ⟶ strictHenselizationRing (xR ≫ i)),
      Spec.map b ≫ i = strictHenselizationStructuralMap (xR ≫ i) ∧
      (∀ r : R, algebraMap (Localization.AtPrime q) (strictHenselizationRing (xR ≫ i))
        (algebraMap R (Localization.AtPrime q) r) = b.hom r) ∧
      Algebra.IsStrictHenselization (Localization.AtPrime q) K
        (strictHenselizationRing (xR ≫ i)) := open CategoryTheory.Limits Opposite in by
  classical
  let s := xR ≫ i
  let p := (SpecToEquivOfField Ω (Spec R) xR).1
  let F := (Spec R).residueField p
  let e := (SpecToEquivOfField Ω (Spec R) xR).2
  let : Algebra F Ω := e.hom.toAlgebra
  let K := separableClosure F Ω
  obtain ⟨_, _, _, _, E, δ, hδ, cn, cu, ct, ⟨hcn⟩, ⟨_⟩, ⟨hct⟩, r, t, _, ht⟩ :=
    etale_local_ring_triples S Ω R i xR
  let c := ct
  have hc : IsColimit c := hct
  let χ := CommRingCat.ofHom (algebraMap ((Spec R).residueField p) K)
  let t₀ : EtaleResidueTriples R p K χ :=
    ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩
  let ρ := c.ι.app t₀
  have hρ (t : EtaleResidueTriples R p K χ) : t.α ≫ c.ι.app t = ρ := by
    let g : t₀ ⟶ t := InducedCategory.homMk
      (Under.homMk (Over.homMk t.α (by
        change t.α ≫ (ΓSpecIso t.B).inv ≫ (Spec t.B).Γevaluation t.q ≫ t.φ =
          (ΓSpecIso R).inv ≫ (Spec R).Γevaluation p ≫ χ
        exact t.compatible)) (by
        apply Over.OverMorphism.ext
        simp [t₀, EtaleResidueTriple.factorization]))
    exact c.w g
  let Nall := (pointSmallEtale s).fiber.Elements
  let P : ObjectProperty Nall := fun n ↦ IsAffine n.1.left
  let D := (P.ι ⋙ CategoryOfElements.π (pointSmallEtale s).fiber ⋙
    Etale.forget S ⋙ Over.forget S).op ⋙ Scheme.Γ
  let : HasColimit D := ⟨⟨cn, hcn⟩⟩
  let incl := strictHenselizationAffineInclusion s
  let : incl.IsEquivalence := strictHenselizationAffineInclusion_isEquivalence s
  let rep := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse
  let q := (rep ⋙ incl).op
  let cmp : strictHenselizationRing s ≅ cn.pt :=
    Functor.Final.colimitIso q D ≪≫ colimit.isoColimitCocone ⟨cn, hcn⟩
  let k := hct.coconePointUniqueUpToIso hc
  let ringIso : strictHenselizationRing s ≅ c.pt := cmp ≪≫ t ≪≫ k
  have hstruct : Spec.map (ρ ≫ ringIso.inv) ≫ i =
      strictHenselizationStructuralMap s := by
    let a := AffineEtale.mk i
    let y : (pointSmallEtale s).fiber.obj ((AffineEtale.Spec S).obj a) :=
      Over.homMk xR rfl
    let n := (AffineEtale.Spec S ⋙ (pointSmallEtale s).fiber).elementsMk a y
    let j := rep.objPreimage n
    let η := rep.objObjPreimageIso n
    let g : ((incl.obj (rep.obj j)).obj.1.left) ⟶ Spec R :=
      (AffineEtale.Spec S).map η.hom.1 |>.1.left
    have hg : g ≫ i = (incl.obj (rep.obj j)).obj.1.hom := η.hom.1.w
    let b := incl.obj (rep.obj j)
    let Q : ObjectProperty P.FullSubcategory := fun z ↦
      ∃ g : z.obj.1.left ⟶ Spec R, g ≫ i = z.obj.1.hom
    let d : Q.FullSubcategory := ⟨b, ⟨g, hg⟩⟩
    have hcmp : (colimit.cocone (strictHenselizationAffineDiagram s)).ι.app (op j) ≫ cmp.hom =
        cn.ι.app (op b) := by
      change colimit.ι (q ⋙ D) (op j) ≫
        ((Functor.Final.colimitIso q D).hom ≫
          (colimit.isoColimitCocone ⟨cn, hcn⟩).hom) = _
      rw [← Category.assoc, Functor.Final.ι_colimitIso_hom]
      exact colimit.isoColimitCocone_ι_hom ⟨cn, hcn⟩ (op b)
    have htrip := (hδ d).1 g hg
    have hbase : (ΓSpecIso R).inv ≫ g.appTop ≫ δ.hom.app (op d) ≫
        c.ι.app (E.functor.obj (op d)) = ρ := by
      simpa only [Category.assoc] using
        (congrArg (fun f ↦ f ≫ c.ι.app (E.functor.obj (op d))) htrip).trans (hρ _)
    have hleg : cn.ι.app (op b) ≫ t.hom ≫ k.hom =
        δ.hom.app (op d) ≫ c.ι.app (E.functor.obj (op d)) := by
      calc
        _ = (δ.hom.app (op d) ≫ ct.ι.app (E.functor.obj (op d))) ≫ k.hom :=
          congrArg (fun f ↦ f ≫ k.hom) (ht (op d))
        _ = _ := by
          simp only [Category.assoc, k, IsColimit.comp_coconePointUniqueUpToIso_hom]
    have hring : (ΓSpecIso R).inv ≫ g.appTop ≫
        (colimit.cocone (strictHenselizationAffineDiagram s)).ι.app (op j) = ρ ≫ ringIso.inv := by
      apply (cancel_mono ringIso.hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      change (ΓSpecIso R).inv ≫ g.appTop ≫
        (colimit.cocone (strictHenselizationAffineDiagram s)).ι.app (op j) ≫
        cmp.hom ≫ t.hom ≫ k.hom = ρ
      rw [← Category.assoc _ cmp.hom, hcmp, hleg]
      exact hbase
    let : IsAffine b.obj.1.left := b.property
    have hgSpec : Spec.map g.appTop ≫ Spec.map (ΓSpecIso R).inv =
        Spec.map (ΓSpecIso (rep.obj j).1.left.unop).inv ≫ g := by
      have hh := isoSpec_inv_naturality g
      change Spec.map g.appTop ≫ (Spec R).isoSpec.inv =
        (Spec (rep.obj j).1.left.unop).isoSpec.inv ≫ g at hh
      simpa only [isoSpec_Spec_inv] using hh
    have hstr := strictHenselizationStructuralMap_eq s j
    change Spec.map ((colimit.cocone (strictHenselizationAffineDiagram s)).ι.app (op j)) ≫
      Spec.map (ΓSpecIso (rep.obj j).1.left.unop).inv ≫ b.obj.1.hom =
      strictHenselizationStructuralMap s at hstr
    calc
      Spec.map (ρ ≫ ringIso.inv) ≫ i =
          Spec.map ((colimit.cocone (strictHenselizationAffineDiagram s)).ι.app (op j)) ≫
            Spec.map g.appTop ≫ Spec.map (ΓSpecIso R).inv ≫ i := by
        simpa only [Spec.map_comp, Category.assoc] using
          congrArg (fun f ↦ Spec.map f ≫ i) hring.symm
      _ = Spec.map ((colimit.cocone (strictHenselizationAffineDiagram s)).ι.app (op j)) ≫
          Spec.map (ΓSpecIso (rep.obj j).1.left.unop).inv ≫ b.obj.1.hom := by
        rw [← Category.assoc (Spec.map g.appTop), hgSpec, Category.assoc, hg]
      _ = _ := hstr
  obtain ⟨L, hL, ares, hsep, aL, htower, aH, hbase, hH⟩ :=
    etaleResidueTriples_localized_isStrictHenselization R p K c hc
      (strictHenselizationRing s) ringIso.symm (ρ ≫ ringIso.inv) (by
        intro t
        rw [← Category.assoc, hρ t]
        rfl)
  exact ⟨L, hL, ares, hsep, aL, htower, aH,
    ρ ≫ ringIso.inv, hstruct, hbase, hH⟩


/-- Regularity and dimension part of the smooth strict-local model.
Source: blueprint local calculation in dimension d; this is the regularity and
dimension subargument of `lem-sc-smooth-strict-local-field-model-core`.
(blueprint: lem-sc-smooth-strict-local-field-model-core) -/
private theorem smooth_strict_local_core_regular_dimension
    (K : Type u) [Field K] [IsAlgClosed K] (Y : Scheme.{u}) [IsIntegral Y]
    (f : Y ⟶ Spec (.of K)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d a : ℕ) (hd : topologicalKrullDim Y = (d : WithBot ℕ∞))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (y : Y) (hy : s (IsLocalRing.closedPoint Ω) = y)
    [Algebra K (Y.residueField y)]
    (hκ : Spec.map (CommRingCat.ofHom (algebraMap K (Y.residueField y))) =
      Y.fromSpecResidueField y ≫ f)
    [Algebra (Y.residueField y) Ω]
    (_hΩ : Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
      Y.fromSpecResidueField y = s)
    (ha : Algebra.trdeg K (Y.residueField y) = (a : Cardinal))
    [Algebra K (strictHenselizationRing s)]
    (_hK : Spec.map (CommRingCat.ofHom (algebraMap K (strictHenselizationRing s))) =
      strictHenselizationStructuralMap s ≫ f) :
    IsRegularLocalRing (strictHenselizationRing s) ∧
    ∃ hlocal : IsLocalRing (strictHenselizationRing s),
      ∃ hdomain : IsDomain (strictHenselizationRing s),
        let := hlocal
        let := hdomain
        ringKrullDim (strictHenselizationRing s) = ((d - a : ℕ) : WithBot ℕ∞) := by
  classical
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : Y.Opens) from trivial)
  let R := Γ(Y, U)
  let j := hU.fromSpec
  have hsj : Set.range s ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    rw [hz, hy]
    exact hU.range_fromSpec.symm ▸ hyU
  let xR := IsOpenImmersion.lift j s hsj
  have hxR : xR ≫ j = s := IsOpenImmersion.lift_fac j s hsj
  have hp : (SpecToEquivOfField Ω (Spec R) xR).1 = hU.primeIdealOf ⟨y, hyU⟩ := by
    apply j.isOpenEmbedding.injective
    change j (xR (IsLocalRing.closedPoint Ω)) = _
    rw [← Scheme.Hom.comp_apply, hxR, hy]
    exact (hU.fromSpec_primeIdealOf ⟨y, hyU⟩).symm
  have hpres := smooth_chart_local_presentation R j xR
  dsimp only at hpres
  rw [hxR, hp] at hpres
  obtain ⟨L, hL, ares, hsep, aL, htower, aH, b, hb, hbase, hH⟩ := hpres
  let := hL
  let := ares
  let := hsep
  let := aL
  let := htower
  let := aH
  let p := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal
  let B := Localization.AtPrime p
  let : Algebra R (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hyU⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) p := hU.isLocalization_stalk ⟨y, hyU⟩
  let e : B ≃+* Y.presheaf.stalk y :=
    (IsLocalization.algEquiv p.primeCompl B (Y.presheaf.stalk y)).toRingEquiv
  have hregY : IsRegularLocalRing (Y.presheaf.stalk y) :=
    Smooth.isRegularLocalRing_stalk f y
  have hregB : IsRegularLocalRing B := .of_ringEquiv e.symm
  have hreg : IsRegularLocalRing (strictHenselizationRing s) :=
    (Algebra.isRegularLocalRing_iff_strictHenselization B L _ hH).mp hregB
  have hdomain : IsDomain (strictHenselizationRing s) := inferInstance
  refine ⟨hreg, inferInstance, hdomain, ?_⟩
  have hdim := Algebra.ringKrullDim_eq_of_isStrictHenselization B L _ hH
  rw [← hdim, e.ringKrullDim]
  let : Y.Over (Spec (.of K)) := ⟨f⟩
  let : LocallyOfFiniteType (Y ↘ Spec (.of K)) := ‹LocallyOfFiniteType f›
  let : QuasiCompact (Y ↘ Spec (.of K)) := ‹QuasiCompact f›
  have hcan : f.residueFieldAlgebraMap y = algebraMap K (Y.residueField y) := by
    have hc : CommRingCat.ofHom (f.residueFieldAlgebraMap y) =
        CommRingCat.ofHom (algebraMap K (Y.residueField y)) := by
      apply Spec.map_injective
      rw [f.specMap_residueFieldAlgebraMap, hκ]
    exact congrArg CommRingCat.Hom.hom hc
  have htr : @Algebra.trdeg K (Y.residueField y) _ _
      (f.residueFieldAlgebraMap y).toAlgebra = (a : Cardinal) := by
    rw [hcan]
    exact ha
  have hformula := topologicalKrullDimAt_eq_stalk_dimension_add_residue_trdeg
    (K := K) Y y
  have hpoint : topologicalKrullDimAt y = (d : WithBot ℕ∞) := by
    rw [← hd]
    apply topologicalKrullDimAt_eq_of_forall
    intro V hyV
    have : Nonempty V := ⟨⟨y, hyV⟩⟩
    exact topologicalKrullDim_opens_eq f V
  rw [hpoint, htr, Cardinal.toENat_nat] at hformula
  have hfinite := IsRegularLocalRing.spanFinrank_maximalIdeal (R := Y.presheaf.stalk y)
  rw [← hfinite] at hformula ⊢
  have hn : (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).spanFinrank + a = d := by
    exact_mod_cast hformula.symm
  exact_mod_cast (Nat.eq_sub_of_add_eq hn)


/-- Residue-field part of the smooth strict-local model.
Source: blueprint local calculation in dimension d; this is the residue-field
subargument of `lem-sc-smooth-strict-local-field-model-core`.
(blueprint: lem-sc-smooth-strict-local-field-model-core) -/
private theorem smooth_strict_local_core_residue
    (K : Type u) [Field K] [IsAlgClosed K] (Y : Scheme.{u}) [IsIntegral Y]
    (f : Y ⟶ Spec (.of K)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d a : ℕ) (_hd : topologicalKrullDim Y = (d : WithBot ℕ∞))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (y : Y) (hy : s (IsLocalRing.closedPoint Ω) = y)
    [Algebra K (Y.residueField y)]
    (hκ : Spec.map (CommRingCat.ofHom (algebraMap K (Y.residueField y))) =
      Y.fromSpecResidueField y ≫ f)
    [Algebra (Y.residueField y) Ω]
    (hΩ : Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
      Y.fromSpecResidueField y = s)
    (ha : Algebra.trdeg K (Y.residueField y) = (a : Cardinal))
    [Algebra K (strictHenselizationRing s)]
    (_hK : Spec.map (CommRingCat.ofHom (algebraMap K (strictHenselizationRing s))) =
      strictHenselizationStructuralMap s ≫ f)
    [IsLocalRing (strictHenselizationRing s)] [IsDomain (strictHenselizationRing s)] :
    ∃ e : IsLocalRing.ResidueField (strictHenselizationRing s) ≃+*
        separableClosure (Y.residueField y) Ω,
      Spec.map (CommRingCat.ofHom
        ((separableClosure (Y.residueField y) Ω).subtype.comp
          (e.toRingHom.comp (IsLocalRing.residue (strictHenselizationRing s))))) ≫
        strictHenselizationStructuralMap s = s := by
  classical
  subst y
  have hmap : Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω)) =
      Spec.map (CommRingCat.ofHom
        (Y.descResidueField (Scheme.stalkClosedPointTo s)).hom) := by
    apply (cancel_mono (Y.fromSpecResidueField (s (IsLocalRing.closedPoint Ω)))).1
    rw [CommRingCat.ofHom_hom, hΩ]
    exact (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω Y s).symm
  have hdesc : algebraMap (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω =
      (Y.descResidueField (Scheme.stalkClosedPointTo s)).hom := by
    have hc := (Functor.map_injective Scheme.Spec hmap)
    exact congrArg (fun g ↦ g.unop.hom) hc
  obtain ⟨_, _, _, hsep, ⟨e, heuniq⟩⟩ :=
    AlgebraicGeometry.strictHenselizationResidue s hdesc
  have hv : (separableClosure (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω).subtype =
      (separableClosure (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω).val.toRingHom := by
    ext x
    rfl
  refine ⟨e, ?_⟩
  rw [hv]
  simpa only [RingHom.comp_assoc] using heuniq.1.2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Function-field part of the smooth strict-local model.
Source: blueprint local calculation in dimension d; this is the function-field
subargument of `lem-sc-smooth-strict-local-field-model-core`.
(blueprint: lem-sc-smooth-strict-local-field-model-core) -/
private theorem smooth_strict_local_core_function
    (K : Type u) [Field K] [IsAlgClosed K] (Y : Scheme.{u}) [IsIntegral Y]
    (f : Y ⟶ Spec (.of K)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d a : ℕ) (_hd : topologicalKrullDim Y = (d : WithBot ℕ∞))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (y : Y) (hy : s (IsLocalRing.closedPoint Ω) = y)
    [Algebra K (Y.residueField y)]
    (_hκ : Spec.map (CommRingCat.ofHom (algebraMap K (Y.residueField y))) =
      Y.fromSpecResidueField y ≫ f)
    [Algebra (Y.residueField y) Ω]
    (_hΩ : Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
      Y.fromSpecResidueField y = s)
    (_ha : Algebra.trdeg K (Y.residueField y) = (a : Cardinal))
    [Algebra K (strictHenselizationRing s)]
    (_hK : Spec.map (CommRingCat.ofHom (algebraMap K (strictHenselizationRing s))) =
      strictHenselizationStructuralMap s ≫ f)
    [IsLocalRing (strictHenselizationRing s)] [IsDomain (strictHenselizationRing s)] :
    ∃ i : Y.functionField →+* FractionRing (strictHenselizationRing s),
      Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk (genericPoint Y) =
        Spec.map (CommRingCat.ofHom
          (algebraMap (strictHenselizationRing s)
            (FractionRing (strictHenselizationRing s)))) ≫
          strictHenselizationStructuralMap s ∧
      (letI := i.toAlgebra
       Algebra.IsAlgebraic Y.functionField (FractionRing (strictHenselizationRing s))) := by
  classical
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : Y.Opens) from trivial)
  let : Nonempty U := ⟨⟨y, hyU⟩⟩
  let R := Γ(Y, U)
  let H := strictHenselizationRing s
  let Q := FractionRing H
  let j := hU.fromSpec
  have hsj : Set.range s ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    rw [hz, hy]
    exact hU.range_fromSpec.symm ▸ hyU
  let xR := IsOpenImmersion.lift j s hsj
  have hxR : xR ≫ j = s := IsOpenImmersion.lift_fac j s hsj
  have hpres := smooth_chart_local_presentation R j xR
  dsimp only at hpres
  rw [hxR] at hpres
  obtain ⟨_, _, _, _, _, _, _, b, hb, _, _⟩ := hpres
  let : Algebra R H := b.hom.toAlgebra
  have hind : Algebra.IndEtale R H :=
    smallStrictHenselization_indEtale_of_affine_chart s R j
      (hsj (Set.mem_range_self (IsLocalRing.closedPoint Ω))) (Iso.refl _) b.hom (by
        change Spec.map b ≫ j = 𝟙 _ ≫ strictHenselizationStructuralMap s
        simpa only [Category.id_comp] using hb)
  have : Module.Flat R H := inferInstance
  have hbinj : Function.Injective b.hom := FaithfulSMul.algebraMap_injective R H
  let g : R →+* Q := (algebraMap H Q).comp b.hom
  have hginj : Function.Injective g := (IsFractionRing.injective H Q).comp hbinj
  have : IsFractionRing R Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  let i : Y.functionField →+* Q := IsFractionRing.lift hginj
  have hi (r : R) : i (algebraMap R Y.functionField r) = g r :=
    IsFractionRing.lift_algebraMap hginj r
  refine ⟨i, ?_, ?_⟩
  · have hgeneric : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫ j =
        Y.fromSpecStalk (genericPoint Y) :=
      hU.fromSpecStalk_eq_fromSpecStalk _
    rw [← hgeneric, ← Category.assoc, ← Spec.map_comp]
    have hm : CommRingCat.ofHom (algebraMap R Y.functionField) ≫
        CommRingCat.ofHom i = b ≫ CommRingCat.ofHom (algebraMap H Q) := by
      ext r
      exact hi r
    rw [hm, Spec.map_comp, Category.assoc, hb]
  · let : Algebra Y.functionField Q := i.toAlgebra
    have : IsScalarTower R Y.functionField Q := IsScalarTower.of_algebraMap_eq'
      (by ext r; exact (hi r).symm)
    let φ : H →ₐ[R] Q :=
      { algebraMap H Q with commutes' := fun r ↦ rfl }
    have hint (r : H) : _root_.IsIntegral Y.functionField (algebraMap H Q r) :=
      (Algebra.IndEtale.isSeparable_of_algHom_to_isLocalRing Y.functionField Q φ r).isIntegral
    refine ⟨fun z ↦ ?_⟩
    obtain ⟨r, t, _, hrt⟩ := IsFractionRing.div_surjective H z
    rw [← hrt, div_eq_mul_inv]
    exact ((hint r).mul (hint t).inv).isAlgebraic


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Regularity, dimension, residue and function field of a smooth strict localization.
Source: blueprint thm-sc-affine-torsion-cd, local calculation in dimension d;
Stacks Tags 04HX, 04GW, 04GP, 00TT, 06LN, 00NP, 0A21 and 06LK.
(blueprint: lem-sc-smooth-strict-local-field-model-core)

Proof: choose a smooth affine chart U = Spec A at y and let p be its prime at y.
The stalk is B = A_p, and A is a domain since Y is integral. Restrict the affine
pointed-etale neighbourhoods to those lying over U: every neighbourhood has such
an affine refinement, so this restriction is cofinal. Their residue fields are
finite separable over kappa(y); hence the specified maps into Omega land in
l = separableClosure (Y.residueField y) Omega. The chart/residue-triples comparison
identifies the coordinate-ring colimit R with the triples colimit. The localized
triples theorem equips this same ring with its B-algebra strict henselization
structure, preserving its structural map. For the residue field, hOmega and hy
identify the prescribed embedding with descResidueField(stalkClosedPointTo s):
cancel the monomorphism fromSpecResidueField and use faithfulness of Spec.
The existing strictHenselizationResidue theorem then supplies the residue-field
isomorphism and exactly the required pointed structural factorization.

Smoothness makes B regular local and Noetherian. Strict henselization preserves
regularity, and a regular local ring is a domain. The affine-chart ind-etale theorem
makes R flat over the domain A. Since R is nontrivial, this makes A -> R injective.
Thus A -> R -> Q = Frac(R) embeds Frac(A) in Q.
Identify Frac(A) with Y.functionField using the generic stalk of the integral
scheme. On the affine chart both structural composites are induced by the same
A-map; the localization universal property and the open immersion give the
stated equality of morphisms from Spec Q to Y.

Every nonempty open of the integral locally algebraic Y has dimension d, so
its dimension at y is d. The finite-type point dimension formula gives
 dim B + trdeg_K kappa(y) = d. With ha this implies a <= d and dim B = d-a.
Strict henselization preserves this local dimension, proving the dimension of R.
The equation hKappa (hκ in Lean) identifies the given K-algebra on kappa(y)
with the canonical residue-field algebra by full faithfulness of Spec, as needed
by the dimension formula. The dimension and function-field conclusions do not
need the supplied K-algebra structure on R.

Finally the affine-chart ind-etale theorem gives an ind-etale A-algebra R.
The source-library theorem
`Algebra.IndEtale.isSeparable_of_algHom_to_isLocalRing`, applied to R -> Q
with fraction field Y.functionField of A, makes each image of an element of R
separable and hence integral over Y.functionField. Every element of Q is a
quotient of two such images. Integral elements over a field are closed under
products and inverses, so this quotient is algebraic, with the algebra structure
specified by the structural embedding i. -/
theorem smooth_strict_local_field_model_core
    (K : Type u) [Field K] [IsAlgClosed K] (Y : Scheme.{u}) [IsIntegral Y]
    (f : Y ⟶ Spec (.of K)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d a : ℕ) (hd : topologicalKrullDim Y = (d : WithBot ℕ∞))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    (y : Y) (hy : s (IsLocalRing.closedPoint Ω) = y)
    [Algebra K (Y.residueField y)]
    (hκ : Spec.map (CommRingCat.ofHom (algebraMap K (Y.residueField y))) =
      Y.fromSpecResidueField y ≫ f)
    [Algebra (Y.residueField y) Ω]
    (hΩ : Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
      Y.fromSpecResidueField y = s)
    (ha : Algebra.trdeg K (Y.residueField y) = (a : Cardinal))
    [Algebra K (strictHenselizationRing s)]
    (hK : Spec.map (CommRingCat.ofHom (algebraMap K (strictHenselizationRing s))) =
      strictHenselizationStructuralMap s ≫ f) :
    IsRegularLocalRing (strictHenselizationRing s) ∧
    ∃ hlocal : IsLocalRing (strictHenselizationRing s),
      ∃ hdomain : IsDomain (strictHenselizationRing s),
        letI := hlocal
        letI := hdomain
        ringKrullDim (strictHenselizationRing s) = ((d - a : ℕ) : WithBot ℕ∞) ∧
        ∃ e : IsLocalRing.ResidueField (strictHenselizationRing s) ≃+*
            separableClosure (Y.residueField y) Ω,
          Spec.map (CommRingCat.ofHom
            ((separableClosure (Y.residueField y) Ω).subtype.comp
              (e.toRingHom.comp (IsLocalRing.residue (strictHenselizationRing s))))) ≫
            strictHenselizationStructuralMap s = s ∧
          ∃ i : Y.functionField →+* FractionRing (strictHenselizationRing s),
            Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk (genericPoint Y) =
              Spec.map (CommRingCat.ofHom
                (algebraMap (strictHenselizationRing s)
                  (FractionRing (strictHenselizationRing s)))) ≫
                strictHenselizationStructuralMap s ∧
            (letI := i.toAlgebra
             Algebra.IsAlgebraic Y.functionField (FractionRing (strictHenselizationRing s))) := by
  obtain ⟨hreg, hlocal, hdomain, hdim⟩ :=
    smooth_strict_local_core_regular_dimension K Y f d a hd Ω s y hy hκ hΩ ha hK
  let := hlocal
  let := hdomain
  obtain ⟨he, hres⟩ := smooth_strict_local_core_residue K Y f d a hd Ω s y hy hκ hΩ ha hK
  obtain ⟨i, hi, halg⟩ := smooth_strict_local_core_function K Y f d a hd Ω s y hy hκ hΩ ha hK
  exact ⟨hreg, hlocal, hdomain, hdim, he, hres, i, hi, halg⟩

end Scheme
end AlgebraicGeometry
