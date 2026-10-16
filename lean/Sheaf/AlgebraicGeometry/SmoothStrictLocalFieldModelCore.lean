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

import Sheaf.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.Paper.StrictHenselizationFunctoriality
import WeilConjectures.PointCount
import Sheaf.RingTheory.StrictHenselizationTriplesPresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization
import Sheaf.RingTheory.StrictHenselizationRegular
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import Sheaf.RingTheory.StrictHenselizationDimension
import Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale

/-! # The geometric core of a smooth strict localization

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc/thm-sc-affine-torsion-cd,
local calculation in dimension d; Stacks Tags 04HX, 04GP, 06LN, 06LK and 04GG.
(blueprint: lem-sc-smooth-strict-local-field-model-core)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/- The affine-chart presentation with its actual point prime and structural map.
This is the chart argument of `StrictHenselizationLocalPresentation`, specialized
to retain the identified prime. Source: Stacks Tag 04HX and the localized-triples lemma. -/
set_option maxHeartbeats 800000 in
-- The nested small-model, affine-chart, and triple diagrams require extra elaboration.
set_option backward.isDefEq.respectTransparency false in
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
  let eSmall : strictHenselizationRing s ≅ colimit (smallStrictHenselizationDiagram s) :=
    (isColimitSmallStrictHenselizationCocone s).coconePointUniqueUpToIso
      (colimit.isColimit (smallStrictHenselizationDiagram s))
  let cmp : strictHenselizationRing s ≅ cn.pt :=
    eSmall ≪≫ Functor.Final.colimitIso q D ≪≫ colimit.isoColimitCocone ⟨cn, hcn⟩
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
    have hcmp : (smallStrictHenselizationCocone s).ι.app (op j) ≫ cmp.hom =
        cn.ι.app (op b) := by
      change (smallStrictHenselizationCocone s).ι.app (op j) ≫
        (eSmall.hom ≫
        ((Functor.Final.colimitIso q D).hom ≫
          (colimit.isoColimitCocone ⟨cn, hcn⟩).hom)) = _
      rw [← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
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
        (smallStrictHenselizationCocone s).ι.app (op j) = ρ ≫ ringIso.inv := by
      apply (cancel_mono ringIso.hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      change (ΓSpecIso R).inv ≫ g.appTop ≫
        (smallStrictHenselizationCocone s).ι.app (op j) ≫ cmp.hom ≫ t.hom ≫ k.hom = ρ
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
    change Spec.map ((smallStrictHenselizationCocone s).ι.app (op j)) ≫
      Spec.map (ΓSpecIso (rep.obj j).1.left.unop).inv ≫ b.obj.1.hom =
      strictHenselizationStructuralMap s at hstr
    calc
      Spec.map (ρ ≫ ringIso.inv) ≫ i =
          Spec.map ((smallStrictHenselizationCocone s).ι.app (op j)) ≫
            Spec.map g.appTop ≫ Spec.map (ΓSpecIso R).inv ≫ i := by
        simpa only [Spec.map_comp, Category.assoc] using
          congrArg (fun f ↦ Spec.map f ≫ i) hring.symm
      _ = Spec.map ((smallStrictHenselizationCocone s).ι.app (op j)) ≫
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
structure, preserving its structural map. The triples theorem gives a surjection
rho : R -> l with maximal-ideal kernel. It induces the asserted residue-field
isomorphism e. Its equations on every colimit leg, followed by l -> Omega, give
Spec(rho) followed by the structural map equal to s, exactly the displayed
compatibility; hOmega and hy identify the prescribed residue-field embedding.

Smoothness makes B regular local and Noetherian. Strict henselization preserves
regularity, and a regular local ring is a domain. The map B -> R is faithfully
flat, hence injective. Thus A -> B -> R -> Q = Frac(R) embeds Frac(A) in Q.
Identify Frac(A) with Y.functionField using the generic stalk of the integral
scheme. On the affine chart both structural composites are induced by the same
A-map; the localization universal property and the open immersion give the
stated equality of morphisms from Spec Q to Y.

Every nonempty open of the integral locally algebraic Y has dimension d, so
its dimension at y is d. The finite-type point dimension formula gives
 dim B + trdeg_K kappa(y) = d. With ha this implies a <= d and dim B = d-a.
Strict henselization preserves this local dimension, proving the dimension of R.
The algebra structures used in this calculation agree with the given ones:
hK and hKappa (hκ in Lean), together with the structural-map equations, fix them
by full faithfulness of Spec and the monomorphism Spec(kappa(y)) -> Y.

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
             Algebra.IsAlgebraic Y.functionField (FractionRing (strictHenselizationRing s))) :=
  open CategoryTheory.Limits Opposite in by
  classical
  have _ := hK
  subst y
  have hΩ' : algebraMap (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω =
      (Y.descResidueField (stalkClosedPointTo s)).hom := by
    change (CommRingCat.ofHom (algebraMap _ Ω)).hom = _
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecResidueField (s (IsLocalRing.closedPoint Ω)))).1
    exact hΩ.trans
      (Y.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω s).symm
  obtain ⟨hlocal, _, _, _, e, he, _⟩ := strictHenselizationResidue s hΩ'
  let := hlocal
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show s (IsLocalRing.closedPoint Ω) ∈ (⊤ : Y.Opens) from trivial)
  let A := Γ(Y, U)
  let p := hU.primeIdealOf ⟨s (IsLocalRing.closedPoint Ω), hyU⟩
  have hsr : Set.range s ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (IsLocalRing.closedPoint Ω), hU.range_fromSpec]
    exact hyU
  let xU := IsOpenImmersion.lift hU.fromSpec s hsr
  have hxU : xU ≫ hU.fromSpec = s := IsOpenImmersion.lift_fac _ _ _
  have hp : (SpecToEquivOfField Ω (Spec A) xU).1 = p := by
    apply hU.fromSpec.isOpenEmbedding.injective
    change hU.fromSpec (xU (IsLocalRing.closedPoint Ω)) = hU.fromSpec p
    rw [← Scheme.Hom.comp_apply, hxU]
    exact (hU.fromSpec_primeIdealOf ⟨s (IsLocalRing.closedPoint Ω), hyU⟩).symm
  have H := smooth_chart_local_presentation A hU.fromSpec xU
  dsimp only at H
  rw [hxU, hp] at H
  obtain ⟨L, hL, ares, hsep, aL, htower, aR, b, hb, hcomp, hstrict⟩ := H
  let := hL
  let := ares
  let := hsep
  let := aL
  let := htower
  let := aR
  let : Algebra A (Y.presheaf.stalk (s (IsLocalRing.closedPoint Ω))) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨_, hyU⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk (s (IsLocalRing.closedPoint Ω)))
      p.asIdeal := hU.isLocalization_stalk ⟨_, hyU⟩
  let E := IsLocalization.algEquiv p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) (Y.presheaf.stalk (s (IsLocalRing.closedPoint Ω)))
  have : IsRegularLocalRing (Y.presheaf.stalk (s (IsLocalRing.closedPoint Ω))) :=
    Smooth.isRegularLocalRing_stalk f _
  have hB : IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
    .of_ringEquiv E.symm.toRingEquiv
  let := hB
  have hR : IsRegularLocalRing (strictHenselizationRing s) :=
    (Algebra.isRegularLocalRing_iff_strictHenselization _ L _ hstrict).mp hB
  let := hR
  have hdomain : IsDomain (strictHenselizationRing s) := IsRegularLocalRing.isDomain _
  let := hdomain
  refine ⟨hR, hlocal, hdomain, ?_, e, ?_, ?_⟩
  · let : Y.Over (Spec (.of K)) := ⟨f⟩
    have : LocallyOfFiniteType (Y ↘ Spec (.of K)) :=
      show LocallyOfFiniteType f from inferInstance
    have : QuasiCompact (Y ↘ Spec (.of K)) :=
      show QuasiCompact f from inferInstance
    have hcanonical : algebraMap K (Y.residueField (s (IsLocalRing.closedPoint Ω))) =
        f.residueFieldAlgebraMap (s (IsLocalRing.closedPoint Ω)) := by
      change (CommRingCat.ofHom (algebraMap _ _)).hom = _
      apply congrArg CommRingCat.Hom.hom
      apply Spec.map_injective
      exact hκ.trans (f.specMap_residueFieldAlgebraMap _).symm
    have htr : @Algebra.trdeg K (Y.residueField (s (IsLocalRing.closedPoint Ω))) _ _
        (f.residueFieldAlgebraMap _).toAlgebra = (a : Cardinal) := by
      rw [← hcanonical]
      exact ha
    have hpoint : topologicalKrullDimAt (s (IsLocalRing.closedPoint Ω)) =
        topologicalKrullDim Y := by
      apply topologicalKrullDimAt_eq_of_forall
      intro V hyV
      let : Nonempty V := ⟨⟨_, hyV⟩⟩
      exact topologicalKrullDim_opens_eq f V
    have hformula := topologicalKrullDimAt_eq_stalk_dimension_add_residue_trdeg
      (K := K) Y (s (IsLocalRing.closedPoint Ω))
    change topologicalKrullDimAt (s (IsLocalRing.closedPoint Ω)) =
      ringKrullDim (Y.presheaf.stalk (s (IsLocalRing.closedPoint Ω))) +
        (Cardinal.toENat (@Algebra.trdeg K (Y.residueField (s (IsLocalRing.closedPoint Ω)))
          _ _ (f.residueFieldAlgebraMap _).toAlgebra) : WithBot ℕ∞) at hformula
    rw [hpoint, hd, htr, Cardinal.toENat_nat] at hformula
    have hdim := Algebra.ringKrullDim_eq_of_isStrictHenselization _ L _ hstrict
    rw [← hdim, E.toRingEquiv.ringKrullDim]
    have hn : ringKrullDim (Y.presheaf.stalk (s (IsLocalRing.closedPoint Ω))) =
        ((IsLocalRing.maximalIdeal
          (Y.presheaf.stalk (s (IsLocalRing.closedPoint Ω)))).spanFinrank : WithBot ℕ∞) :=
      (IsRegularLocalRing.spanFinrank_maximalIdeal
        (R := Y.presheaf.stalk (s (IsLocalRing.closedPoint Ω)))).symm
    rw [hn] at hformula ⊢
    norm_cast at hformula ⊢
    omega
  · have hv : (separableClosure (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω).subtype =
        (separableClosure (Y.residueField (s (IsLocalRing.closedPoint Ω))) Ω).val.toRingHom := by
      ext x
      rfl
    simpa only [hv, RingHom.comp_assoc] using he.2
  · have : Nonempty U := ⟨⟨_, hyU⟩⟩
    have : IsDomain A := inferInstance
    have hbinj : Function.Injective b.hom := by
      obtain ⟨pB, hpB, aB, hsB, ιB, ⟨hcB⟩, hρB⟩ :=
        hstrict.triples_presentation (Localization.AtPrime p.asIdeal) L
          (strictHenselizationRing s)
      let := aB
      let := hsB
      have hf := strictHenselization_faithfullyFlat
        (.of (Localization.AtPrime p.asIdeal)) pB hpB L (Cocone.mk _ ιB) hcB
        (CommRingCat.ofHom (algebraMap (Localization.AtPrime p.asIdeal)
          (strictHenselizationRing s))) hρB
      have hAinj : Function.Injective (algebraMap A (Localization.AtPrime p.asIdeal)) :=
        IsLocalization.injective _ p.asIdeal.primeCompl_le_nonZeroDivisors
      have hcmp : (algebraMap (Localization.AtPrime p.asIdeal)
          (strictHenselizationRing s)).comp
          (algebraMap A (Localization.AtPrime p.asIdeal)) = b.hom := RingHom.ext hcomp
      rw [← hcmp]
      exact hf.injective.comp hAinj
    let Q := FractionRing (strictHenselizationRing s)
    let φ : A →+* Q := (algebraMap (strictHenselizationRing s) Q).comp b.hom
    have hφ : Function.Injective φ :=
      (IsFractionRing.injective (strictHenselizationRing s) Q).comp hbinj
    have : IsFractionRing A Y.functionField :=
      functionField_isFractionRing_of_isAffineOpen Y U hU
    let i : Y.functionField →+* Q := IsFractionRing.lift hφ
    have hi (x : A) : i (algebraMap A Y.functionField x) = φ x :=
      IsFractionRing.lift_algebraMap hφ x
    refine ⟨i, ?_, ?_⟩
    · have hη : genericPoint Y ∈ U :=
        ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
          (by simpa using (show Nonempty U from inferInstance))
      have hfrom : Spec.map (CommRingCat.ofHom (algebraMap A Y.functionField)) ≫
          hU.fromSpec = Y.fromSpecStalk (genericPoint Y) :=
        hU.fromSpecStalk_eq_fromSpecStalk hη
      rw [← hfrom, ← Category.assoc, ← Spec.map_comp]
      have hring : CommRingCat.ofHom (algebraMap A Y.functionField) ≫
          CommRingCat.ofHom i = CommRingCat.ofHom φ :=
        CommRingCat.hom_ext (RingHom.ext hi)
      rw [hring]
      change Spec.map (b ≫ CommRingCat.ofHom
        (algebraMap (strictHenselizationRing s) Q)) ≫ hU.fromSpec = _
      rw [Spec.map_comp, Category.assoc, hb]
    · let : Algebra A (strictHenselizationRing s) := b.hom.toAlgebra
      have : Algebra.IndEtale A (strictHenselizationRing s) :=
        strictHenselization_indEtale_of_affine_chart s A hU.fromSpec
          (by rw [hU.range_fromSpec]; exact hyU) (Iso.refl _) b.hom
          (by simpa only [CommRingCat.ofHom_hom, Iso.refl_hom, Category.id_comp] using hb)
      let : Algebra Y.functionField Q := i.toAlgebra
      have : IsScalarTower A Y.functionField Q :=
        IsScalarTower.of_algebraMap_eq' (RingHom.ext hi).symm
      have : IsScalarTower A (strictHenselizationRing s) Q := inferInstance
      have key (r : strictHenselizationRing s) :
          IsSeparable Y.functionField (algebraMap (strictHenselizationRing s) Q r) :=
        Algebra.IndEtale.isSeparable_of_algHom_to_isLocalRing Y.functionField Q
          (IsScalarTower.toAlgHom A (strictHenselizationRing s) Q) r
      refine ⟨fun z ↦ ?_⟩
      obtain ⟨r, t, _, rfl⟩ := IsFractionRing.div_surjective (strictHenselizationRing s) z
      simpa only [div_eq_mul_inv] using
        ((key r).isIntegral.mul (key t).isIntegral.inv).isAlgebraic

end Scheme
end AlgebraicGeometry
