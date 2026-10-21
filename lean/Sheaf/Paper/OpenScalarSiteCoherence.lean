/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.SixFunctors.EtaleOpenTensor
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import Sheaf.Paper.WitnessCompatibility
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.CategoryTheory.RingedSliceExtensionTensor
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Sheaf.CategoryTheory.DerivedExactSquareComposition
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import all Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import all Sheaf.SixFunctors.EtaleOpenTensorDefs
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsPullbackSquare
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import Sheaf.AlgebraicGeometry.EtaleConstantModuleFlat
import Sheaf.Paper.OpenScalarFlatModelRealization
import all Sheaf.Paper.WitnessCompatibility
import all Sheaf.SixFunctors.ComparisonOpenTensorCoherence
import all Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems
import all Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization

/-! # Open extension, scalar extension, and site comparison

Source: Stacks Project, Tags 0GL1, 0E8I, 09AF, 06YQ and 0G7E; the specified
scalar/site square and open composition laws
(blueprint: lem-sp-open-scalar-site-coherence).

## Main declarations

* `scalarOpen`: the canonical pro-etale scalar/open adjunction mate.
* `extension_flat_kflat`: preservation of the required flat models on both sites.
* `scalar_site_square`: the specified B-linear derived square.
* `etale_scalar_comp`, `proetale_scalar_comp`: scalar composition coherence.
* `etale_scalar_id`, `proetale_scalar_id`: scalar identity normalization.
* `site_comp`, `site_id`: derived site composition and identity coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
private theorem uniq_eq_conjugate
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    a.leftAdjointUniq (b.ofNatIsoRight e) = (conjugateIsoEquiv b a).symm e := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]

private theorem exact_identity_square
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : C ⥤ C) (N : C ⥤ D) (P : D ⥤ D)
    [E.Additive] [N.Additive] [P.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (q : E ⋙ N ≅ N ⋙ P) (e : E ≅ 𝟭 C) (p : P ≅ 𝟭 D)
    (hq : ∀ X, q.hom.app X ≫ p.hom.app (N.obj X) = N.map (e.hom.app X))
    (K : DerivedCategory C) :
    (Functor.mapDerivedCategorySquareIso q).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso p ≪≫ Functor.mapDerivedCategoryIdIso D).hom.app
          (N.mapDerivedCategory.obj K) =
      N.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app K) := by
  have heq : q ≪≫ Functor.isoWhiskerLeft N p ≪≫ N.rightUnitor =
      Functor.isoWhiskerRight e N ≪≫ N.leftUnitor := by
    ext X
    simpa using hq X
  have hd := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso z).hom.app K) heq
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at hd
  have hleft := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft N p) K
  have hright := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e N) K
  have hu : (Functor.mapDerivedCategoryNatIso N.rightUnitor).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  have hv : (Functor.mapDerivedCategoryNatIso N.leftUnitor).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  rw [hu, hv] at hd
  simp only [NatTrans.id_app, Category.comp_id] at hd
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso E N).hom.app K)).mp
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  have hp := congr_app (Functor.mapDerivedCategoryCompIso_comp_id N) K
  have he := congr_app (Functor.mapDerivedCategoryCompIso_id_comp N) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app] at hp he
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hleft hright
  calc
    _ = (Functor.mapDerivedCategoryNatIso q).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft N p)).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso N (𝟭 D)).hom.app K ≫
        (Functor.mapDerivedCategoryIdIso D).hom.app (N.mapDerivedCategory.obj K) := by
      rw [reassoc_of% hleft]
    _ = (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight e N)).hom.app K := by
      rw [hp]
      erw [Category.comp_id]
      exact hd
    _ = (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight e N)).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso (𝟭 C) N).hom.app K ≫
        N.mapDerivedCategory.map ((Functor.mapDerivedCategoryIdIso C).hom.app K) := by
      rw [he]
      erw [Category.comp_id]
    _ = _ := by rw [← Category.assoc, hright, Category.assoc]

private theorem scalar_composition
    {A B C D E F : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    {La : A ⥤ D} {Ra : D ⥤ A} {Lb : B ⥤ E} {Rb : E ⥤ B}
    {Lc : C ⥤ F} {Rc : F ⥤ C}
    {H : A ⥤ B} {S : B ⥤ A} {I : B ⥤ C} {T : C ⥤ B}
    {J : A ⥤ C} {U : C ⥤ A}
    {P : D ⥤ E} {Rp : E ⥤ D} {Q : E ⥤ F} {Rq : F ⥤ E}
    {R : D ⥤ F} {Rr : F ⥤ D}
    (a : La ⊣ Ra) (b : Lb ⊣ Rb) (c : Lc ⊣ Rc)
    (h : H ⊣ S) (i : I ⊣ T) (j : J ⊣ U)
    (p : P ⊣ Rp) (q : Q ⊣ Rq) (r : R ⊣ Rr)
    (α01 : Rp ⋙ Ra ≅ Rb ⋙ S) (α12 : Rq ⋙ Rb ≅ Rc ⋙ T)
    (α02 : Rr ⋙ Ra ≅ Rc ⋙ U) (β : U ≅ T ⋙ S) (γ : Rq ⋙ Rp ≅ Rr)
    (μ : J ≅ H ⋙ I) (κ : R ≅ P ⋙ Q)
    (hμ : conjugateIsoEquiv (h.comp i) j μ = β.symm)
    (hκ : conjugateIsoEquiv (p.comp q) r κ = γ)
    (hr : α02 = Functor.isoWhiskerRight γ.symm Ra ≪≫
      Functor.associator Rq Rp Ra ≪≫ Functor.isoWhiskerLeft Rq α01 ≪≫
      (Functor.associator Rq Rb S).symm ≪≫ Functor.isoWhiskerRight α12 S ≪≫
      Functor.associator Rc T S ≪≫ Functor.isoWhiskerLeft Rc β.symm)
    (K : A) :
    Lc.map (μ.hom.app K) ≫
        ((i.comp c).leftAdjointUniq ((b.comp q).ofNatIsoRight α12)).hom.app (H.obj K) ≫
        Q.map (((h.comp b).leftAdjointUniq ((a.comp p).ofNatIsoRight α01)).hom.app K) ≫
        κ.inv.app (La.obj K) =
      ((j.comp c).leftAdjointUniq ((a.comp r).ofNatIsoRight α02)).hom.app K := by
  let t01 := (h.comp b).leftAdjointUniq ((a.comp p).ofNatIsoRight α01)
  let t12 := (i.comp c).leftAdjointUniq ((b.comp q).ofNatIsoRight α12)
  let t02 := (j.comp c).leftAdjointUniq ((a.comp r).ofNatIsoRight α02)
  have he := adjunctionSquareComposition a b c h i j p q r
    α01 α12 α02 β γ t01.symm t12.symm t02.symm μ κ.symm
    (by rw [conjugateIsoEquiv_iso_symm, CategoryTheory.conj_uniq_transport])
    (by rw [conjugateIsoEquiv_iso_symm, CategoryTheory.conj_uniq_transport])
    (by rw [conjugateIsoEquiv_iso_symm, CategoryTheory.conj_uniq_transport]) hμ
    (by rw [conjugateIsoEquiv_iso_symm, hκ]) hr
  have he' := congrArg (fun z ↦ z.inv.app K) he
  simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
    Category.id_comp, Category.comp_id] at he'
  exact CategoryTheory.paste_cancel (Lc.mapIso (μ.app K)) _ _ (κ.app (La.obj K)) _ he'

private theorem scalar_identity
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} {E S : C ⥤ C} {P T : D ⥤ D}
    (a : L ⊣ R) (b : E ⊣ S) (c : P ⊣ T)
    (q : T ⋙ R ≅ R ⋙ S) (s : S ≅ 𝟭 C) (t : T ≅ 𝟭 D)
    (hq : ∀ X, q.hom.app X ≫ s.hom.app (R.obj X) = R.map (t.hom.app X))
    (K : C) :
    ((b.comp a).leftAdjointUniq ((a.comp c).ofNatIsoRight q)).hom.app K ≫
        (Adjunction.leftAdjointIdIso c t).hom.app (L.obj K) =
      L.map ((Adjunction.leftAdjointIdIso b s).hom.app K) := by
  have h := CategoryTheory.identity_square a b c
    ((b.comp a).leftAdjointUniq ((a.comp c).ofNatIsoRight q))
    (Adjunction.leftAdjointIdIso b s) (Adjunction.leftAdjointIdIso c t) q.symm s t
    (by
      rw [conjugateIsoEquiv_iso_symm, CategoryTheory.conj_uniq_transport])
    (Equiv.apply_symm_apply _ _) (Equiv.apply_symm_apply _ _) (by
      apply Iso.ext
      ext X
      simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerLeft_hom, Iso.symm_hom, Iso.symm_inv,
        NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.leftUnitor_inv_app, Functor.rightUnitor_inv_app,
        Category.id_comp]
      apply (cancel_mono (s.hom.app (R.obj X))).mp
      rw [Category.assoc, hq, ← R.map_comp, Iso.inv_hom_id_app, R.map_id,
        Iso.inv_hom_id_app]
      rfl)
  simpa using congrArg (fun z ↦ z.hom.app K) h

private theorem scalar_open_inverse_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) :
    ((mateEquiv a b).symm
      ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv))).natTrans =
      ((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv := by
  rw [uniq_eq_conjugate]
  exact congrArg TwoSquare.natTrans
    (iterated_mateEquiv_conjugateEquiv_symm a b u x (TwoSquare.mk _ _ _ _ q.inv))

private theorem open_mate_cube
    {C D E F Cb Db Eb Fb : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category Cb] [Category Db] [Category Eb] [Category Fb]
    {LA : C ⥤ D} {JA : D ⥤ C} {LA' : E ⥤ F} {JA' : F ⥤ E}
    {LB : Cb ⥤ Db} {JB : Db ⥤ Cb} {LB' : Eb ⥤ Fb} {JB' : Fb ⥤ Eb}
    (a : LA ⊣ JA) (a' : LA' ⊣ JA') (b : LB ⊣ JB) (b' : LB' ⊣ JB')
    {HA : C ⥤ E} {GA : D ⥤ F} {HB : Cb ⥤ Eb} {GB : Db ⥤ Fb}
    {S : C ⥤ Cb} {Q : D ⥤ Db} {S' : E ⥤ Eb} {Q' : F ⥤ Fb}
    (β : LA ⋙ Q ≅ S ⋙ LB) (β' : LA' ⋙ Q' ≅ S' ⋙ LB')
    (dA : HA ⋙ LA' ≅ LA ⋙ GA) (dB : HB ⋙ LB' ≅ LB ⋙ GB)
    (lj : JA ⋙ S ⟶ Q ⋙ JB) (lj' : JA' ⋙ S' ⟶ Q' ⋙ JB')
    (lh : S ⋙ HB ≅ HA ⋙ S') (lg : Q ⋙ GB ≅ GA ⋙ Q')
    (cA : JA ⋙ HA ≅ GA ⋙ JA') (cB : JB ⋙ HB ≅ GB ⋙ JB')
    (hi : ∀ M, b.unit.app (S.obj M) ≫ JB.map (β.inv.app M) =
      S.map (a.unit.app M) ≫ lj.app (LA.obj M))
    (hi' : ∀ M, b'.unit.app (S'.obj M) ≫ JB'.map (β'.inv.app M) =
      S'.map (a'.unit.app M) ≫ lj'.app (LA'.obj M))
    (hdA : ∀ M, a'.unit.app (HA.obj M) ≫ JA'.map (dA.hom.app M) =
      HA.map (a.unit.app M) ≫ cA.hom.app (LA.obj M))
    (hdB : ∀ M, b'.unit.app (HB.obj M) ≫ JB'.map (dB.hom.app M) =
      HB.map (b.unit.app M) ≫ cB.hom.app (LB.obj M))
    (hc : ∀ N, S'.map (cA.hom.app N) ≫ lj'.app (GA.obj N) ≫
        JB'.map (lg.inv.app N) =
      lh.inv.app (JA.obj N) ≫ HB.map (lj.app N) ≫ cB.hom.app (Q.obj N))
    (M : C) :
    LB'.map (lh.inv.app M) ≫ dB.hom.app (S.obj M) ≫ GB.map (β.inv.app M) =
      β'.inv.app (HA.obj M) ≫ Q'.map (dA.hom.app M) ≫ lg.inv.app (LA.obj M) := by
  set_option backward.isDefEq.respectTransparency false in
    apply (b'.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]
    have hn := b'.unit.naturality (lh.inv.app M)
    dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
    rw [← reassoc_of% hn, reassoc_of% hdB]
    have hn := cB.hom.naturality (β.inv.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [← hn, ← HB.map_comp_assoc, hi, HB.map_comp, Category.assoc]
    have hn := lh.inv.naturality (a.unit.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [← reassoc_of% hn]
    rw [reassoc_of% hi']
    have hn := lj'.naturality (dA.hom.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [← reassoc_of% hn, ← S'.map_comp_assoc, hdA, S'.map_comp, Category.assoc]
    rw [hc]


namespace AlgebraicGeometry.ProEtale.OpenScalarSite

private def site_pullback (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    Etale.upperStar (ModuleCat.{u + 1} A) j ⋙
      comparisonUpperStar (ModuleCat.{u + 1} A) U ≅
    comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙ upperStar (ModuleCat.{u + 1} A) j :=
  supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) j


/-- The recorded pro-etale coefficient realization, restricted along its canonical
commutative constant-ring comparison. The finite ring has its discrete topology.
Source: Stacks 00YV, 03CY and 03ER
(blueprint: lem-sp-open-scalar-site-coherence). -/
abbrev proRealization (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  finiteCoefficientRealization X A ⋙
    SheafOfModules.restrictScalars (finiteCoefficientCommRingComparison A X)

/-- The sectionwise coefficient identification for pro-etale open restriction.
Source: Stacks 03EL, 03EK (blueprint: lem-sp-open-scalar-site-coherence). -/
def restrictScalarsIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    upperStar (ModuleCat.{u + 1} B) j ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology U) φ ≅
      Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙
        upperStar (ModuleCat.{u + 1} A) j :=
  Functor.isoWhiskerRight (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j) _ ≪≫
    (show openImmersionRestriction (ModuleCat.{u + 1} B) j ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology U) φ ≅
      Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙
        openImmersionRestriction (ModuleCat.{u + 1} A) j from
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)) ≪≫
    Functor.isoWhiskerLeft _
      (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm

/-- The canonical pro-etale scalar/open comparison. This is the mate of the literal
coefficient/restriction identification under the derived scalar and exact open
adjunctions. Thus it specifies the summand-preserving map, rather than choosing an
arbitrary isomorphism. Source: Stacks 0GL1, 0E8I, 06YY
(blueprint: lem-sp-open-scalar-site-coherence). -/
def scalarOpen {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology X) φ ≅
      pbcFixedScalarExtension (Scheme.ProEt.topology U) φ ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ))).leftAdjointUniq
    (((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U) φ)).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)).ofNatIsoRight
      (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ j)))

/-- Exact descent of the recorded pro-etale extension compositor.
Source: Stacks 03DI, 09AF (blueprint: lem-sp-open-scalar-site-coherence). -/
def extensionComp (A : Type (u + 1)) [CommRing A] {V U X : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion k] [IsOpenImmersion j] :=
  Functor.mapDerivedCategoryNatIso (proEtaleOpenExtensionComp A k j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The pro-etale identity extension identification, normalized by its adjunction.
Source: Stacks 03DI, 09AF (blueprint: lem-sp-open-scalar-site-coherence). -/
def extensionId (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  Functor.mapDerivedCategoryNatIso
    ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X)).leftAdjointUniq
      (Adjunction.id.ofNatIsoRight (upperStarId (ModuleCat.{u + 1} A) X).symm)) ≪≫
    Functor.mapDerivedCategoryIdIso _

private lemma pro_derived_comp_conjugate
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}}
    (j₁ : X ⟶ Y) (j₂ : Y ⟶ Z) [IsOpenImmersion j₁] [IsOpenImmersion j₂] :
    let B := ModuleCat.{u + 1} A
    conjugateEquiv
      ((openImmersionLowerShriekUpperStarAdjunction B j₁
        ).mapDerivedCategoryAdjunction.comp
        (openImmersionLowerShriekUpperStarAdjunction B j₂
          ).mapDerivedCategoryAdjunction)
      (openImmersionLowerShriekUpperStarAdjunction B (j₁ ≫ j₂)
        ).mapDerivedCategoryAdjunction
      (Functor.mapDerivedCategoryTriangleIso
        (proEtaleOpenExtensionComp A j₁ j₂)).hom =
      (Functor.mapDerivedCategoryTriangleIso
        (upperStarComp B j₁ j₂)).inv := by
  let B := ModuleCat.{u + 1} A
  let a := openImmersionLowerShriekUpperStarAdjunction B j₁
  let b := openImmersionLowerShriekUpperStarAdjunction B j₂
  let c := openImmersionLowerShriekUpperStarAdjunction B (j₁ ≫ j₂)
  let e := proEtaleOpenExtensionComp A j₁ j₂
  let r := upperStarComp B j₁ j₂
  have hu (K : Sheaf (Scheme.ProEt.topology X) B) :
      c.unit.app K ≫ (upperStar B (j₁ ≫ j₂)).map (e.hom.app K) =
        (a.comp b).unit.app K ≫ r.inv.app
          (((openImmersionLowerShriek B j₁) ⋙ (openImmersionLowerShriek B j₂)).obj K) := by
    exact Adjunction.unit_leftAdjointUniq_hom_app c ((a.comp b).ofNatIsoRight r.symm) K
  have hd := Etale.exact_adj_conjugate
    (C := Sheaf (Scheme.ProEt.topology X) B) (D := Sheaf (Scheme.ProEt.topology Z) B)
    c (a.comp b) e r.symm hu
  rw [Etale.exact_adj_comp (C := Sheaf (Scheme.ProEt.topology X) B)
    (D := Sheaf (Scheme.ProEt.topology Y) B) (E := Sheaf (Scheme.ProEt.topology Z) B) a b] at hd
  apply conjugateEquiv_eq_of_unit
  intro K
  have hK := congrArg (fun t ↦ t.app K) hd
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Adjunction.comp_unit_app,
    Functor.mapDerivedCategoryNatIso_symm] at hK
  let L₁ := openImmersionLowerShriek B j₁
  let L₂ := openImmersionLowerShriek B j₂
  let R := upperStar B (j₁ ≫ j₂)
  let R₁ := upperStar B j₁
  let R₂ := upperStar B j₂
  have hk := congrArg (fun t ↦ t ≫ R.mapDerivedCategory.map
    ((Functor.mapDerivedCategoryCompIso L₁ L₂).hom.app K)) hK
  simp only [Category.assoc] at hk
  have hn := (Functor.mapDerivedCategoryTriangleIso r).inv.naturality
    ((Functor.mapDerivedCategoryCompIso L₁ L₂).hom.app K)
  simp only [Functor.comp_map] at hn
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_inv,
    NatTrans.comp_app, Category.assoc] at hn
  erw [← hn] at hk
  erw [← (R₂.mapDerivedCategory ⋙ R₁.mapDerivedCategory).map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp] at hk
  simpa only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app, Functor.map_comp, Adjunction.comp_unit_app,
    a, b, c, e, r, L₁, L₂, R, R₁, R₂, Category.assoc] using hk.symm


private theorem pro_restrict_comp {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :
    (Sheaf.restrictScalars (Scheme.ProEt.topology V) φ).map
        ((upperStarComp (ModuleCat.{u + 1} B) k j).hom.app M) ≫
      (restrictScalarsIso φ k).hom.app ((upperStar (ModuleCat.{u + 1} B) j).obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) k).map ((restrictScalarsIso φ j).hom.app M) =
    (restrictScalarsIso φ (k ≫ j)).hom.app M ≫
      (upperStarComp (ModuleCat.{u + 1} A) k j).hom.app
        ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj M) := by
  let RA (T : Scheme.{u}) :
      Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} B) ⥤
        Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) :=
    Sheaf.restrictScalars (Scheme.ProEt.topology T) φ
  let GA := openImmersionRestriction (ModuleCat.{u + 1} A) k
  let a := upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) k
  let aj := upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j
  have hA := congr_app (up_res_comp (ModuleCat.{u + 1} A) k j) ((RA X).obj M)
  have hB := congr_app (up_res_comp (ModuleCat.{u + 1} B) k j) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hA hB
  let z := (upperStar (ModuleCat.{u + 1} A) k).mapIso (aj.app ((RA X).obj M)) ≪≫
    a.app ((openImmersionRestriction (ModuleCat.{u + 1} A) j).obj ((RA X).obj M))
  apply (Iso.cancel_iso_hom_right _ _ z).mp
  dsimp only [z, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  change _ = (restrictScalarsIso φ (k ≫ j)).hom.app M ≫
    (upperStarComp (ModuleCat.{u + 1} A) k j).hom.app ((RA X).obj M) ≫
    (upperStar (ModuleCat.{u + 1} A) k).map
      ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.app
        ((RA X).obj M)) ≫
    (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) k).hom.app
      ((openImmersionRestriction (ModuleCat.{u + 1} A) j).obj ((RA X).obj M))
  rw [hA]
  simp only [restrictScalarsIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatIso.ofComponents_hom_app,
    Iso.refl_hom, Category.id_comp, Iso.symm_hom,
    Category.assoc, a, aj, Functor.map_comp,
    Iso.app_hom, RA, Iso.inv_hom_id_app_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [← (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) k).inv.naturality_assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  erw [Category.comp_id]
  change (Sheaf.restrictScalars (Scheme.ProEt.topology V) φ).map
      ((upperStarComp (ModuleCat.{u + 1} B) k j).hom.app M ≫
        (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) k).hom.app
          ((upperStar (ModuleCat.{u + 1} B) j).obj M)) ≫
    (Sheaf.restrictScalars (Scheme.ProEt.topology V) φ).map
      ((openImmersionRestriction (ModuleCat.{u + 1} B) k).map
        ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j).hom.app M)) = _
  rw [← Functor.map_comp]
  rw [Category.assoc]
  rw [← (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) k).hom.naturality]
  rw [hB]
  rw [Functor.map_comp]
  congr 1

private theorem pro_derived_restrict_comp {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    (hq : ∀ M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B),
      (Sheaf.restrictScalars (Scheme.ProEt.topology V) φ).map
          ((upperStarComp (ModuleCat.{u + 1} B) k j).hom.app M) ≫
        (restrictScalarsIso φ k).hom.app ((upperStar (ModuleCat.{u + 1} B) j).obj M) ≫
        (upperStar (ModuleCat.{u + 1} A) k).map ((restrictScalarsIso φ j).hom.app M) =
      (restrictScalarsIso φ (k ≫ j)).hom.app M ≫
        (upperStarComp (ModuleCat.{u + 1} A) k j).hom.app
          ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj M)) :
    let RA (T : Scheme.{u}) := Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ
    let UB {S T : Scheme.{u}} (f : S ⟶ T) := (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory
    let UA {S T : Scheme.{u}} (f : S ⟶ T) := (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    let β := Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
    let γ := Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} B) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
    Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ (k ≫ j)) =
      Functor.isoWhiskerRight γ (RA V) ≪≫
      Functor.associator (UB j) (UB k) (RA V) ≪≫
      Functor.isoWhiskerLeft (UB j)
        (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ k)) ≪≫
      (Functor.associator (UB j) (RA U) (UA k)).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ j)) (UA k) ≪≫
      Functor.associator (RA X) (UA j) (UA k) ≪≫
      Functor.isoWhiskerLeft (RA X) β.symm := by
  dsimp only
  apply Iso.ext
  ext K
  have hc :
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology V) φ).map
          ((Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} B) k j) ≪≫
            Functor.mapDerivedCategoryCompIso _ _).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ k)).hom.app
          ((upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) k).mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ j)).hom.app K) =
      (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ (k ≫ j))).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).hom.app
            ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj K) := by
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id] using congrArg (fun e ↦ e.hom.app K)
      (Functor.mapDerivedCategorySquareIso_comp
        (C₀ := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
        (C₁ := Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} B))
        (C₂ := Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} B))
        (D₀ := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
        (D₁ := Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A))
        (D₂ := Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A))
        (upperStar (ModuleCat.{u + 1} B) j) (upperStar (ModuleCat.{u + 1} B) k)
        (upperStar (ModuleCat.{u + 1} B) (k ≫ j))
        (upperStar (ModuleCat.{u + 1} A) j) (upperStar (ModuleCat.{u + 1} A) k)
        (upperStar (ModuleCat.{u + 1} A) (k ≫ j))
        (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
        (Sheaf.restrictScalars (Scheme.ProEt.topology U) φ)
        (Sheaf.restrictScalars (Scheme.ProEt.topology V) φ)
        (restrictScalarsIso φ j) (restrictScalarsIso φ k)
        (restrictScalarsIso φ (k ≫ j))
        (upperStarComp (ModuleCat.{u + 1} B) k j)
        (upperStarComp (ModuleCat.{u + 1} A) k j) hq)
  have he := congrArg (fun t ↦ t ≫
    (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).inv.app
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ).obj K)) hc
  simp only [Category.assoc, Iso.hom_inv_id_app] at he
  erw [Category.comp_id] at he
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using he.symm

private theorem pro_restrict_id {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :
    (restrictScalarsIso φ (𝟙 X)).hom.app M ≫
      (upperStarId (ModuleCat.{u + 1} A) X).hom.app
        ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj M) =
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).map
        ((upperStarId (ModuleCat.{u + 1} B) X).hom.app M) := by
  rw [← up_res_id (ModuleCat.{u + 1} A) X, ← up_res_id (ModuleCat.{u + 1} B) X]
  simp only [restrictScalarsIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatIso.ofComponents_hom_app,
    Iso.refl_hom, Category.id_comp, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  rfl

private theorem et_restrict_comp {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    (M : Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} B)) :
    (Sheaf.restrictScalars (V.smallEtaleTopology) φ).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} B) k j).hom.app M) ≫
      (Etale.openRestrictScalarsIso φ k).hom.app ((Etale.upperStar (ModuleCat.{u + 1} B) j).obj M) ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) k).map ((Etale.openRestrictScalarsIso φ j).hom.app M) =
    (Etale.openRestrictScalarsIso φ (k ≫ j)).hom.app M ≫
      (Etale.upperStarComp (ModuleCat.{u + 1} A) k j).hom.app
        ((Sheaf.restrictScalars (X.smallEtaleTopology) φ).obj M) := by
  have h := (Etale.coefficient_comp_app φ k j (k ≫ j) rfl M).symm
  rw [← Etale.openRestrictScalarsIso_inv_eq, ← Etale.openRestrictScalarsIso_inv_eq,
    ← Etale.openRestrictScalarsIso_inv_eq] at h
  apply (cancel_epi ((Etale.openRestrictScalarsIso φ (k ≫ j)).inv.app M)).mp
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  erw [Category.id_comp]
  rw [← (Etale.upperStar (ModuleCat.{u + 1} A) k).map_comp,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem et_derived_restrict_comp {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    (hq : ∀ M : Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} B),
      (Sheaf.restrictScalars (V.smallEtaleTopology) φ).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} B) k j).hom.app M) ≫
        (Etale.openRestrictScalarsIso φ k).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} B) j).obj M) ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) k).map
          ((Etale.openRestrictScalarsIso φ j).hom.app M) =
      (Etale.openRestrictScalarsIso φ (k ≫ j)).hom.app M ≫
        (Etale.upperStarComp (ModuleCat.{u + 1} A) k j).hom.app
          ((Sheaf.restrictScalars (X.smallEtaleTopology) φ).obj M)) :
    let RA (T : Scheme.{u}) := Sheaf.derivedRestrictScalars (T.smallEtaleTopology) φ
    let UB {S T : Scheme.{u}} (f : S ⟶ T) :=
      (Etale.upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory
    let UA {S T : Scheme.{u}} (f : S ⟶ T) :=
      (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    let β := Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
    let γ := Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} B) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
    Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ (k ≫ j)) =
      Functor.isoWhiskerRight γ (RA V) ≪≫
      Functor.associator (UB j) (UB k) (RA V) ≪≫
      Functor.isoWhiskerLeft (UB j)
        (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ k)) ≪≫
      (Functor.associator (UB j) (RA U) (UA k)).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ j)) (UA k) ≪≫
      Functor.associator (RA X) (UA j) (UA k) ≪≫
      Functor.isoWhiskerLeft (RA X) β.symm := by
  dsimp only
  apply Iso.ext
  ext K
  have hc :
      (Sheaf.derivedRestrictScalars (V.smallEtaleTopology) φ).map
          ((Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} B) k j) ≪≫
            Functor.mapDerivedCategoryCompIso _ _).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ k)).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj K) ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) k).mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ j)).hom.app K) =
      (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ (k ≫ j))).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).hom.app
            ((Sheaf.derivedRestrictScalars (X.smallEtaleTopology) φ).obj K) := by
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id] using congrArg (fun e ↦ e.hom.app K)
      (Functor.mapDerivedCategorySquareIso_comp
        (C₀ := Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} B))
        (C₁ := Sheaf (U.smallEtaleTopology) (ModuleCat.{u + 1} B))
        (C₂ := Sheaf (V.smallEtaleTopology) (ModuleCat.{u + 1} B))
        (D₀ := Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} A))
        (D₁ := Sheaf (U.smallEtaleTopology) (ModuleCat.{u + 1} A))
        (D₂ := Sheaf (V.smallEtaleTopology) (ModuleCat.{u + 1} A))
        (Etale.upperStar (ModuleCat.{u + 1} B) j) (Etale.upperStar (ModuleCat.{u + 1} B) k)
        (Etale.upperStar (ModuleCat.{u + 1} B) (k ≫ j))
        (Etale.upperStar (ModuleCat.{u + 1} A) j) (Etale.upperStar (ModuleCat.{u + 1} A) k)
        (Etale.upperStar (ModuleCat.{u + 1} A) (k ≫ j))
        (Sheaf.restrictScalars (X.smallEtaleTopology) φ)
        (Sheaf.restrictScalars (U.smallEtaleTopology) φ)
        (Sheaf.restrictScalars (V.smallEtaleTopology) φ)
        (Etale.openRestrictScalarsIso φ j) (Etale.openRestrictScalarsIso φ k)
        (Etale.openRestrictScalarsIso φ (k ≫ j))
        (Etale.upperStarComp (ModuleCat.{u + 1} B) k j)
        (Etale.upperStarComp (ModuleCat.{u + 1} A) k j) hq)
  have he := congrArg (fun t ↦ t ≫
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).inv.app
        ((Sheaf.derivedRestrictScalars (X.smallEtaleTopology) φ).obj K)) hc
  simp only [Category.assoc, Iso.hom_inv_id_app] at he
  erw [Category.comp_id] at he
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using he.symm

private theorem et_restrict_id {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (Etale.openRestrictScalarsIso φ (𝟙 X)).hom.app M ≫
      (Etale.upperStarId (ModuleCat.{u + 1} A) X).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) =
      (Sheaf.restrictScalars X.smallEtaleTopology φ).map
        ((Etale.upperStarId (ModuleCat.{u + 1} B) X).hom.app M) := by
  rw [← et_up_res_id (ModuleCat.{u + 1} A) X, ← et_up_res_id (ModuleCat.{u + 1} B) X]
  simp only [Etale.openRestrictScalarsIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatIso.ofComponents_hom_app,
    Iso.refl_hom, Category.id_comp, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  rfl

private theorem etale_identity_normalized (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    Etale.mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) X =
      Adjunction.leftAdjointIdIso
        (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
        (Functor.mapDerivedCategoryNatIso (Etale.upperStarId (ModuleCat.{u + 1} A) X) ≪≫
          Functor.mapDerivedCategoryIdIso _) := by
  dsimp only [Etale.mapDerivedCategoryOpenImmersionLowerShriekId,
    Etale.openImmersionLowerShriekId]
  rw [uniq_eq_conjugate]
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id _).injective
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom]
  exact Etale.derived_open_id_conjugate A X

private theorem proetale_identity_normalized (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    extensionId A X =
      Adjunction.leftAdjointIdIso
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
        (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) X) ≪≫
          Functor.mapDerivedCategoryIdIso _) := by
  dsimp only [extensionId]
  rw [uniq_eq_conjugate]
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id _).injective
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom]
  let B := ModuleCat.{u + 1} A
  let a := openImmersionLowerShriekUpperStarAdjunction B (𝟙 X)
  let e := Adjunction.leftAdjointIdIso a (upperStarId B X)
  have hu (K : Sheaf (Scheme.ProEt.topology X) B) :
      a.unit.app K ≫ (upperStar B (𝟙 X)).map (e.hom.app K) =
        Adjunction.id.unit.app K ≫ (upperStarId B X).inv.app K := by
    have h := unit_conjugateEquiv Adjunction.id a e.hom K
    simpa only [Adjunction.conjugateEquiv_leftAdjointIdIso_hom, e,
      Adjunction.id_unit, NatTrans.id_app, Functor.id_map, Functor.id_obj, Category.id_comp]
      using h.symm
  have hd := Etale.exact_adj_conjugate
    (C := Sheaf (Scheme.ProEt.topology X) B) (D := Sheaf (Scheme.ProEt.topology X) B)
    a Adjunction.id e (upperStarId B X).symm hu
  rw [Etale.exact_adj_id (C := Sheaf (Scheme.ProEt.topology X) B)] at hd
  apply Etale.identity_conjugate_of_unit
  simpa only [Functor.mapDerivedCategoryNatIso_symm, a, e, B,
    Adjunction.leftAdjointIdIso, derivedOpenImmersionLowerShriekUpperStarAdjunction] using hd

private theorem proRealization_flat
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
    (hM : ObjectProperty.flat M) :
    SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
      (R := finiteCoefficientCommRing A T) ((proRealization A T).obj M) := by
  exact OpenScalarFlatModel.finiteCoefficientRealization_flat T A M hM

private theorem etale_bounded_kflat (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hflat : ∀ n : ℤ, Etale.etaleFlat T A (P.X n)) : Etale.etaleKFlat T A P := by
  obtain ⟨a, b, hb⟩ := hbounded
  let := Scheme.etaleConstantModuleFunctor_isEquivalence T A
  let E := Scheme.etaleSumFlatModuleRealization T A
  have : E.PreservesZeroMorphisms := by
    dsimp [E, Scheme.etaleSumFlatModuleRealization]
    infer_instance
  let Q : CochainComplex _ ℤ := (E.mapHomologicalComplex (.up ℤ)).obj P
  have : Q.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff Q b).2
    (fun i hi ↦ E.map_isZero (hb i (Or.inr hi)))
  exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of.{u + 1} A))
    Q b hflat

/-- Bounded flat models stay termwise flat and K-flat after extension by zero on
both sites (on the pro-etale site the input is the comparison pullback).
Source: Stacks 0GL1, 06YQ, 09AF (blueprint: lem-sp-open-scalar-site-coherence).
Proof: Restriction is exact and the sheaf projection formula identifies tensoring
with j!P with extension by zero of tensoring with P. Exactness of j! therefore
preserves flatness. Comparison inverse image is exact and preserves flat modules.
Apply these facts degreewise, then the bounded-flat-implies-K-flat lemma on each
site, using the canonical constant-coefficient realizations. -/
theorem extension_flat_kflat (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hflat : ∀ n : ℤ, Etale.etaleFlat U A (P.X n)) :
    (∀ n : ℤ, Etale.etaleFlat X A
      ((((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (.up ℤ)).obj P).X n)) ∧
    Etale.etaleKFlat X A
      (((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
        (.up ℤ)).obj P) ∧
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology X)
      (R := finiteCoefficientCommRing A X)
      ((proRealization A X).obj
        ((((comparisonUpperStar (ModuleCat.{u + 1} A) U ⋙
          openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex
            (.up ℤ)).obj P).X n))) ∧
    CochainComplex.IsKFlatIndependentCoefficients (J := Scheme.ProEt.topology X)
      (R := finiteCoefficientCommRing A X)
      (((comparisonUpperStar (ModuleCat.{u + 1} A) U ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⋙ proRealization A X).mapHomologicalComplex
          (.up ℤ)).obj P) := by
  let h := Etale.etaleOpenTensorComparisons (RingHom.id A) j
  have hf (n : ℤ) : Etale.etaleFlat X A
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj (P.X n)) :=
    h.flat_preserved _ (hflat n)
  have hp (n : ℤ) : SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology X)
      (R := finiteCoefficientCommRing A X)
      ((proRealization A X).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj (P.X n)))) := by
    apply proRealization_flat
    apply ObjectProperty.prop_of_iso ObjectProperty.flat
      ((openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} A) j).app (P.X n))
    exact flat_comparisonUpperStar_obj ((Scheme.etaleConstantModule_flat_iff X A _).mpr (hf n))
  refine ⟨hf, h.kflat_preserved P (etale_bounded_kflat A U P hbounded hflat), hp, ?_⟩
  obtain ⟨a, b, hb⟩ := hbounded
  let E := comparisonUpperStar (ModuleCat.{u + 1} A) U ⋙
    openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⋙ proRealization A X
  let Q : CochainComplex _ ℤ := (E.mapHomologicalComplex (.up ℤ)).obj P
  have : Q.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff Q b).2
    (fun i hi ↦ E.map_isZero (hb i (Or.inr hi)))
  exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    (finiteCoefficientCommRing A X) Q b hp

private theorem comparison_restriction_mate (A : Type (u + 1)) [CommRing A]
    [Finite A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} A) X)
      (comparisonAdjunction (ModuleCat.{u + 1} A) U)
      (TwoSquare.mk _ _ _ _ (openComparisonRestrictionIso A j).hom)).natTrans = 𝟙 _ := by
  let B := ModuleCat.{u + 1} A
  let cX := comparisonAdjunction B X
  let cU := comparisonAdjunction B U
  let r := Etale.openImmersionRestrictionLowerStarAdjunction B j
  let s := openImmersionRestrictionLowerStarAdjunction B j
  apply congrArg TwoSquare.natTrans
  apply (mateEquiv s r).injective
  apply (TwoSquare.equivNatTrans _ _ _ _).injective
  change (mateEquiv s r (mateEquiv cX cU
    (TwoSquare.mk _ _ _ _ (openComparisonRestrictionIso A j).hom))).natTrans =
    (mateEquiv s r (TwoSquare.mk _ _ _ _
      (comparisonLowerStarOpenImmersionRestrictionIso B j).hom)).natTrans
  rw [iterated_mateEquiv_conjugateEquiv]
  exact (openComparisonRestrictionIso_conjugate A j).trans
    (openComparisonRestriction_directImage_mate A j).symm

private theorem comparison_restriction_left (A : Type (u + 1)) [CommRing A]
    [Finite A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ((mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} A) X)
      (comparisonAdjunction (ModuleCat.{u + 1} A) U)).symm
      (TwoSquare.mk _ _ _ _
        (comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} A) j).hom)).natTrans =
      (openComparisonRestrictionIso A j).hom := by
  apply congrArg TwoSquare.natTrans
  apply (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} A) X)
    (comparisonAdjunction (ModuleCat.{u + 1} A) U)).injective
  rw [Equiv.apply_symm_apply]
  apply (TwoSquare.equivNatTrans _ _ _ _).injective
  exact (comparison_restriction_mate A j).symm

private theorem restriction_coefficient_cube {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (openComparisonRestrictionIso A j).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) ≫
      (openImmersionRestriction (ModuleCat.{u + 1} A) j).map
        ((pbcComparisonRestrict X φ).inv.app M) =
    (pbcComparisonRestrict U φ).inv.app
        ((Etale.openImmersionRestriction (ModuleCat.{u + 1} B) j).obj M) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology U) φ).map
        ((openComparisonRestrictionIso B j).hom.app M) := by
  let aX := comparisonAdjunction (ModuleCat.{u + 1} B) X
  let aU := comparisonAdjunction (ModuleCat.{u + 1} B) U
  let dX := comparisonAdjunction (ModuleCat.{u + 1} A) X
  let dU := comparisonAdjunction (ModuleCat.{u + 1} A) U
  have hu (T : Scheme.{u}) (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      (comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
          ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj N) ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) T).map
          ((pbcComparisonRestrict T φ).inv.app N) =
      (Sheaf.restrictScalars T.smallEtaleTopology φ).map
        ((comparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app N) := by
    have hm := comparison_restrict_mate T φ
    have ht := unit_mateEquiv
      (comparisonAdjunction (ModuleCat.{u + 1} B) T)
      (comparisonAdjunction (ModuleCat.{u + 1} A) T)
      (TwoSquare.mk _ _ _ _ (pbcComparisonRestrict T φ).inv) N
    change (Sheaf.restrictScalars T.smallEtaleTopology φ).map
      ((comparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app N) ≫
      (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} B) T)
        (comparisonAdjunction (ModuleCat.{u + 1} A) T)
        (TwoSquare.mk _ _ _ _ (pbcComparisonRestrict T φ).inv)).natTrans.app
          ((comparisonUpperStar (ModuleCat.{u + 1} B) T).obj N) = _ at ht
    rw [hm] at ht
    simp only [NatTrans.id_app] at ht
    erw [Category.comp_id] at ht
    exact ht.symm
  have h := left_mate_normalization aX aU dX dU
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
    (Sheaf.restrictScalars U.smallEtaleTopology φ)
    (Sheaf.restrictScalars (Scheme.ProEt.topology U) φ)
    (pbcComparisonRestrict X φ).inv (pbcComparisonRestrict U φ).inv
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} B) j).hom
    (comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} A) j).hom
    (fun N ↦ by
      simp only [Iso.refl_hom, NatTrans.id_app]
      erw [Category.comp_id]
      exact hu X N)
    (fun N ↦ by
      simp only [Iso.refl_hom, NatTrans.id_app]
      erw [Category.comp_id]
      exact hu U N)
    (fun N ↦ by simp only [Iso.refl_hom]; rfl) M
  simp only [aX, aU, dX, dU, comparison_restriction_left, Iso.refl_hom,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp] at h
  erw [Category.comp_id] at h
  exact h

private theorem upper_coefficient_cube {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) U).map
        ((Etale.openRestrictScalarsIso φ j).inv.app M) ≫
      (pbcComparisonRestrict U φ).inv.app ((Etale.upperStar (ModuleCat.{u + 1} B) j).obj M) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology U) φ).map
        ((site_pullback B j).hom.app M) =
    (site_pullback A j).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) j).map ((pbcComparisonRestrict X φ).inv.app M) ≫
      (restrictScalarsIso φ j).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) X).obj M) := by
  let eA := Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j
  let eB := Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j
  let pA : upperStar (ModuleCat.{u + 1} A) j ≅
      openImmersionRestriction (ModuleCat.{u + 1} A) j :=
    upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j
  let pB : upperStar (ModuleCat.{u + 1} B) j ≅
      openImmersionRestriction (ModuleCat.{u + 1} B) j :=
    upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j
  let νA := comparisonUpperStar (ModuleCat.{u + 1} A) U
  let νB := comparisonUpperStar (ModuleCat.{u + 1} B) U
  let ρ : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} B) ⥤
      Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A) :=
    Sheaf.restrictScalars (Scheme.ProEt.topology U) φ
  have hsite (C : Type (u + 1)) [CommRing C] [Finite C]
      (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)) :
      (site_pullback C j).hom.app N ≫
          (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} C) j).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} C) X).obj N) =
        (comparisonUpperStar (ModuleCat.{u + 1} C) U).map
          ((Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} C) j).hom.app N) ≫
          (openComparisonRestrictionIso C j).hom.app N := by
    simp only [site_pullback, openComparisonRestrictionIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have hqp (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :
      (restrictScalarsIso φ j).inv.app N =
        pA.hom.app ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj N) ≫
          ρ.map (pB.inv.app N) := by
    simp only [restrictScalarsIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents_inv_app,
      Iso.refl_inv]
    erw [Category.comp_id]
  have hqe : (Etale.openRestrictScalarsIso φ j).inv.app M =
      eA.hom.app ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) ≫
        (Sheaf.restrictScalars U.smallEtaleTopology φ).map (eB.inv.app M) := by
    simp only [Etale.openRestrictScalarsIso, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents_inv_app,
      Iso.refl_inv]
    erw [Category.comp_id]
  let z := ρ.mapIso (pB.app ((comparisonUpperStar (ModuleCat.{u + 1} B) X).obj M))
  apply (cancel_mono z.hom).mp
  simp only [z, Functor.mapIso_hom, Iso.app_hom]
  simp only [Category.assoc]
  rw [← ρ.map_comp, hsite, hqp]
  simp only [Category.assoc]
  erw [← ρ.map_comp, Iso.inv_hom_id_app, ρ.map_id, Category.comp_id]
  have hn := pA.hom.naturality ((pbcComparisonRestrict X φ).inv.app M)
  erw [hn]
  erw [reassoc_of% (hsite A ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M))]
  rw [hqe]
  simp only [Functor.map_comp, Category.assoc]
  have hd := (pbcComparisonRestrict U φ).inv.naturality
    ((Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j).inv.app M)
  rw [reassoc_of% hd]
  erw [← ρ.map_comp_assoc, ← νB.map_comp, Iso.inv_hom_id_app]
  erw [νB.map_id, ρ.map_id, Category.id_comp]
  rw [restriction_coefficient_cube φ j M]


private theorem derived_coefficient_cube {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ j)).inv.app M) ≫
      (pbcDerivedComparisonRestrict U φ).inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj M) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U) φ).map
        ((Functor.mapDerivedCategorySquareIso
          (site_pullback B j)).hom.app M) =
    (Functor.mapDerivedCategorySquareIso
        (site_pullback A j)).hom.app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        ((pbcDerivedComparisonRestrict X φ).inv.app M) ≫
      (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ j)).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj M) := by
  have h := derived_cube
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (Sheaf.restrictScalars U.smallEtaleTopology φ)
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
    (Sheaf.restrictScalars (Scheme.ProEt.topology U) φ)
    (Etale.upperStar (ModuleCat.{u + 1} A) j)
    (Etale.upperStar (ModuleCat.{u + 1} B) j)
    (upperStar (ModuleCat.{u + 1} A) j)
    (upperStar (ModuleCat.{u + 1} B) j)
    (comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (comparisonUpperStar (ModuleCat.{u + 1} B) X)
    (comparisonUpperStar (ModuleCat.{u + 1} A) U)
    (comparisonUpperStar (ModuleCat.{u + 1} B) U)
    (Etale.openRestrictScalarsIso φ j).symm (pbcComparisonRestrict U φ).symm
    (pbcComparisonRestrict X φ).symm (restrictScalarsIso φ j).symm
    (site_pullback A j)
    (site_pullback B j)
    (upper_coefficient_cube φ j) M
  simpa only [pbcDerivedComparisonRestrict, Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc] using h

private theorem scalar_pullback_cube {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : Etale.DerivedCategoryModule A X) :
    (pbcFixedScalarExtension (Scheme.ProEt.topology U) φ).map
        ((Functor.mapDerivedCategorySquareIso
          (site_pullback A j)).hom.app M) ≫
      ((mateEquiv
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ))
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U)
      φ))).symm
          (TwoSquare.mk _ _ _ _
            (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ j)).inv)).natTrans.app
              ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M) ≫
      (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((pbcComparisonReduction X φ).hom.app M) =
    (pbcComparisonReduction U φ).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) U).mapDerivedCategory.map
        ((Etale.openScalarRestriction φ j).hom.app M) ≫
      (Functor.mapDerivedCategorySquareIso
        (site_pullback B j)).hom.app
          ((Etale.scalarExtension φ X).obj M) := by
  let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let al := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let am := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)
  let ad := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U) φ)
  let t := TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ j)).inv
  let k := TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict U φ).inv
  let c := TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict X φ).inv
  let q := TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ j)).inv
  let b := Functor.mapDerivedCategorySquareIso
    (site_pullback A j)
  let b' := Functor.mapDerivedCategorySquareIso
    (site_pullback B j)
  have hp : TwoSquare.vComp t k = TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ) b.hom ≫
        (TwoSquare.vComp c q).natTrans ≫ Functor.whiskerRight b'.inv
          (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U) φ)) := by
    ext N
    simp only [TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
    dsimp only [t, k, c, q, b, b']
    apply (cancel_mono ((Sheaf.derivedRestrictScalars
      (Scheme.ProEt.topology U) φ).map
        ((Functor.mapDerivedCategorySquareIso
          (site_pullback B j)).hom.app N))).mp
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
    exact derived_coefficient_cube φ j N
  have h := inverse_mate_cube a al am ad t k c q b b' hp M
  simpa only [a, al, am, ad, t, k, c, q, b, b', pbcComparisonReduction, asIso_hom,
    pbcComparisonReductionMap, Etale.openScalarRestriction, asIso_hom,
    Etale.openScalarRestrictionMap, Etale.openDerivedRestrictScalarsIso,
    pbcFixedScalarExtension, Etale.scalarExtension,
    Category.assoc,
    TwoSquare, TwoSquare.mk, TwoSquare.natTrans] using h

private theorem scalar_site_square_aux {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (L : Etale.DerivedCategoryModule A U) :
    (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).map
        ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} A) j).hom.app L) ≫
      (scalarOpen φ j).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj L) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((pbcComparisonReduction U φ).hom.app L) =
    (pbcComparisonReduction X φ).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj L) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
        ((Etale.openScalarExtension φ j).hom.app L) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} B) j).hom.app
          ((Etale.scalarExtension φ U).obj L) := by
  let ae := Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j
  let ap := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let be := Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) j
  let bp := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let xe := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let ue := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let xp := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)
  let up := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U) φ)
  let qe := Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ j)
  let qp := Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ j)
  let le := ((mateEquiv xe ue).symm (TwoSquare.mk _ _ _ _ qe.inv)).natTrans
  let lp := ((mateEquiv xp up).symm (TwoSquare.mk _ _ _ _ qp.inv)).natTrans
  have he (N : Etale.DerivedCategoryModule A U) :
      be.unit.app ((Etale.scalarExtension φ U).obj N) ≫
        (Etale.upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
          ((Etale.openScalarExtension φ j).inv.app N) =
      (Etale.scalarExtension φ U).map (ae.unit.app N) ≫ le.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj N) := by
    have h := unit_mateEquiv_symm ae be
      ((mateEquiv xe ue).symm (TwoSquare.mk _ _ _ _ qe.inv)) N
    have hm := scalar_open_inverse_mate ae be xe ue qe
    change (Etale.scalarExtension φ U).map (ae.unit.app N) ≫ le.app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj N) =
      be.unit.app ((Etale.scalarExtension φ U).obj N) ≫ (Etale.upperStar (ModuleCat.{u + 1} B)
      j).mapDerivedCategory.map
        (((mateEquiv ae be).symm ((mateEquiv xe ue).symm
          (TwoSquare.mk _ _ _ _ qe.inv))).natTrans.app N) at h
    rw [hm] at h
    exact h.symm
  have hp (N : DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A))) :
      bp.unit.app ((pbcFixedScalarExtension (Scheme.ProEt.topology U) φ).obj N) ≫
        (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
          ((scalarOpen φ j).inv.app N) =
      (pbcFixedScalarExtension (Scheme.ProEt.topology U) φ).map (ap.unit.app N) ≫ lp.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj N) := by
    have h := unit_mateEquiv_symm ap bp
      ((mateEquiv xp up).symm (TwoSquare.mk _ _ _ _ qp.inv)) N
    have hm := scalar_open_inverse_mate ap bp xp up qp
    change (pbcFixedScalarExtension (Scheme.ProEt.topology U) φ).map (ap.unit.app N) ≫ lp.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj N) =
      bp.unit.app ((pbcFixedScalarExtension (Scheme.ProEt.topology U) φ).obj N) ≫ (upperStar
      (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        (((mateEquiv ap bp).symm ((mateEquiv xp up).symm
          (TwoSquare.mk _ _ _ _ qp.inv))).natTrans.app N) at h
    rw [hm] at h
    exact h.symm
  have h := open_mate_cube ae ap be bp
    (Etale.openScalarExtension φ j) (scalarOpen φ j)
    (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} A) j).symm
    (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} B) j).symm
    le lp (pbcComparisonReduction U φ).symm (pbcComparisonReduction X φ).symm
    (Functor.mapDerivedCategorySquareIso
      (site_pullback A j))
    (Functor.mapDerivedCategorySquareIso
      (site_pullback B j))
    he hp (comparison_derived_extension_mate A j) (comparison_derived_extension_mate B j)
    (scalar_pullback_cube φ j) L
  simp only [Iso.symm_hom, Iso.symm_inv] at h
  let eA := mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
    (ModuleCat.{u + 1} A) j
  let eB := mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
    (ModuleCat.{u + 1} B) j
  let SX := pbcFixedScalarExtension (Scheme.ProEt.topology X) φ
  let NX := (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory
  let a := SX.mapIso (eA.app L) ≪≫
    (scalarOpen φ j).app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj L)
  let b := NX.mapIso ((Etale.openScalarExtension φ j).app L) ≪≫
    eB.app ((Etale.scalarExtension φ U).obj L)
  let d := J.mapIso ((pbcComparisonReduction U φ).app L)
  let c := (pbcComparisonReduction X φ).app
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj L)
  have hi : d ≪≫ b.symm = a.symm ≪≫ c := by
    apply Iso.ext
    simpa only [d, b, a, c, J, NX, SX, eA, eB, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom,
      Iso.app_inv, Category.assoc] using h
  have hr : a ≪≫ d = c ≪≫ b := by
    calc
      a ≪≫ d = a ≪≫ (d ≪≫ b.symm) ≪≫ b := by simp
      _ = a ≪≫ (a.symm ≪≫ c) ≪≫ b := by rw [hi]
      _ = c ≪≫ b := by simp
  simpa only [d, b, a, c, J, NX, SX, eA, eB, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc] using congrArg Iso.hom hr


/-- The scalar/open/site square, in the ordinary fixed-coefficient derived
categories. All three comparisons are specified natural isomorphisms, so this
assertion is natural in L. Source: Stacks 0GL1, 0E8I, 09AF, 0G7E
(blueprint: lem-sp-open-scalar-site-coherence).
Proof: Normalize the ordinary coefficient/site pullback cube by the units of
comparison pullback and literal open restriction. Transport it through the
canonical upper-star/restriction identifications, then descend this exact-functor
cube to derived categories. Taking scalar-extension mates followed by open
extension mates gives the inverse square. Cancel its canonical isomorphisms to
obtain the displayed square. This proves the equation for arbitrary L, so the
recorded bounded flat representative is not needed for this coherence equation. -/
theorem scalar_site_square {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (L : Etale.DerivedCategoryModule A U)
    (P : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hflat : ∀ n : ℤ, Etale.etaleFlat U A (P.X n))
    (hrep : Nonempty ((DerivedCategory.Q.obj P) ≅ L)) :
    (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).map
        ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} A) j).hom.app L) ≫
      (scalarOpen φ j).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj L) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((pbcComparisonReduction U φ).hom.app L) =
    (pbcComparisonReduction X φ).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj L) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
        ((Etale.openScalarExtension φ j).hom.app L) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} B) j).hom.app
          ((Etale.scalarExtension φ U).obj L) := by
  have _hb := hbounded
  have _hf := hflat
  have _hr := hrep
  exact scalar_site_square_aux φ j L

/-- Scalar/open composition coherence on the etale site, with the canonical
open compositors. Source: Stacks 03DI, 0E8I, 0GL1
(blueprint: lem-sp-open-scalar-site-coherence).
Proof: The ordinary compositor composes the extension factorizations. Both
scalar routes send each generating section tensored with b to the same extension
generator with section s tensor b; if there is no factorization the source is
zero. The sheafification universal property gives equality of sheaf maps, also
through intermediate sheafification. Apply this calculation degreewise on K-flat
resolutions, preserved by open extension, and descend to the derived category.
Equivalently, compose the specified scalar/open adjunction mates and use their
uniqueness with the restriction compositor. -/
theorem etale_scalar_comp {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {V U X : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion k] [IsOpenImmersion j]
    (L : Etale.DerivedCategoryModule A V) :
    (Etale.scalarExtension φ X).map
        ((Etale.mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) k j).hom.app L) ≫
      (Etale.openScalarExtension φ j).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj L) ≫
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((Etale.openScalarExtension φ k).hom.app L) ≫
      (Etale.mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} B) k j).inv.app ((Etale.scalarExtension φ V).obj L) =
    (Etale.openScalarExtension φ (k ≫ j)).hom.app L := by
  exact scalar_composition
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (V.smallEtaleTopology) φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (U.smallEtaleTopology) φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (X.smallEtaleTopology) φ))
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k)
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (k ≫ j))
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) k)
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) (k ≫ j))
    (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ k))
    (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ j))
    (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ (k ≫ j)))
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _)
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} B) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).symm
    (Etale.mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) k j)
    (Etale.mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} B) k j)
    (Iso.ext (Etale.derived_open_comp_conjugate (ModuleCat.{u + 1} A) k j))
    (Iso.ext (Etale.derived_open_comp_conjugate (ModuleCat.{u + 1} B) k j))
    (et_derived_restrict_comp φ k j (et_restrict_comp φ k j)) L


/-- The scalar/open comparison for the identity open is the identity after the
canonical identity identifications. Source: Stacks 03DI, 0E8I, 0GL1
(blueprint: lem-sp-open-scalar-site-coherence).
Proof: The unique identity factorization leaves every extension generator
unchanged. Tensoring its section gives the identity scalar comparison; apply the
sheafification universal property and descend on K-flat representatives.
The adjunction definition has exactly this identity normalization. -/
theorem etale_scalar_id {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (X : Scheme.{u})
    (L : Etale.DerivedCategoryModule A X) :
    (Etale.openScalarExtension φ (𝟙 X)).hom.app L ≫
      (Etale.mapDerivedCategoryOpenImmersionLowerShriekId
        (ModuleCat.{u + 1} B) X).hom.app ((Etale.scalarExtension φ X).obj L) =
    (Etale.scalarExtension φ X).map
      ((Etale.mapDerivedCategoryOpenImmersionLowerShriekId
        (ModuleCat.{u + 1} A) X).hom.app L) := by
  rw [etale_identity_normalized B X, etale_identity_normalized A X]
  exact scalar_identity
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) (𝟙 X))
    (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ (𝟙 X)))
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarId (ModuleCat.{u + 1} A) X) ≪≫
      Functor.mapDerivedCategoryIdIso _)
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarId (ModuleCat.{u + 1} B) X) ≪≫
      Functor.mapDerivedCategoryIdIso _)
    (fun M ↦ exact_identity_square
      (Etale.upperStar (ModuleCat.{u + 1} B) (𝟙 X))
      (Sheaf.restrictScalars X.smallEtaleTopology φ)
      (Etale.upperStar (ModuleCat.{u + 1} A) (𝟙 X))
      (Etale.openRestrictScalarsIso φ (𝟙 X))
      (Etale.upperStarId (ModuleCat.{u + 1} B) X)
      (Etale.upperStarId (ModuleCat.{u + 1} A) X) (et_restrict_id φ X) M) L

/-- Scalar/open composition coherence on the proetale site, with the canonical
open compositors. Source: Stacks 03DI, 0E8I, 0GL1
(blueprint: lem-sp-open-scalar-site-coherence).
Proof: The ordinary compositor composes the extension factorizations. Both
scalar routes send each generating section tensored with b to the same extension
generator with section s tensor b; if there is no factorization the source is
zero. The sheafification universal property gives equality of sheaf maps, also
through intermediate sheafification. Apply this calculation degreewise on K-flat
resolutions, preserved by open extension, and descend to the derived category.
Equivalently, compose the specified scalar/open adjunction mates and use their
uniqueness with the restriction compositor. -/
theorem proetale_scalar_comp {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {V U X : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion k] [IsOpenImmersion j]
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A))) :
    (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).map ((extensionComp A k j).hom.app L) ≫
      (scalarOpen φ j).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj L) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((scalarOpen φ k).hom.app L) ≫
      (extensionComp B k j).inv.app ((pbcFixedScalarExtension (Scheme.ProEt.topology V) φ).obj L) =
    (scalarOpen φ (k ≫ j)).hom.app L := by
  exact scalar_composition
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology V) φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U) φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (k ≫ j))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) k)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) (k ≫ j))
    (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ k))
    (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ j))
    (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ (k ≫ j)))
    (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _)
    (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} B) k j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).symm
    (extensionComp A k j) (extensionComp B k j)
    (Iso.ext (pro_derived_comp_conjugate A k j))
    (Iso.ext (pro_derived_comp_conjugate B k j))
    (pro_derived_restrict_comp φ k j (pro_restrict_comp φ k j)) L

/-- The scalar/open comparison for the identity open is the identity after the
canonical identity identifications. Source: Stacks 03DI, 0E8I, 0GL1
(blueprint: lem-sp-open-scalar-site-coherence).
Proof: The unique identity factorization leaves every extension generator
unchanged. Tensoring its section gives the identity scalar comparison; apply the
sheafification universal property and descend on K-flat representatives.
The adjunction definition has exactly this identity normalization. -/
theorem proetale_scalar_id {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (X : Scheme.{u})
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (scalarOpen φ (𝟙 X)).hom.app L ≫
      (extensionId B X).hom.app ((pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).obj L) =
    (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).map ((extensionId A X).hom.app L) := by
  rw [proetale_identity_normalized B X, proetale_identity_normalized A X]
  exact scalar_identity
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) (𝟙 X))
    (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ (𝟙 X)))
    (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) X) ≪≫
      Functor.mapDerivedCategoryIdIso _)
    (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} B) X) ≪≫
      Functor.mapDerivedCategoryIdIso _)
    (fun M ↦ exact_identity_square
      (upperStar (ModuleCat.{u + 1} B) (𝟙 X))
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
      (upperStar (ModuleCat.{u + 1} A) (𝟙 X))
      (restrictScalarsIso φ (𝟙 X))
      (upperStarId (ModuleCat.{u + 1} B) X)
      (upperStarId (ModuleCat.{u + 1} A) X) (pro_restrict_id φ X) M) L

/-- Derived site comparisons compose with the same open compositors.
Source: Stacks 09AF (blueprint: lem-sp-open-scalar-site-coherence).
Proof: Use the recorded sheaf site-comparison composition identity, whose two
maps have the same transpose under the open adjunctions. Apply the degreewise
complex functor and localization. The derived functor composition isomorphisms
identify the resulting equation with this displayed equation. -/
theorem site_comp (R : Type (u + 1)) [CommRing R] [Finite R]
    {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j] (L : Etale.DerivedCategoryModule R V) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.map
        ((Etale.mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} R) k j).hom.app L) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} R) j).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) k).mapDerivedCategory.obj L) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.map
        ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} R) k).hom.app L) ≫
      (extensionComp R k j).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} R) V).mapDerivedCategory.obj L) =
    (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} R) (k ≫ j)).hom.app L := by
  let E (T : Scheme.{u}) := comparisonUpperStar (ModuleCat.{u + 1} R) T
  let f := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) k
  let g := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j
  let fg := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) (k ≫ j)
  let f' := openImmersionLowerShriek (ModuleCat.{u + 1} R) k
  let g' := openImmersionLowerShriek (ModuleCat.{u + 1} R) j
  let fg' := openImmersionLowerShriek (ModuleCat.{u + 1} R) (k ≫ j)
  have hq (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} R)) :
      (E X).map ((Etale.openImmersionLowerShriekComp
        (ModuleCat.{u + 1} R) k j).hom.app F) ≫
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) j).hom.app
        (f.obj F) ≫ g'.map
        ((openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) k).hom.app F) =
      (openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} R) (k ≫ j)).hom.app F ≫
      (proEtaleOpenExtensionComp R k j).hom.app ((E V).obj F) := by
    have hc := (openImmersionLowerShriekComparison_coherence R).2.1 k j F
    have he := congrArg (fun t ↦ t ≫
      (proEtaleOpenExtensionComp R k j).hom.app ((E V).obj F)) hc
    simpa [Category.assoc, E, f, g'] using he
  have hc :
      (E X).mapDerivedCategory.map
          ((Etale.mapDerivedCategoryOpenImmersionLowerShriekComp
            (ModuleCat.{u + 1} R) k j).hom.app L) ≫
        (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} R) j).hom.app (f.mapDerivedCategory.obj L) ≫
        g'.mapDerivedCategory.map
          ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} R) k).hom.app L) =
      (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} R) (k ≫ j)).hom.app L ≫
        (extensionComp R k j).hom.app ((E V).mapDerivedCategory.obj L) := by
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Iso.symm_hom, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id,
      mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso,
      Etale.mapDerivedCategoryOpenImmersionLowerShriekComp, extensionComp, E, f, g, fg,
      f', g', fg'] using (congrArg (fun e ↦ e.hom.app L)
      (Functor.mapDerivedCategorySquareIso_comp
      (C₀ := Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} R))
      (C₁ := Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))
      (C₂ := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
      (D₀ := Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} R))
      (D₁ := Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R))
      (D₂ := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))
      f g fg f' g' fg' (E V) (E U) (E X)
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) k)
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) j)
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) (k ≫ j))
      (Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} R) k j)
      (proEtaleOpenExtensionComp R k j) hq))
  have he := congrArg (fun t ↦ t ≫ (extensionComp R k j).inv.app
    ((E V).mapDerivedCategory.obj L)) hc
  simp only [Category.assoc, Iso.hom_inv_id_app] at he
  erw [Category.comp_id] at he
  simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso,
    Etale.mapDerivedCategoryOpenImmersionLowerShriekComp, extensionComp, E, f, g, fg,
    f', g', fg'] using he

/-- The derived site comparison for the identity open is the identity after the
canonical identity identifications. Source: Stacks 09AF
(blueprint: lem-sp-open-scalar-site-coherence).
Proof: For the identity open, restriction and its comparison are identities.
The unit normalization of the site comparison forces the sheaf comparison to
be the identity. Apply degreewise complexes and localization to that recorded
identity, using the derived identity isomorphisms. -/
theorem site_id (R : Type (u + 1)) [CommRing R] [Finite R]
    (X : Scheme.{u}) (L : Etale.DerivedCategoryModule R X) :
    (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} R) (𝟙 X)).hom.app L ≫
      (extensionId R X).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj L) =
    (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.map
      ((Etale.mapDerivedCategoryOpenImmersionLowerShriekId
        (ModuleCat.{u + 1} R) X).hom.app L) := by
  have h := exact_identity_square
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) (𝟙 X))
    (comparisonUpperStar (ModuleCat.{u + 1} R) X)
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) (𝟙 X))
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) (𝟙 X))
    (Adjunction.leftAdjointIdIso
      (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) (𝟙 X))
      (Etale.upperStarId (ModuleCat.{u + 1} R) X))
    (Adjunction.leftAdjointIdIso
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} R) (𝟙 X))
      (upperStarId (ModuleCat.{u + 1} R) X))
    ((openImmersionLowerShriekComparison_coherence R).2.2 X) L
  dsimp only [extensionId, Etale.mapDerivedCategoryOpenImmersionLowerShriekId]
  rw [uniq_eq_conjugate]
  dsimp only [Etale.openImmersionLowerShriekId]
  rw [uniq_eq_conjugate]
  exact h

end AlgebraicGeometry.ProEtale.OpenScalarSite
