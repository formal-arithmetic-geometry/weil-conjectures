/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124; NA stage-2 revalidation
-/
module

public import Sheaf.CategoryTheory.FlatRingedDiagramRestrictionComparisonAdjuncts
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.FlatRestrictionExactLeftAdjoint
import Sheaf.CategoryTheory.FlatRestrictionOrdinaryComparisons
import Sheaf.CategoryTheory.FlatRestrictionDerivedMate
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Flat coefficient restriction on derived module diagrams

Source: Stacks Project, Derived Categories, Tags 0FND and 0DVC; Modules on Sites,
Tag 03D3, specialized to compatible flat coefficient changes on diagram sites
(blueprint: lem-weil-pbc-flat-ringed-diagram-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
namespace FlatRingedDiagramInput

open SheafOfModules in
private theorem forget_preserves_colimits
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C} (A : Sheaf K RingCat.{u}) :
    PreservesFiniteColimits (toSheaf.{u} A) := by
  constructor
  intro T _ _
  constructor
  intro F
  let L := PresheafOfModules.sheafification.{u} (𝟙 A.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 A.obj)
  let G := F ⋙ (SheafOfModules.forget A ⋙ PresheafOfModules.restrictScalars (𝟙 A.obj))
  let e : G ⋙ L ≅ F := Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ F.rightUnitor
  have : PreservesColimitsOfShape T (presheafToSheaf K AddCommGrpCat.{u}) :=
    (sheafificationAdjunction K AddCommGrpCat.{u}).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have : PreservesColimit G (L ⋙ toSheaf.{u} A) :=
    preservesColimit_of_natIso G (PresheafOfModules.sheafificationCompToSheaf (𝟙 A.obj)).symm
  let hc := colimit.isColimit G
  have : PreservesColimit (G ⋙ L) (toSheaf.{u} A) :=
    preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves L hc)
      (isColimitOfPreserves (L ⋙ toSheaf.{u} A) hc)
  exact preservesColimit_of_iso_diagram (toSheaf.{u} A) e

open SheafOfModules in
private theorem restrict_exact
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    {R S : Sheaf K CommRingCat.{u}} (c : R ⟶ S) :
    exactFunctor _ _ (restrictScalars.{u}
      ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map c)) := by
  let R' := (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let S' := (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S
  let res := restrictScalars.{u}
    ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map c)
  have := forget_preserves_colimits R'
  have := forget_preserves_colimits S'
  have : PreservesFiniteLimits (res ⋙ toSheaf R') :=
    inferInstanceAs (PreservesFiniteLimits (toSheaf.{u} S'))
  have : PreservesFiniteColimits (res ⋙ toSheaf R') :=
    inferInstanceAs (PreservesFiniteColimits (toSheaf.{u} S'))
  have : ReflectsFiniteColimits (toSheaf.{u} R') :=
    inferInstance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves res (toSheaf R'),
    preservesFiniteColimits_of_reflects_of_preserves res (toSheaf R')⟩



private theorem adjunct_mate
    {A B E F : Type*} [Category A] [Category B] [Category E] [Category F]
    {LS : A ⥤ B} {FS : B ⥤ A} {LR : E ⥤ F} {FR : F ⥤ E}
    (aS : LS ⊣ FS) (aR : LR ⊣ FR) (rV : A ⥤ E) (rU : B ⥤ F)
    (b : LS ⋙ rU ≅ rV ⋙ LR) (M : A) (N : B) (t : LS.obj M ⟶ N) :
    aR.homEquiv (rV.obj M) (rU.obj N) (b.inv.app M ≫ rU.map t) =
      rV.map (aS.homEquiv M N t) ≫
        (mateEquiv aS aR (TwoSquare.mk _ _ _ _ b.inv)).app N := by
  let d := mateEquiv aS aR (TwoSquare.mk _ _ _ _ b.inv)
  have h := unit_mateEquiv aS aR (TwoSquare.mk _ _ _ _ b.inv) M
  change rV.map (aS.unit.app M) ≫ d.app (LS.obj M) =
    aR.unit.app (rV.obj M) ≫ FR.map (b.inv.app M) at h
  rw [aR.homEquiv_unit, FR.map_comp, ← Category.assoc, ← h, Category.assoc]
  have hd : d.app (LS.obj M) ≫ FR.map (rU.map t) =
      rV.map (FS.map t) ≫ d.app N := d.natTrans.naturality t |>.symm
  rw [hd]
  rw [aS.homEquiv_unit, rV.map_comp, Category.assoc]

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {H : GrothendieckTopology D}
  (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]
  [HasDerivedCategory.{w} (x.diagramsRU J)]
  [HasDerivedCategory.{w} (x.diagramsSU J)]
  [HasDerivedCategory.{w} (x.diagramsRV J)]
  [HasDerivedCategory.{w} (x.diagramsSV J)]
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem inverse_localization
    (LR : derivedRV x J ⥤ derivedRU x J)
    (LS : derivedSV x J ⥤ derivedSU x J)
    (rU : derivedSU x J ⥤ derivedRU x J)
    (rV : derivedSV x J ⥤ derivedRV x J)
    (qLR : DerivedCategory.Q ⋙ LR ≅ inverseRComplex x J ⋙ DerivedCategory.Q)
    (qLS : DerivedCategory.Q ⋙ LS ≅ inverseSComplex x J ⋙ DerivedCategory.Q)
    (qU : DerivedCategory.Q ⋙ rU ≅ restrictUComplex x J ⋙ DerivedCategory.Q)
    (qV : DerivedCategory.Q ⋙ rV ≅ restrictVComplex x J ⋙ DerivedCategory.Q)
    (b0 : x.inverseS J ⋙ x.restrictU J ≅ x.restrictV J ⋙ x.inverseR J) :
    ∃ b : LS ⋙ rU ≅ rV ⋙ LR, ∀ P : cochainSV x J,
      rU.map (qLS.hom.app P) ≫ qU.hom.app ((inverseSComplex x J).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b0 (.up ℤ)).hom.app P) =
      b.hom.app (DerivedCategory.Q.obj P) ≫ LR.map (qV.hom.app P) ≫
        qLR.hom.app ((restrictVComplex x J).obj P) := by
  let c : DerivedCategory.Q ⋙ (LS ⋙ rU) ≅ DerivedCategory.Q ⋙ (rV ⋙ LR) :=
    isoWhiskerRight qLS rU ≪≫ isoWhiskerLeft (inverseSComplex x J) qU ≪≫
      isoWhiskerRight (NatIso.mapHomologicalComplex b0 (.up ℤ)) DerivedCategory.Q ≪≫
      isoWhiskerLeft (restrictVComplex x J) qLR.symm ≪≫ isoWhiskerRight qV.symm LR
  let b := Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (x.diagramsSV J) (.up ℤ))
    (DerivedCategory.Q ⋙ (LS ⋙ rU)) (DerivedCategory.Q ⋙ (rV ⋙ LR))
    (LS ⋙ rU) (rV ⋙ LR) c
  refine ⟨b, ?_⟩
  intro P
  have hb : b.hom.app (DerivedCategory.Q.obj P) = c.hom.app P := by
    simp [b, Localization.liftNatIso, Localization.liftNatTrans_app,
      Localization.Lifting.compLeft]
  rw [hb]
  simp only [c, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    whiskerRight_app, isoWhiskerLeft_hom, whiskerLeft_app, Iso.symm_hom]
  simp only [Category.assoc, ← LR.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, Category.id_comp]
  simp only [← Category.assoc]
  exact (Category.comp_id _).symm

/-- Flat coefficient restriction is exact, preserves K-injective diagram complexes,
and has canonical inverse-image and right-derived-direct-image comparisons compatible
with the normalized derived adjunctions. The supplied derived functors have universal
right-derived units, invertible on K-injectives, and the representative transpose
formula of 0FND. These specify the
chosen derived operations. The factor isomorphisms identify rU and rV
with exact localization of the actual termwise restriction functors. The b equation
is exact localization of the ordinary comparison. The d equation is its universal
right-derived-unit normalization, in particular the identity on K-injectives.

Source: Stacks 0FND, 0DVC and 03D3, specialized to compatible flat coefficient changes
on the product diagram sites
(blueprint: lem-weil-pbc-flat-ringed-diagram-restriction).

Proof plan (the ten steps of the node, grouped by construction):
1. Use lem-weil-pbc-diagram-site-realization to realize the four diagram categories
as sheaves of modules on the small product sites. All subsequent maps are maps of
these diagram categories; no equality is inferred only from derived evaluations.
2. Restriction changes only the scalar action. Kernels are computed sectionwise
and cokernels by sheafification, so restriction is exact. Tensor extension is its
left adjoint. Flatness makes that adjoint exact, also on diagrams, since kernels,
cokernels and tensor extension are pointwise. An exact left adjoint sends acyclic
complexes to acyclic complexes; the complex Hom adjunction and homotopy adjunction
therefore show that restriction preserves K-injectives.
3. The structural ring square identifies the two inverse-image actions. The
identity on identified inverse-image sheaves is linear and natural, giving b0.
The adjoint ring square similarly identifies the direct-image actions, giving d0.
These are identities on every sheaf and diagram transition. Exact localization
gives rU, rV and b with their displayed factor and normalization equations.
4. Choose K-injective diagram resolutions. Their restrictions remain K-injective
by step 2, so both right-derived images are computed by the same ordinary diagram
identity d0. This defines d and proves it invertible. The universal right-derived
units extend this construction naturally and give the displayed equation on all
complexes. On a K-injective I both units are isomorphisms, exactly the stated
normalization of d at QI; computesR and computesS supply these isomorphisms.
5. The underlying set-sheaf adjunction identifies b0 and d0 as mates, by the
transpose equations of the input. Apply the fraction-normalized Hom comparison
of lem-pc-pre-derived-adjoint-functors-general. For its representing cocone, choose
a resolution s0: K → I0 and set p_s = RF(Qs)⁻¹ β_I, with splitting
ρ = β_I0⁻¹ RF(Qs0). A common refinement into a K-injective diagram gives
QF(a) ρ p_s = QF(c). For the exact left-derived functor use the cone
u_t = QG(t)⁻¹ ∘ φ_M and splitting φ_M⁻¹; the dual fraction equation holds.
These supply the essential-constancy hypotheses, rather than assuming them.
On a K-injective target the identity
of step 4 and the ordinary transpose equation give the final displayed adjunct
equation. Represent arbitrary derived morphisms by fractions and use naturality
and invertibility of their denominators to obtain the equation for every M,N,t.
All constructions occur in full diagram categories, retaining every J-arrow. -/
theorem flatRingedDiagramRestriction
    (LR : derivedRV x J ⥤ derivedRU x J)
    (FR : derivedRU x J ⥤ derivedRV x J)
    (qLR : DerivedCategory.Q ⋙ LR ≅
      inverseRComplex x J ⋙ DerivedCategory.Q)
    (ηR : directRComplex x J ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ FR)
    (aR : LR ⊣ FR)
    (derivedR : FR.IsRightDerivedFunctor ηR
      (HomologicalComplex.quasiIso (x.diagramsRU J) (.up ℤ)))
    (computesR : ∀ I : cochainRU x J,
      I.IsKInjective → IsIso (ηR.app I))
    (transposeR : ∀ (P : cochainRV x J)
      (I : cochainRU x J)
      (f : (inverseRComplex x J).obj P ⟶ I),
      aR.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
        (qLR.hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        (((Adjunction.whiskerRight J x.R.adjunction).mapHomologicalComplex (.up ℤ)).homEquiv
          P I f) ≫ ηR.app I)
    (LS : derivedSV x J ⥤ derivedSU x J)
    (FS : derivedSU x J ⥤ derivedSV x J)
    (qLS : DerivedCategory.Q ⋙ LS ≅
      inverseSComplex x J ⋙ DerivedCategory.Q)
    (ηS : directSComplex x J ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ FS)
    (aS : LS ⊣ FS)
    (derivedS : FS.IsRightDerivedFunctor ηS
      (HomologicalComplex.quasiIso (x.diagramsSU J) (.up ℤ)))
    (computesS : ∀ I : cochainSU x J,
      I.IsKInjective → IsIso (ηS.app I))
    (transposeS : ∀ (P : cochainSV x J)
      (I : cochainSU x J)
      (f : (inverseSComplex x J).obj P ⟶ I),
      aS.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
        (qLS.hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        (((Adjunction.whiskerRight J x.S.adjunction).mapHomologicalComplex (.up ℤ)).homEquiv
          P I f) ≫ ηS.app I) :
    PreservesFiniteLimits (x.restrictU J) ∧
    PreservesFiniteColimits (x.restrictU J) ∧
    PreservesFiniteLimits (x.restrictV J) ∧
    PreservesFiniteColimits (x.restrictV J) ∧
    (∀ I : cochainSU x J, I.IsKInjective →
      CochainComplex.IsKInjective ((restrictUComplex x J).obj I)) ∧
    (∀ I : cochainSV x J, I.IsKInjective →
      CochainComplex.IsKInjective ((restrictVComplex x J).obj I)) ∧
    Nonempty (DerivedRestrictionComparison (x := x) (J := J) LR FR qLR ηR aR LS FS qLS ηS aS) := by
  have hU := restrict_exact x.aU
  have hV := restrict_exact x.aV
  have : PreservesFiniteLimits (SheafOfModules.restrictScalars
      ((sheafCompose H (forget₂ CommRingCat RingCat)).map x.aU)) := hU.1
  have : PreservesFiniteColimits (SheafOfModules.restrictScalars
      ((sheafCompose H (forget₂ CommRingCat RingCat)).map x.aU)) := hU.2
  have : PreservesFiniteLimits (SheafOfModules.restrictScalars
      ((sheafCompose K (forget₂ CommRingCat RingCat)).map x.aV)) := hV.1
  have : PreservesFiniteColimits (SheafOfModules.restrictScalars
      ((sheafCompose K (forget₂ CommRingCat RingCat)).map x.aV)) := hV.2
  have hUL : PreservesFiniteLimits (x.restrictU J) := by
    constructor
    intro T _ _
    exact whiskeringRight_preservesLimitsOfShape _
  have hUC : PreservesFiniteColimits (x.restrictU J) := by
    constructor
    intro T _ _
    exact whiskeringRight_preservesColimitsOfShape _
  have hVL : PreservesFiniteLimits (x.restrictV J) := by
    constructor
    intro T _ _
    exact whiskeringRight_preservesLimitsOfShape _
  have hVC : PreservesFiniteColimits (x.restrictV J) := by
    constructor
    intro T _ _
    exact whiskeringRight_preservesColimitsOfShape _
  have := hUL
  have := hUC
  have := hVL
  have := hVC
  have kinj {T : Type u} [SmallCategory T] {L : GrothendieckTopology T}
      {R S : Sheaf L CommRingCat.{u}} (a : R ⟶ S)
      (hf : SheafOfModules.IsFlatOnSite.{u, u, u, u}
        ((SheafOfModules.restrictScalars.{u}
          ((sheafCompose L (forget₂ CommRingCat RingCat)).map a)).obj
          (SheafOfModules.unit.{u} ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S)))) :
      ((Functor.whiskeringRight J _ _).obj (SheafOfModules.restrictScalars.{u}
        ((sheafCompose L (forget₂ CommRingCat RingCat)).map a))).PreservesKInjectiveComplexes := by
    obtain ⟨E, hE, hlim, ⟨adj⟩⟩ := SheafOfModules.flatRestriction_exact_leftAdjoint a hf
    have := hE
    have := hlim
    have : PreservesColimits E := adj.leftAdjoint_preservesColimits
    let ED := (Functor.whiskeringRight J _ _).obj E
    have : PreservesFiniteLimits ED := by
      constructor
      intro T _ _
      exact whiskeringRight_preservesLimitsOfShape _
    have : PreservesFiniteColimits ED := by
      constructor
      intro T _ _
      exact whiskeringRight_preservesColimitsOfShape _
    exact (Adjunction.whiskerRight J adj).preservesKInjectiveComplexes
  have hKU := kinj x.aU x.flatU
  have hKV := kinj x.aV x.flatV
  have := hKU
  have := hKV
  have kU : ∀ I : cochainSU x J, I.IsKInjective →
      CochainComplex.IsKInjective ((restrictUComplex x J).obj I) := by
    intro I hI
    let : CochainComplex.IsKInjective I := hI
    let : ((Functor.whiskeringRight J _ _).obj
        (SheafOfModules.restrictScalars.{u}
          ((sheafCompose H (forget₂ CommRingCat RingCat)).map
            x.aU))).PreservesKInjectiveComplexes := hKU
    exact Functor.PreservesKInjectiveComplexes.isKInjective_map I
  have kV : ∀ I : cochainSV x J, I.IsKInjective →
      CochainComplex.IsKInjective ((restrictVComplex x J).obj I) := by
    intro I hI
    let : CochainComplex.IsKInjective I := hI
    let : ((Functor.whiskeringRight J _ _).obj
        (SheafOfModules.restrictScalars.{u}
          ((sheafCompose K (forget₂ CommRingCat RingCat)).map
            x.aV))).PreservesKInjectiveComplexes := hKV
    exact Functor.PreservesKInjectiveComplexes.isKInjective_map I
  obtain ⟨b0, d0, ordinary⟩ := flatRestriction_ordinary_comparisons x J
  let rU := (x.restrictU J).mapDerivedCategory
  let rV := (x.restrictV J).mapDerivedCategory
  let qU := (x.restrictU J).mapDerivedCategoryFactors
  let qV := (x.restrictV J).mapDerivedCategoryFactors
  obtain ⟨b, hb⟩ := inverse_localization x J LR LS rU rV qLR qLS qU qV b0
  obtain ⟨hd, hn⟩ := flatRestriction_derived_mate x J LR FR qLR ηR aR derivedR computesR
    transposeR LS FS qLS ηS aS derivedS computesS transposeS rU rV qU qV b0 d0 ordinary kU b hb
  let δ := (mateEquiv aS aR (TwoSquare.mk _ _ _ _ b.inv)).natTrans
  have : IsIso δ := hd
  let maps : DerivedRestrictionComparisonMaps x J LR FR LS FS :=
    ⟨b0, d0, rU, rV, qU, qV, b, asIso δ⟩
  refine ⟨hUL, hUC, hVL, hVC, kU, kV, ⟨⟨maps, ordinary, hb, hn, ?_⟩⟩⟩
  intro M N t
  exact adjunct_mate aS aR rV rU b M N t

end FlatRingedDiagramInput
end CategoryTheory
