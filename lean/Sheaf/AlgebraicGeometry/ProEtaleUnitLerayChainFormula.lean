/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# The ordinary pro-etale unit--Leray chain formula

Source: Stacks Project, sites-cohomology.tex, Tags 07A6, 08J6 and 0D6E;
derived.tex, Tags 070I, 08BJ and 0FND
(blueprint: lem-trf-proetale-unit-leray-chain-formula).

The module and derived units are those of the recorded constant-ring adjunction.
The terminal comparison uses its sectionwise direct image, identified with the canonical
fixed-scalar realization by the published section-normalized comparison. Thus its final
map is evaluation at the actual terminal base change, X times_Y Y = X.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- Global sections, forgetting the locally constant scalar extension by the recorded
realization inverse. The coefficient ring is the common lift of A to the site universe.
Source: Stacks Tag 08J6 (blueprint: lem-trf-proetale-unit-leray-chain-formula). -/
noncomputable def proEtaleUnitLeraySections (X : Scheme.{u}) :=
  (sfIntrinsicModuleEquivalence X A).inverse ⋙
    Sheaf.Γ (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))

/-- Sections are additive, as the composite of the recorded additive functors.
Source: Stacks Tag 08J6 (blueprint: lem-trf-proetale-unit-leray-chain-formula). -/
noncomputable instance proEtaleUnitLeraySections_additive (X : Scheme.{u}) :
    (proEtaleUnitLeraySections A X).Additive :=
  letI := Functor.additive_of_preserves_binary_products
    (Sheaf.Γ (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
  inferInstanceAs (((sfIntrinsicModuleEquivalence X A).inverse ⋙
    Sheaf.Γ (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).Additive)

/-- The recorded direct image is the direct image through the constant-section ring map:
the adjunct of the coefficient comparison is the original coefficient map, by adjunction.
Source: Stacks Tags 03D1 and 0H7J
(blueprint: lem-trf-proetale-unit-leray-chain-formula). -/
noncomputable def proEtaleUnitLerayDirectImageIso {X Y : Scheme.{u}} (h : X ⟶ Y) :
    proEtaleConstantRingPushforward A h ≅ proEtaleConstantModuleDirectImage h A := by
  have he : proEtaleRingDirectImageMap h (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison h A) =
        proEtaleCoefficientDirectImageMap h A := by
    change (proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _
      (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _).symm
        (proEtaleCoefficientDirectImageMap h A)) = _
    exact Equiv.apply_symm_apply _ _
  exact SheafOfModules.pushforwardCongr
    (congrArg (fun (a : proEtaleConstantRing Y A ⟶
      (proEtaleSheafDirectImage h CommRingCat.{u + 1}).obj (proEtaleConstantRing X A)) ↦
      (show ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing Y A)) ⟶
        ((proEtaleBaseChange h).sheafPushforwardContinuous RingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology X)).obj
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (proEtaleConstantRing X A)) from
        ⟨Functor.whiskerRight a.hom (forget₂ CommRingCat RingCat)⟩)) he)

/-- The exact recorded pullback makes its recorded right adjoint preserve K-injectives.
Source: Stacks Tag 08BJ (blueprint: lem-trf-proetale-unit-leray-chain-formula). -/
noncomputable instance proEtaleUnitLerayPushforward_preservesKInjective
    {X Y : Scheme.{u}} (h : X ⟶ Y) :
    (proEtaleConstantRingPushforward A h).PreservesKInjectiveComplexes :=
  (proEtaleConstantRingAdjunction A h).preservesKInjectiveComplexes

/-- Fixed-scalar terminal evaluation, using preservation of the terminal object by base change.
Source: Stacks Tag 08J6 (blueprint: lem-trf-proetale-unit-leray-chain-formula). -/
noncomputable def proEtaleUnitLerayFixedTerminalIso {X Y : Scheme.{u}} (h : X ⟶ Y) :
    ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h ⋙
        Sheaf.Γ (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ≅
      Sheaf.Γ (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :=
  isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _ (terminalIsTerminal (C := Y.ProEt))) ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _) ≪≫
    ((sheafSections _ _).mapIso
      (PreservesTerminal.iso (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h)).op).symm ≪≫
    (Sheaf.ΓNatIsoSheafSections _ _ (terminalIsTerminal (C := X.ProEt))).symm

/-- Terminal-object identification for the recorded direct image. First identify its
coefficient map with the constant-section map by adjunction. The published comparison
is normalized on scalar-unit sections. Cancel the realization equivalences and evaluate
base change at the terminal object, X times_Y Y = X.
Source: Stacks Tag 08J6 (blueprint: lem-trf-proetale-unit-leray-chain-formula). -/
noncomputable def proEtaleUnitLerayTerminalIso {X Y : Scheme.{u}} (h : X ⟶ Y) :
    proEtaleConstantRingPushforward A h ⋙ proEtaleUnitLeraySections A Y ≅
      proEtaleUnitLeraySections A X :=
  isoWhiskerRight (proEtaleUnitLerayDirectImageIso A h) (proEtaleUnitLeraySections A Y) ≪≫
    isoWhiskerRight (sfIntrinsicModuleEquivalence X A).counitIso.symm
      (proEtaleConstantModuleDirectImage h A ⋙ proEtaleUnitLeraySections A Y) ≪≫
    isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
      (isoWhiskerRight (sfIntrinsicDirectImageComparison h A)
        (proEtaleUnitLeraySections A Y)) ≪≫
    isoWhiskerLeft ((sfIntrinsicModuleEquivalence X A).inverse ⋙
      ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h)
        ((sfIntrinsicModuleEquivalence Y A).funInvIdAssoc
          (Sheaf.Γ (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) ≪≫
    isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
      (proEtaleUnitLerayFixedTerminalIso A h)

/-- The canonical Leray comparison, derived from the specified terminal-object isomorphism.
Source: Stacks Tags 08J6 and 0D6E (blueprint: lem-trf-proetale-unit-leray-chain-formula). -/
noncomputable def proEtaleUnitLerayIso {X Y : Scheme.{u}} (h : X ⟶ Y) :=
  Functor.rightDerivedFunctorCompIso' (proEtaleConstantRingPushforward A h)
    (proEtaleUnitLeraySections A Y) (proEtaleUnitLerayTerminalIso A h)

/-- The unit on section complexes, degree by degree, with its canonical terminal comparison.
Source: Stacks Tags 07A6 and 08J6 (blueprint: lem-trf-proetale-unit-leray-chain-formula). -/
noncomputable def proEtaleUnitLeraySectionUnit {X Y : Scheme.{u}} (h : X ⟶ Y) :=
  whiskerRight (proEtaleConstantRingAdjunction A h).unit (proEtaleUnitLeraySections A Y) ≫
    whiskerLeft (proEtaleConstantRingPullback A h) (proEtaleUnitLerayTerminalIso A h).hom

section UnitLerayCalculation

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  {L : D ⥤ C} {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
  [L.Additive] [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [F.PreservesKInjectiveComplexes] (a : L ⊣ F) (e : F ⋙ G ≅ H)

-- The composition comparison carries the composite derived unit to the derived unit.
private lemma unitLerayFac :
    Functor.rightDerivedFunctorCompUnit F G ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso' F G e).hom =
    Functor.whiskerRight
        (NatTrans.mapHomotopyCategory
          e.hom (.up ℤ))
        DerivedCategory.Qh ≫
      H.rightDerivedFunctorUnit := by
  have hc : (F ⋙ G).rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso F G).hom =
      Functor.rightDerivedFunctorCompUnit F G := by
    simp [Functor.rightDerivedFunctorCompIso]
  rw [← hc, Category.assoc, ← Functor.whiskerLeft_comp]
  simp only [Functor.rightDerivedFunctorCompIso',
    Iso.trans_hom, Iso.symm_hom]
  rw [Iso.hom_inv_id_assoc]
  exact Functor.rightDerivedNatTrans_fac
    (F ⋙ G).rightDerivedFunctor
    H.rightDerivedFunctor
    (F ⋙ G).rightDerivedFunctorUnit
    H.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ)) _

-- Compute before inverting units; no K-injectivity is required at this stage.
private lemma unitLerayHomotopy
    (K : HomotopyCategory D (.up ℤ)) :
    G.rightDerivedFunctorUnit.app K ≫
        G.rightDerivedFunctor.map
          (a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Qh.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso' F G e).hom.app
            (L.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
      H.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K) =
      DerivedCategory.Qh.map
        ((G.mapHomotopyCategory (.up ℤ)).map ((a.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
          (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
            ((L.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        H.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj K) := by
  let T := (L.mapHomotopyCategory (.up ℤ)).obj K
  have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso _ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    F.rightDerivedFunctorUnit K
  have hn := (Functor.rightDerivedFunctorCompIso' F G e).hom.naturality
    (L.mapDerivedCategoryFactorsh.hom.app K)
  have hg := G.rightDerivedFunctorUnit.naturality
    ((a.mapHomotopyCategory (.up ℤ)).unit.app K)
  have hc := NatTrans.congr_app (unitLerayFac e) T
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app T =
      𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)) T
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  dsimp only [Functor.comp_map] at hn hg
  dsimp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at hc
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hc
  change DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app T) ≫
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj T) ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app T) ≫
      (Functor.rightDerivedFunctorCompIso' F G e).hom.app (DerivedCategory.Qh.obj T) = _ at hc
  rw [hi, DerivedCategory.Qh.map_id, Category.id_comp] at hc
  erw [← hn]
  erw [← Functor.map_comp_assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  erw [← reassoc_of% hg, hc, ← DerivedCategory.Qh.map_comp_assoc]

-- Naturality in j and inversion of the units at I and J give the chain representative.
private theorem unitLerayChain
    (I : CochainComplex D ℤ)
    (J : CochainComplex C ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (j : (L.mapHomologicalComplex (.up ℤ)).obj I ⟶ J) :
    (G.rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
              (whiskerRight a.unit G ≫ whiskerLeft L e.hom) (.up ℤ)).app I ≫
            (H.mapHomologicalComplex (.up ℤ)).map j) ≫
      (H.rightDerivedFunctorObjQIso J).inv =
    G.rightDerivedFunctor.map
        (a.mapDerivedCategoryRightDerivedAdjunction.unit.app
          (DerivedCategory.Q.obj I)) ≫
      (Functor.rightDerivedFunctorCompIso' F G e).hom.app
        (L.mapDerivedCategory.obj (DerivedCategory.Q.obj I)) ≫
      H.rightDerivedFunctor.map
        (L.mapDerivedCategoryFactors.hom.app I ≫
          DerivedCategory.Q.map j) := by
  let K := (HomotopyCategory.quotient _ (.up ℤ)).obj I
  let U := (L.mapHomotopyCategory (.up ℤ)).obj K
  let v := (G.mapHomologicalComplex (.up ℤ)).map
      ((a.mapHomologicalComplex (.up ℤ)).unit.app I) ≫
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
      ((L.mapHomologicalComplex (.up ℤ)).obj I)
  have hfactor : L.mapDerivedCategoryFactorsh.hom.app K =
      L.mapDerivedCategoryFactors.hom.app I := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
    repeat erw [CategoryTheory.Functor.map_id]
    repeat erw [Category.comp_id]
    repeat erw [Category.id_comp]
  have hquotient : DerivedCategory.Qh.map
      (((G.mapHomotopyCategory (.up ℤ)).map
          ((a.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
        (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app U) ≫
        (H.mapHomotopyCategory (.up ℤ)).map
          ((HomotopyCategory.quotient _ (.up ℤ)).map j)) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (whiskerRight a.unit G ≫ whiskerLeft L e.hom)
          (.up ℤ)).app I ≫ (H.mapHomologicalComplex (.up ℤ)).map j) := by
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
      (v ≫ (H.mapHomologicalComplex (.up ℤ)).map j)) = _
    rfl
  have hc := unitLerayHomotopy a e K
  rw [hfactor] at hc
  have hj := H.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map j)
  dsimp only [Functor.comp_map] at hj
  have hc' := congrArg (fun t ↦ t ≫ H.rightDerivedFunctor.map (DerivedCategory.Q.map j)) hc
  simp only [Category.assoc] at hc'
  erw [← hj, ← DerivedCategory.Qh.map_comp_assoc] at hc'
  erw [hquotient] at hc'
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, asIso_hom, asIso_inv]
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.id_comp]
  repeat erw [Category.comp_id]
  rw [← cancel_epi (G.rightDerivedFunctorUnit.app K)]
  erw [IsIso.hom_inv_id_assoc]
  simp only [Functor.map_comp, Category.assoc] at hc' ⊢
  exact hc'.symm

end UnitLerayCalculation

/-- An arbitrary chain map represents the derived unit--Leray composite on sections.
Source: Stacks Tags 07A6, 08J6, 0D6E, 070I, 08BJ and 0FND
(blueprint: lem-trf-proetale-unit-leray-chain-formula).

The ordinary unit, derived unit and termwise comparison all use the recorded
`proEtaleConstantRingAdjunction` and `proEtaleConstantRingPullback`.

Proof: (1) Direct image preserves K-injectives because its left adjoint is exact
(lem-weil-pbc-right-adjoint-preserves-kinjective); put H = h_* J. Existence of resolutions
and lem-weil-pbc-kinjective-total-derived give the canonical evaluation isomorphisms
on I, J and H, using their identity resolutions.
(2) The termwise adjunction (lem-weil-pbc-termwise-adjunction-homotopy) transposes j
into u = eta_I followed by h_* j. Naturality of the terminal-object comparison gives
Gamma_Y(u) followed by t_J = e_I followed by Gamma_X(j), which is w.
(3) Apply lem-pc-pre-derived-adjoint-functors-general with identity denominators:
the derived adjunct of Q(j) c_I is Q(u) followed by the inverse direct-image comparison.
Thus Rh_*(Q(j) c_I) composed with the derived unit equals that representative.
(4) lem-sf-kinjective-derived-map-computation on the identity resolutions computes
RGamma_Y(Q(u)) as a_I followed by Q(Gamma_Y(u)) followed by a_H inverse.
(5) lem-weil-pbc-ringed-topoi-derived-pushforward-composition for h and the terminal
ringed-topos morphism normalizes Leray at J as a_H followed by Q(t_J) followed by
a_J inverse, after the direct-image comparison. Its naturality moves Q(j) c_I through
Leray. (6) Substitute (3), (5), (4), (2), and cancel comparisons. The resulting arrow
is a_I followed by Q(w) followed by a_J inverse. No step inverts j, u or w. -/
theorem proEtale_unit_leray_chain_formula
    {X Y : Scheme.{u}} (h : X ⟶ Y)
    (I : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ)
    (J : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (j : ((proEtaleConstantRingPullback A h).mapHomologicalComplex (.up ℤ)).obj I ⟶ J) :
    ((proEtaleUnitLeraySections A Y).rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (proEtaleUnitLeraySectionUnit A h) (.up ℤ)).app I ≫
            ((proEtaleUnitLeraySections A X).mapHomologicalComplex (.up ℤ)).map j) ≫
      ((proEtaleUnitLeraySections A X).rightDerivedFunctorObjQIso J).inv =
    (proEtaleUnitLeraySections A Y).rightDerivedFunctor.map
        ((proEtaleConstantRingAdjunction A h).mapDerivedCategoryRightDerivedAdjunction.unit.app
          (DerivedCategory.Q.obj I)) ≫
      (proEtaleUnitLerayIso A h).hom.app
        ((proEtaleConstantRingDerivedPullback A h).obj (DerivedCategory.Q.obj I)) ≫
      (proEtaleUnitLeraySections A X).rightDerivedFunctor.map
        ((proEtaleConstantRingPullback A h).mapDerivedCategoryFactors.hom.app I ≫
          DerivedCategory.Q.map j) := by
  exact unitLerayChain (proEtaleConstantRingAdjunction A h)
    (proEtaleUnitLerayTerminalIso A h) I J j

end AlgebraicGeometry.Scheme
