/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Slice restriction and strict derived limits

Source: Stacks Project, sites-cohomology.tex, Tags 0940 and 0941, with sites-modules.tex,
Tag 03DJ (blueprint: lem-sp-slice-restriction-strict-derived-limit).
-/

@[expose] public section

set_option autoImplicit false

universe u v w r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The levelwise restriction functor on strict towers over a localized site.
Source: sites-modules.tex, Tags 03DJ and 04IX (blueprint:
lem-sp-slice-restriction-strict-derived-limit). -/
noncomputable abbrev sliceTowerRestriction
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C) :
    (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ⥤
      (ℕᵒᵖ ⥤ ringedSiteModules.{r} (Sheaf.over R U)) :=
  (Functor.whiskeringRight (ℕᵒᵖ) (ringedSiteModules.{r} R)
    (ringedSiteModules.{r} (Sheaf.over R U))).obj (SheafOfModules.overFunctor R U)

/-- The derived functor induced by levelwise slice restriction.
Source: sites-modules.tex, Tags 03DJ and 04IX (blueprint:
lem-sp-slice-restriction-strict-derived-limit). -/
noncomputable abbrev sliceTowerDerivedRestriction
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C)
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify (J.over U) AddCommGrpCat.{r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r} (Sheaf.over R U))]
    [(SheafOfModules.overFunctor R U).Additive]
    [PreservesFiniteLimits (sliceTowerRestriction R U)]
    [PreservesFiniteColimits (sliceTowerRestriction R U)] :
    DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ⥤
      DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{r} (Sheaf.over R U)) :=
  (sliceTowerRestriction R U).mapDerivedCategory

/-- Termwise inverse limit of a complex of strict module towers.
Source: Stacks 0940 and 0941 (blueprint: lem-sp-slice-restriction-strict-derived-limit). -/
noncomputable abbrev sliceStrictTowerLimitComplex
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) :=
  (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ⥤
    ringedSiteModules.{r} R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The actual underived restriction/limit comparison, degreewise `limit.post`.
Source: Stacks 04IX and 0940 (blueprint: lem-sp-slice-restriction-strict-derived-limit).
Its components are the maps induced by the restricted limit cone, hence the identity
on compatible tuples. No comparison map is supplied as an arbitrary parameter. -/
noncomputable def sliceStrictTowerLimitComparison
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) (U : C)
    [(SheafOfModules.overFunctor.{r} R U).Additive]
    (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ℤ) :
    ((SheafOfModules.overFunctor R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((sliceStrictTowerLimitComplex R).obj I) ⟶
      (sliceStrictTowerLimitComplex (Sheaf.over R U)).obj
        (((sliceTowerRestriction R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) where
  f i := limit.post (I.X i) (SheafOfModules.overFunctor R U)
  comm' i j _ := (limit.map_post (I.d i j) (SheafOfModules.overFunctor R U)).symm

/-- The canonical nth projection of a termwise strict-tower limit complex.
Source: Stacks 0940 (blueprint: lem-sp-slice-restriction-strict-derived-limit). -/
noncomputable abbrev sliceStrictTowerLimitProjection
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r})
    (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r} R) ℤ) (n : ℕ) :=
  (NatTrans.mapHomologicalComplex
    (lim.π (C := ringedSiteModules.{r} R) (op n)) (ComplexShape.up ℤ)).app I

private theorem slice_commRingSheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v r})
    (hcomm : ∀ (V : Cᵒᵖ) (a b : R.obj.obj V), a * b = b * a) :
    ∃ O : Sheaf J CommRingCat.{max u v r},
      (sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj O = R := by
  let obj (V : Cᵒᵖ) : CommRingCat.{max u v r} :=
    { carrier := R.obj.obj V
      commRing := { (inferInstance : Ring (R.obj.obj V)) with mul_comm := hcomm V } }
  let Oc : Cᵒᵖ ⥤ CommRingCat.{max u v r} :=
    { obj := obj
      map := fun {V W} f ↦
        @CommRingCat.ofHom (obj V) (obj W) (obj V).commRing (obj W).commRing
          (R.obj.map f).hom
      map_id := fun V ↦ by
        apply CommRingCat.hom_ext
        exact congrArg RingCat.Hom.hom (R.obj.map_id V)
      map_comp := fun f g ↦ by
        apply CommRingCat.hom_ext
        exact congrArg RingCat.Hom.hom (R.obj.map_comp f g) }
  have hO : Presheaf.IsSheaf J Oc := by
    apply Presheaf.isSheaf_of_isSheaf_comp J Oc (forget₂ CommRingCat RingCat)
    exact R.property
  exact ⟨⟨Oc, hO⟩, rfl⟩

private theorem slice_kinjective_localization
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w} A]
    (hres : ∀ X : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (q : X ⟶ I),
      I.IsKInjective ∧ QuasiIso q) :
    (CochainComplex.KInjectives.ι ⋙ DerivedCategory.Q.{w}).IsLocalization
      (CochainComplex.KInjectives.quasiIso A) := by
  let QI := CochainComplex.KInjectives.ι ⋙ DerivedCategory.Q.{w} (C := A)
  have : (CochainComplex.KInjectives.toHomotopyCategory ⋙
      HomotopyCategory.KInjectives.Qh (C := A)).Full := inferInstance
  have : QI.Full := Functor.Full.of_iso
    (F := CochainComplex.KInjectives.toHomotopyCategory ⋙
      HomotopyCategory.KInjectives.Qh (C := A))
    (Functor.isoWhiskerLeft CochainComplex.KInjectives.ι
      (DerivedCategory.quotientCompQhIso A))
  have : QI.EssSurj := by
    constructor
    intro Z
    obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Q.{w}) Z
    obtain ⟨I, q, hI, hq⟩ := hres X
    have := hI
    have := hq
    exact ⟨CochainComplex.KInjectives.mk I, ⟨(asIso (DerivedCategory.Q.map q)).symm ≪≫ e⟩⟩
  refine Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders QI
    (CochainComplex.KInjectives.quasiIso A) ?_ ?_
  · intro K L f hf
    have : QuasiIso f.hom := hf
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso A f.hom).mpr inferInstance
  · intro K L f₀ f₁ h
    obtain ⟨K, hK, rfl⟩ := K.mk_surjective
    obtain ⟨L, hL, rfl⟩ := L.mk_surjective
    have := hK
    have := hL
    obtain ⟨f₀, rfl⟩ := ObjectProperty.homMk_surjective f₀
    obtain ⟨f₁, rfl⟩ := ObjectProperty.homMk_surjective f₁
    have h' : (HomotopyCategory.quotient A (.up ℤ)).map f₀ =
        (HomotopyCategory.quotient A (.up ℤ)).map f₁ := by
      apply (CochainComplex.IsKInjective.Qh_map_bijective _ L).injective
      apply (cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app L)).mp
      simp only [DerivedCategory.quotientCompQhIso_hom_naturality]
      exact congrArg (fun f ↦ (DerivedCategory.quotientCompQhIso A).hom.app K ≫ f) h
    let H : Homotopy f₀ f₁ := HomotopyCategory.homotopyOfEq _ _ h'
    refine ⟨K.precylinder.toFullSubcategory (by
      change CochainComplex.IsKInjective (HomologicalComplex.cylinder K)
      infer_instance),
      HomotopicalAlgebra.Precylinder.LeftHomotopy.fullSubcategoryEquiv.symm
        { h := HomologicalComplex.cylinder.desc _ _ H }, ?_⟩
    exact (HomologicalComplex.cylinder.homotopyEquiv K
      (fun n ↦ ⟨n - 1, by simp⟩)).quasiIso_hom

private theorem slice_restriction_properties
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J RingCat.{max u v r})
    (_hcomm : ∀ (V : Cᵒᵖ) (a b : R.obj.obj V), a * b = b * a) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}] :
    ∃ (_hadd : (SheafOfModules.overFunctor.{max u v r} R U).Additive)
      (_hfl : PreservesFiniteLimits (SheafOfModules.overFunctor.{max u v r} R U))
      (_hfc : PreservesFiniteColimits (SheafOfModules.overFunctor.{max u v r} R U))
      (_htl : PreservesFiniteLimits (sliceTowerRestriction R U))
      (_htc : PreservesFiniteColimits (sliceTowerRestriction R U)),
      (sliceTowerRestriction R U).PreservesKInjectiveComplexes ∧
      PreservesLimitsOfShape ℕᵒᵖ (SheafOfModules.overFunctor.{max u v r} R U) := by
  obtain ⟨O, rfl⟩ := slice_commRingSheaf.{u, v, r} R _hcomm
  let R : Sheaf J RingCat.{max u v r} :=
    (sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj O
  have hadd : (SheafOfModules.overFunctor.{max u v r} R U).Additive :=
    SheafOfModules.localizedSystemRestrictionAdditive.{u, v, r} O U
  have hfl : PreservesFiniteLimits (SheafOfModules.overFunctor.{max u v r} R U) :=
    SheafOfModules.localizedSystemRestrictionLimits.{u, v, r} O U
  have hfc : PreservesFiniteColimits (SheafOfModules.overFunctor.{max u v r} R U) :=
    SheafOfModules.localizedSystemRestrictionColimits.{u, v, r} O U
  have htl : PreservesFiniteLimits (sliceTowerRestriction R U) := by
    dsimp [sliceTowerRestriction]
    exact ⟨fun _ ↦ inferInstance⟩
  have htc : PreservesFiniteColimits (sliceTowerRestriction R U) := by
    dsimp [sliceTowerRestriction]
    exact ⟨fun _ ↦ inferInstance⟩
  have adj := (SheafOfModules.localizedSystemAdjunction.{u, v, r} O U).whiskerRight ℕᵒᵖ
  have hel : PreservesFiniteLimits
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
        (SheafOfModules.localizedSystemExtension.{u, v, r} O U)) :=
    ⟨fun _ ↦ inferInstance⟩
  have hec : PreservesFiniteColimits
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
        (SheafOfModules.localizedSystemExtension.{u, v, r} O U)) :=
    ⟨fun _ ↦ inferInstance⟩
  have hta : (sliceTowerRestriction R U).Additive := by
    dsimp [sliceTowerRestriction]
    infer_instance
  have hea : ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (SheafOfModules.localizedSystemExtension.{u, v, r} O U)).Additive := inferInstance
  have hki : (sliceTowerRestriction R U).PreservesKInjectiveComplexes :=
    adj.preservesKInjectiveComplexes
  have hlim : PreservesLimitsOfShape ℕᵒᵖ (SheafOfModules.overFunctor.{max u v r} R U) :=
    (SheafOfModules.localizedSystemAdjunction.{u, v, r} O U).rightAdjoint_preservesLimits
      |>.preservesLimitsOfShape
  exact ⟨hadd, hfl, hfc, htl, htc, hki, hlim⟩

set_option maxHeartbeats 300000 in
-- Resolving the module and tower category instances needs a larger heartbeat budget.
/-- Restriction to a slice commutes canonically with total right derived strict inverse limit.

Source: Stacks 0940 and 0941, with 04IX and 03DJ
(blueprint: lem-sp-slice-restriction-strict-derived-limit).

The existential exactness witnesses express properties of the fixed restrictions, not
additional assumptions. The units and their right-derived universal properties specify
actual total derived limits. They are invertible on K-injective towers. The displayed
normalization specifies the comparison on complexes; the last equation is compatibility
with every derived tower projection on K-injective representatives. Here `n : ℕ` means the
paper's index `n + 1`.

In particular, take any complex representing H and its strict multiplication-by-a tower.
The fixed restriction functor keeps section modules and sends each scalar transition to
multiplication by the restricted scalar. The same comparison therefore gives the stated
multiplication-tower isomorphism for every global a, including zero and one.

Proof:
1. Lift the exact extension-by-zero/restriction adjunction componentwise to strict towers
   (lem-pur-site-restriction-module-adjunction-exact). The Hom bijections are compatible
   with transitions by naturality; exactness is levelwise
   (lem-weil-tower-category-levelwise-abelian). Both fixed restrictions induce derived
   functors, because exactness preserves quasi-isomorphisms.
2. Apply lem-weil-pbc-right-adjoint-preserves-kinjective to the tower adjunction: its
   exact left adjoint makes restriction preserve K-injectivity in the tower category.
3. Ordinary module-sheaf limits are sectionwise compatible tuples. Restriction keeps
   these tuples, so limit.post is an isomorphism and commutes with all projections
   and differentials (def-pur-localized-ringed-site).
4. Use lem-weil-pbc-ringed-strict-tower-homotopy-limit on the original and slice sites
   to obtain the two derived limits and units. For a K-injective resolution q : X → I,
   restricted q is still a quasi-isomorphism with K-injective target. Thus the two
   derived limits are computed by restriction of lim I and by lim of restricted I.
   Step 3 identifies them and gives precisely the normalization below.
5. By lem-weil-pbc-kinjective-hom-derived, maps are homotopy classes of maps between
   K-injective resolutions. The tuple comparison is natural and additive, so respects
   homotopies and descends to the natural isomorphism e, independently of resolution.
6. The nth projection is lim I → I_n; invert the unit and the evaluated resolution
   quasi-isomorphism to get its derived projection. Step 3 proves the last equation.
   Restriction preserves scalar transitions sectionwise. Apply the same result to a
   multiplication-by-a representative tower; levelwise quasi-isomorphisms ensure it
   is independent of the chosen representative of H. -/
theorem sliceRestrictionStrictDerivedLimit
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J RingCat.{max u v r})
    (_hcomm : ∀ (V : Cᵒᵖ) (a b : R.obj.obj V), a * b = b * a) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R)]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r} (Sheaf.over R U))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} (Sheaf.over R U))] :
    ∃ (_hadd : (SheafOfModules.overFunctor.{max u v r} R U).Additive)
      (_hfl : PreservesFiniteLimits (SheafOfModules.overFunctor.{max u v r} R U))
      (_hfc : PreservesFiniteColimits (SheafOfModules.overFunctor.{max u v r} R U))
      (_htl : PreservesFiniteLimits (sliceTowerRestriction R U))
      (_htc : PreservesFiniteColimits (sliceTowerRestriction R U))
      (L : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R) ⥤
        DerivedCategory.{w} (ringedSiteModules.{max u v r} R))
      (LU : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} (Sheaf.over R U)) ⥤
        DerivedCategory.{w} (ringedSiteModules.{max u v r} (Sheaf.over R U)))
      (η : sliceStrictTowerLimitComplex R ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ L)
      (ηU : sliceStrictTowerLimitComplex (Sheaf.over R U) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ LU)
      (e : L ⋙ (SheafOfModules.overFunctor R U).mapDerivedCategory ≅
        sliceTowerDerivedRestriction R U ⋙ LU),
      L.IsRightDerivedFunctor η
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R)
          (ComplexShape.up ℤ)) ∧
      LU.IsRightDerivedFunctor ηU
        (HomologicalComplex.quasiIso
          (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} (Sheaf.over R U)) (ComplexShape.up ℤ)) ∧
      (∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)) ∧
      (∀ I, CochainComplex.IsKInjective I → IsIso (ηU.app I)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R) ℤ),
        (SheafOfModules.overFunctor R U).mapDerivedCategory.map (η.app I) ≫
            e.hom.app (DerivedCategory.Q.obj I) ≫
            LU.map ((sliceTowerRestriction R U).mapDerivedCategoryFactors.hom.app I) =
          (SheafOfModules.overFunctor R U).mapDerivedCategoryFactors.hom.app
              ((sliceStrictTowerLimitComplex R).obj I) ≫
            DerivedCategory.Q.map (sliceStrictTowerLimitComparison R U I) ≫
            ηU.app (((sliceTowerRestriction R U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R) ℤ),
        CochainComplex.IsKInjective I →
        ∃ (_hη : IsIso (η.app I))
          (_hηU : IsIso (ηU.app (((sliceTowerRestriction R U).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I))),
          ∀ n : ℕ,
            e.hom.app (DerivedCategory.Q.obj I) ≫
                LU.map ((sliceTowerRestriction R U).mapDerivedCategoryFactors.hom.app I) ≫
                inv (ηU.app (((sliceTowerRestriction R U).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj I)) ≫
                DerivedCategory.Q.map (sliceStrictTowerLimitProjection (Sheaf.over R U)
                  (((sliceTowerRestriction R U).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj I) n) =
              (SheafOfModules.overFunctor R U).mapDerivedCategory.map (inv (η.app I)) ≫
                (SheafOfModules.overFunctor R U).mapDerivedCategoryFactors.hom.app
                  ((sliceStrictTowerLimitComplex R).obj I) ≫
                DerivedCategory.Q.map
                  (((SheafOfModules.overFunctor R U).mapHomologicalComplex
                    (ComplexShape.up ℤ)).map (sliceStrictTowerLimitProjection R I n))) := by
  obtain ⟨hadd, hfl, hfc, htl, htc, hki, hlim⟩ :=
    slice_restriction_properties.{u, v, r} R _hcomm U
  have hta : (sliceTowerRestriction R U).Additive := by
    dsimp [sliceTowerRestriction]
    infer_instance
  obtain ⟨L, η, hL, hη, hres, _⟩ :=
    ringedStrictTowerHomotopyLimitOfUniverses.{w, u, v, r} J R _hcomm
  have hcommU : ∀ (V : (Over U)ᵒᵖ) (a b : (Sheaf.over R U).obj.obj V),
      a * b = b * a := fun V ↦ _hcomm ((Over.forget U).op.obj V)
  obtain ⟨LU, ηU, hLU, hηU, _, _⟩ :=
    ringedStrictTowerHomotopyLimitOfUniverses.{w, max u v, v, r}
      (J.over U) (Sheaf.over R U) hcommU
  let F := SheafOfModules.overFunctor.{max u v r} R U
  let T := sliceTowerRestriction R U
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let Tc := T.mapHomologicalComplex (ComplexShape.up ℤ)
  let P := CochainComplex.KInjectives.ι (C := ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R)
  let QI := P ⋙ DerivedCategory.Q.{w}
  have hQI : QI.IsLocalization (CochainComplex.KInjectives.quasiIso _) :=
    slice_kinjective_localization hres
  have hcomparison : ∃ c : sliceStrictTowerLimitComplex R ⋙ Fc ≅
      Tc ⋙ sliceStrictTowerLimitComplex (Sheaf.over R U),
      ∀ I, c.hom.app I = sliceStrictTowerLimitComparison R U I := by
    refine ⟨NatIso.mapHomologicalComplex (preservesLimitNatIso F) (ComplexShape.up ℤ), ?_⟩
    intro I
    ext i : 1
    change (preservesLimitIso F (I.X i)).hom = limit.post (I.X i) F
    apply limit.hom_ext
    intro n
    rw [preservesLimitIso_hom_π, limit.post_π]
  obtain ⟨c, hc⟩ := hcomparison
  let α := Functor.whiskerLeft P (Functor.whiskerRight η F.mapDerivedCategory)
  have hαapp : ∀ I, IsIso (α.app I) := by
    intro I
    have := hη I.obj I.property
    change IsIso (F.mapDerivedCategory.map (η.app I.obj))
    infer_instance
  have hα : IsIso α := NatIso.isIso_of_isIso_app α
  let β : P ⋙ sliceStrictTowerLimitComplex R ⋙ DerivedCategory.Q ⋙ F.mapDerivedCategory ⟶
      QI ⋙ (T.mapDerivedCategory ⋙ LU) :=
    Functor.whiskerLeft (P ⋙ sliceStrictTowerLimitComplex R)
        F.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight (Functor.whiskerLeft P c.hom) DerivedCategory.Q ≫
      Functor.whiskerLeft (P ⋙ Tc) ηU ≫
      Functor.whiskerRight (Functor.whiskerLeft P T.mapDerivedCategoryFactors.inv) LU
  have hβapp : ∀ I, IsIso (β.app I) := by
    intro I
    have := I.property
    have hηUI : IsIso (ηU.app ((P ⋙ Tc).obj I)) := by
      change IsIso (ηU.app (Tc.obj I.obj))
      exact hηU _ inferInstance
    dsimp only [β, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  have hβ : IsIso β := NatIso.isIso_of_isIso_app β
  have he_exists : ∃ e : L ⋙ F.mapDerivedCategory ≅ T.mapDerivedCategory ⋙ LU,
      ∀ I : CochainComplex.KInjectives (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R),
        α.app I ≫ e.hom.app (QI.obj I) = β.app I := by
    let e₀ : QI ⋙ (L ⋙ F.mapDerivedCategory) ≅ QI ⋙ (T.mapDerivedCategory ⋙ LU) :=
      (asIso α).symm ≪≫ asIso β
    let ff := Localization.fullyFaithfulWhiskeringLeft QI
      (CochainComplex.KInjectives.quasiIso _) (DerivedCategory.{w}
        (ringedSiteModules.{max u v r} (Sheaf.over R U)))
    refine ⟨ff.preimageIso e₀, ?_⟩
    intro I
    have heq : Functor.whiskerLeft QI (ff.preimageIso e₀).hom = e₀.hom :=
      ff.map_preimage _
    rw [show (ff.preimageIso e₀).hom.app (QI.obj I) = e₀.hom.app I from
      NatTrans.congr_app heq I]
    change α.app I ≫ ((asIso α).inv.app I ≫ β.app I) = β.app I
    exact (asIso α).hom_inv_id_app_assoc I (β.app I)
  obtain ⟨e, he⟩ := he_exists
  refine ⟨hadd, hfl, hfc, htl, htc, L, LU, η, ηU, e, hL, hLU, hη, hηU, ?_, ?_⟩
  · intro I
    let δ : sliceStrictTowerLimitComplex R ⋙ DerivedCategory.Q ⋙ F.mapDerivedCategory ⟶
        DerivedCategory.Q ⋙ (T.mapDerivedCategory ⋙ LU) :=
      Functor.whiskerRight η F.mapDerivedCategory ≫
        Functor.whiskerLeft DerivedCategory.Q e.hom
    let γ : sliceStrictTowerLimitComplex R ⋙ DerivedCategory.Q ⋙ F.mapDerivedCategory ⟶
        DerivedCategory.Q ⋙ (T.mapDerivedCategory ⋙ LU) :=
      Functor.whiskerLeft (sliceStrictTowerLimitComplex R) F.mapDerivedCategoryFactors.hom ≫
        Functor.whiskerRight c.hom DerivedCategory.Q ≫
        Functor.whiskerLeft Tc ηU ≫
        Functor.whiskerRight T.mapDerivedCategoryFactors.inv LU
    have hg (K : CochainComplex.KInjectives
        (ℕᵒᵖ ⥤ ringedSiteModules.{max u v r} R)) : δ.app K.obj = γ.app K.obj := he K
    obtain ⟨K, q, hK, hq⟩ := hres I
    have := hK
    have := hq
    have hdg : δ.app I = γ.app I := by
      have : IsIso (((DerivedCategory.Q ⋙ (T.mapDerivedCategory ⋙ LU)).map q)) := by
        dsimp only [Functor.comp_map]
        infer_instance
      apply (cancel_mono ((DerivedCategory.Q ⋙ (T.mapDerivedCategory ⋙ LU)).map q)).mp
      rw [← δ.naturality, ← γ.naturality, hg (CochainComplex.KInjectives.mk K)]
    have hh := congrArg
      (fun f ↦ f ≫ LU.map (T.mapDerivedCategoryFactors.hom.app I)) hdg
    simp only [δ, γ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc, ← LU.map_comp,
      Iso.inv_hom_id_app] at hh
    dsimp only [Functor.comp_obj, Tc] at hh
    simpa only [Functor.map_id, Category.comp_id, hc] using hh
  · intro I hI
    change ∃ (_hη : IsIso (η.app I)) (_hηU : IsIso (ηU.app (Tc.obj I))),
      ∀ n : ℕ, e.hom.app (DerivedCategory.Q.obj I) ≫
        LU.map (T.mapDerivedCategoryFactors.hom.app I) ≫ inv (ηU.app (Tc.obj I)) ≫
        DerivedCategory.Q.map (sliceStrictTowerLimitProjection
          (Sheaf.over R U) (Tc.obj I) n) =
        F.mapDerivedCategory.map (inv (η.app I)) ≫
          F.mapDerivedCategoryFactors.hom.app ((sliceStrictTowerLimitComplex R).obj I) ≫
          DerivedCategory.Q.map (Fc.map (sliceStrictTowerLimitProjection R I n))
    have := hI
    have hηI := hη I hI
    have hηUI := hηU (Tc.obj I) inferInstance
    refine ⟨hηI, hηUI, ?_⟩
    intro n
    have hprojection : sliceStrictTowerLimitComparison R U I ≫
        sliceStrictTowerLimitProjection (Sheaf.over R U) (Tc.obj I) n =
      Fc.map (sliceStrictTowerLimitProjection R I n) := by
      ext i : 1
      exact limit.post_π (I.X i) F (op n)
    have h := he (CochainComplex.KInjectives.mk I)
    dsimp only [α, β, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] at h
    rw [hc] at h
    change F.mapDerivedCategory.map (η.app I) ≫ e.hom.app (DerivedCategory.Q.obj I) =
      F.mapDerivedCategoryFactors.hom.app ((sliceStrictTowerLimitComplex R).obj I) ≫
        DerivedCategory.Q.map (sliceStrictTowerLimitComparison R U I) ≫
        ηU.app (Tc.obj I) ≫ LU.map (T.mapDerivedCategoryFactors.inv.app I) at h
    have hcan : e.hom.app (DerivedCategory.Q.obj I) ≫
        LU.map (T.mapDerivedCategoryFactors.hom.app I) =
      F.mapDerivedCategory.map (inv (η.app I)) ≫
        F.mapDerivedCategoryFactors.hom.app ((sliceStrictTowerLimitComplex R).obj I) ≫
        DerivedCategory.Q.map (sliceStrictTowerLimitComparison R U I) ≫
        ηU.app (Tc.obj I) := by
      apply (cancel_epi (F.mapDerivedCategory.map (η.app I))).mp
      rw [← Category.assoc, h]
      simp only [Category.assoc, ← LU.map_comp, Iso.inv_hom_id_app,
        Functor.map_inv, IsIso.hom_inv_id_assoc]
      simp only [Functor.map_id, Functor.comp_obj, Tc, Category.comp_id]
    rw [← Category.assoc (e.hom.app _) (LU.map _) _, hcan]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, ← DerivedCategory.Q.map_comp, hprojection]


end CategoryTheory
