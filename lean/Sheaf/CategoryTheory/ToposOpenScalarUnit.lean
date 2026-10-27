/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.CategoryTheory.RingedPresentationData
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.SixFunctors.OpenTensorNormalizationData
public import Mathlib.CategoryTheory.Subterminal
public import Sheaf.CategoryTheory.ToposOpenScalarBasic
import Sheaf.CategoryTheory.ToposOpenScalarDerivedFromOrdinary
import Sheaf.CategoryTheory.ToposOpenScalarRestriction
import Sheaf.CategoryTheory.ToposOpenUnitIsIso
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction

/-! # Scalar balancing for an arbitrary open subtopos, with its actual unit

Source: Stacks Project, sites-cohomology.tex, Tag 0GL1, and sites-modules.tex,
Tags 0E8I and 04IE (blueprint: lem-pur-topos-open-scalar-unit).
The statement is the coefficient-linear, unit-normalized refinement of 0GL1.
A fixed small presentation identifies the topos with sheaves; the subterminal need
not be represented on that site. Its slice is the existing category-of-elements site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules.ToposOpenScalar

attribute [local instance 0] hasSheafCompose_of_preservesMulticospan
attribute [local instance 20000] hasSheafCompose_of_preservesLimitsOfSize


variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (A : Sheaf J (Type u)) {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)

private abbrev scalarRestriction {D : Type u} [SmallCategory D]
    {K : GrothendieckTopology D} {B T : Sheaf K CommRingCat.{u}} (b : B ⟶ T) :=
  restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map b)

@[irreducible] private def scalarRestrictionSquare :
    scalarRestriction a ⋙ restriction R A ≅
      restriction S A ⋙ scalarRestriction (sliceMap A a) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
    · let X : ModuleCat ((elementRing
          (derivedChangeRingIndependentCoefficients J R) A).obj.obj U) :=
          ((scalarRestriction a ⋙ restriction R A).obj M).val.obj U
      let Y : ModuleCat ((elementRing
          (derivedChangeRingIndependentCoefficients J R) A).obj.obj U) :=
          ((restriction S A ⋙ scalarRestriction (sliceMap A a)).obj M).val.obj U
      change X ≅ Y
      exact { hom := ModuleCat.ofHom (X := X) (Y := Y)
                { toFun := fun m ↦ m
                  map_add' := fun _ _ ↦ rfl
                  map_smul' := fun _ _ ↦ rfl }
              inv := ModuleCat.ofHom (X := Y) (Y := X)
                { toFun := fun m ↦ m
                  map_add' := fun _ _ ↦ rfl
                  map_smul' := fun _ _ ↦ rfl } }
    · intro U V f
      ext m
      rfl
  · intro M N f
    ext U m
    rfl

private theorem scalarRestrictionSquare_apply
    (M : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J S))
    (U : A.obj.Elementsᵒᵖᵒᵖ) (m : M.val.obj ((elementProjection A).op.obj U)) :
    ((scalarRestrictionSquare A a).hom.app M).val.app U m = m := by
  unfold scalarRestrictionSquare
  rfl

variable
  [HasDerivedCategory.{w}
    (ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R))]
  [HasDerivedCategory.{w}
    (ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J S))]
  [HasDerivedCategory.{w} (ringedSiteModules.{u}
    (derivedChangeRingIndependentCoefficients (elementTopology A) (presentationElementRing R A)))]
  [HasDerivedCategory.{w} (ringedSiteModules.{u}
    (derivedChangeRingIndependentCoefficients (elementTopology A) (presentationElementRing S A)))]


private theorem scalarAdjunction
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {B T : Sheaf K CommRingCat.{u}} (b : B ⟶ T)
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients K B))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients K T))]
    (E : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} b) :
    ∃ d : E.E ⊣ scalarRestriction b,
      ∀ (M : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients K B))
        (N : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients K T))
        (g : E.E.obj M ⟶ N) (U : Dᵒᵖ) (m : M.val.obj U),
      (d.homEquiv M N g).val.app U m = g.val.app U (tensorSection b E M U m 1) := by
  obtain ⟨_, _, h⟩ := sheafRingCoefficientOrdinaryAdjunction b
  obtain ⟨d, hd⟩ := h E.E E.obj_eq E.map_eq
  refine ⟨d, ?_⟩
  intro M N g U m
  have he : eqToHom (E.obj_eq M) ≫ (eqToHom (E.obj_eq M).symm ≫ g) = g := by simp
  have hh := hd M N (eqToHom (E.obj_eq M).symm ≫ g) U m
  rw [he] at hh
  exact hh

private theorem tensorSection_smul
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {B T : Sheaf K CommRingCat.{u}} (b : B ⟶ T)
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients K B))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients K T))]
    (E : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} b)
    (M : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients K B))
    (U : Dᵒᵖ) (m : M.val.obj U) (t : T.obj.obj U) :
    tensorSection b E M U m t = t • tensorSection b E M U m 1 := by
  unfold tensorSection
  have ht : t ⊗ₜ[B.obj.obj U, (b.hom.app U).hom] m =
      t • ((1 : T.obj.obj U) ⊗ₜ[B.obj.obj U, (b.hom.app U).hom] m) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [ht]
  erw [map_smul, map_smul]


private theorem ordinaryExtensionComparison
    (ET : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    (EV : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} (sliceMap A a)) :
    ∃ tau : extension R A ⋙ ET.E ≅ EV.E ⋙ extension S A,
      ∀ (M : ringedSiteModules.{u}
          (derivedChangeRingIndependentCoefficients (elementTopology A)
            (presentationElementRing R A)))
        (U : Cᵒᵖ) (f : A.obj.obj U) (m : M.val.obj (elementObj A U f))
        (s : S.obj.obj U),
        (tau.hom.app M).val.app U
            (tensorSection a ET _ U (extensionSection R A M U f m) s) =
          extensionSection S A (EV.E.obj M) U f
            (tensorSection (sliceMap A a) EV M (elementObj A U f) m s) := by
  obtain ⟨aT, hT⟩ := scalarAdjunction a ET
  obtain ⟨aV, hV⟩ := scalarAdjunction (sliceMap A a) EV
  let b := ((normalizedAdjunction R A).comp aT).ofNatIsoRight
    (scalarRestrictionSquare A a)
  let d := aV.comp (normalizedAdjunction S A)
  let tau := b.leftAdjointUniq d
  refine ⟨tau, ?_⟩
  intro M U f m s
  have hc := b.homEquiv_leftAdjointUniq_hom_app d M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hc
  change (normalizedAdjunction R A).homEquiv _ _
      (aT.homEquiv _ _ (tau.hom.app M)) ≫
      (scalarRestrictionSquare A a).hom.app _ = d.unit.app M at hc
  rw [(normalizedAdjunction R A).homEquiv_unit] at hc
  have he := congrArg (fun g ↦ g.val.app (elementObj A U f) m) hc
  change ((scalarRestrictionSquare A a).hom.app _).val.app (elementObj A U f)
    ((aT.homEquiv _ _ (tau.hom.app M)).val.app U
      (((normalizedAdjunction R A).unit.app M).val.app (elementObj A U f) m)) = _ at he
  rw [scalarRestrictionSquare_apply] at he
  change (aT.homEquiv _ _ (tau.hom.app M)).val.app U
    (extensionSection R A M U f m) = (d.unit.app M).val.app (elementObj A U f) m at he
  rw [hT, Adjunction.comp_unit_app] at he
  have hu := hV M (EV.E.obj M) (𝟙 _) (elementObj A U f) m
  rw [Adjunction.homEquiv_unit] at hu
  change (aV.unit.app M).val.app (elementObj A U f) m =
    tensorSection (sliceMap A a) EV M (elementObj A U f) m 1 at hu
  change (tau.hom.app M).val.app U
      (tensorSection a ET _ U (extensionSection R A M U f m) 1) =
    extensionSection S A (EV.E.obj M) U f
      ((aV.unit.app M).val.app (elementObj A U f) m) at he
  rw [hu] at he
  calc
    (tau.hom.app M).val.app U
        (tensorSection a ET _ U (extensionSection R A M U f m) s) =
      s • (tau.hom.app M).val.app U
        (tensorSection a ET _ U (extensionSection R A M U f m) 1) := by
          rw [tensorSection_smul, map_smul]
    _ = s • extensionSection S A (EV.E.obj M) U f
        (tensorSection (sliceMap A a) EV M (elementObj A U f) m 1) := congrArg (s • ·) he
    _ = extensionSection S A (EV.E.obj M) U f
        (s • tensorSection (sliceMap A a) EV M (elementObj A U f) m 1) :=
      (((normalizedAdjunction S A).unit.app (EV.E.obj M)).val.app
        (elementObj A U f)).hom.map_smul s _ |>.symm
    _ = extensionSection S A (EV.E.obj M) U f
        (tensorSection (sliceMap A a) EV M (elementObj A U f) m s) := by
      exact congrArg (extensionSection S A (EV.E.obj M) U f)
        (tensorSection_smul (sliceMap A a) EV M (elementObj A U f) m s).symm


variable
  [(extension R A).Additive]
  [(extension S A).Additive]
  [(restriction R A).Additive]
  [(restriction S A).Additive]
  [PreservesFiniteLimits (extension R A)]
  [PreservesFiniteColimits (extension R A)]
  [PreservesFiniteLimits (extension S A)]
  [PreservesFiniteColimits (extension S A)]
  [PreservesFiniteLimits (restriction R A)]
  [PreservesFiniteColimits (restriction R A)]
  [PreservesFiniteLimits (restriction S A)]
  [PreservesFiniteColimits (restriction S A)]


private theorem adjunct_of_unit
    {B D : Type*} [Category B] [Category D]
    {I : B ⥤ D} {L : D ⥤ B} (d : I ⊣ L)
    {X : B} {Y : D} (e : Y ≅ I.obj X) (f : X ⟶ L.obj Y)
    (h : f ≫ L.map e.hom = d.unit.app X) :
    d.homEquiv X Y e.inv = f := by
  rw [Adjunction.homEquiv_unit, ← h]
  simp only [Category.assoc, ← L.map_comp, e.hom_inv_id, L.map_id, Category.comp_id]

/-- The open scalar isomorphism is induced by ordinary S-linear tensor balancing and
satisfies its normalization by the actual extension units, equivalently its adjunct formula.
Source: Stacks 0GL1, 0E8I and 04IE; the arbitrary-open, S-linear unit refinement is the
agent-formulated refinement recorded in the node (blueprint: lem-pur-topos-open-scalar-unit).

Proof: coefficient restriction commutes with element-site restriction on every
section. Uniqueness of left adjoints identifies extension followed by scalar change
with scalar change followed by extension. Evaluate its Hom-transpose identity on
unit tensor generators, then use S-linearity for arbitrary scalars. Restriction
commutes with sheafification, giving rho and its pure-tensor formula. Subterminality
makes each inhabited summand index set a singleton, so the actual open units are
invertible, also after exact localization. The derived lift of the two ordinary
comparisons supplies lambda, beta and unit coherence. The adjunction Hom formula
and cancellation of beta with its inverse give the final adjunct equation. -/
theorem exists_toposOpenScalarUnit (hA : IsSubterminal A)
    (ET : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    (EV : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} (sliceMap A a)) :
    ∃ (rho : ET.E ⋙ restriction S A ≅
        restriction R A ⋙ EV.E)
      (tau : extension R A ⋙
          ET.E ≅ EV.E ⋙ extension S A)
      (lambda : ET.T ⋙ (restriction S A).mapDerivedCategory.{w, w} ≅
        (restriction R A).mapDerivedCategory.{w, w}
          ⋙ EV.T)
      (beta : (extension R A).mapDerivedCategory.{w, w} ⋙ ET.T ≅
        EV.T ⋙ (extension S A).mapDerivedCategory.{w, w}),
      (∀ (M : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R))
        (U : Cᵒᵖ) (f : A.obj.obj U) (m : M.val.obj U) (s : S.obj.obj U),
        (rho.hom.app M).val.app (elementObj A U f) (tensorSection a ET M U m s) =
          tensorSection (sliceMap A a) EV
            ((restriction R A).obj M)
            (elementObj A U f) m s) ∧
      (∀ (M : ringedSiteModules.{u}
          (derivedChangeRingIndependentCoefficients (elementTopology A) (presentationElementRing
            R A)))
        (U : Cᵒᵖ) (f : A.obj.obj U) (m : M.val.obj (elementObj A U f)) (s : S.obj.obj U),
        (tau.hom.app M).val.app U
            (tensorSection a ET _ U
              (extensionSection R A M U f m) s) =
          extensionSection S A (EV.E.obj M) U f
            (tensorSection (sliceMap A a) EV M (elementObj A U f) m s)) ∧
      (∀ (P : CochainComplex
          (ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R)) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        (restriction S A).mapDerivedCategory.{w, w}.map
            (ET.ε.app P) ≫
          (restriction S A).mapDerivedCategoryFactors.{w, w}.hom.app ((ET.E.mapHomologicalComplex
            (.up ℤ)).obj P) ≫
          DerivedCategory.Q.{w}.map ((NatIso.mapHomologicalComplex rho (.up ℤ)).hom.app P) =
        lambda.hom.app (DerivedCategory.Q.{w}.obj P) ≫
          EV.T.map ((restriction R A).mapDerivedCategoryFactors.{w, w}.hom.app P) ≫
          EV.ε.app (((restriction R A).mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (∀ (P : CochainComplex (ringedSiteModules.{u}
          (derivedChangeRingIndependentCoefficients (elementTopology A) (presentationElementRing
            R A))) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (R := presentationElementRing R A) P →
        ET.T.map ((extension R A).mapDerivedCategoryFactors.{w, w}.hom.app P) ≫
          ET.ε.app (((extension R A).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.{w}.map ((NatIso.mapHomologicalComplex tau (.up ℤ)).hom.app P) =
        beta.hom.app (DerivedCategory.Q.{w}.obj P) ≫
          (extension S A).mapDerivedCategory.{w, w}.map (EV.ε.app P) ≫
          (extension S A).mapDerivedCategoryFactors.{w, w}.hom.app ((EV.E.mapHomologicalComplex
            (.up ℤ)).obj P)) ∧
      IsIso (OpenTensorNormalization.exactDerivedAdjunction.{u + 1, u, w}
        (normalizedAdjunction R A)).unit ∧
      IsIso (OpenTensorNormalization.exactDerivedAdjunction.{u + 1, u, w}
        (normalizedAdjunction S A)).unit ∧
      (∀ M : DerivedCategory (ringedSiteModules.{u}
          (derivedChangeRingIndependentCoefficients (elementTopology A) (presentationElementRing
            R A))),
        EV.T.map ((OpenTensorNormalization.exactDerivedAdjunction.{u + 1, u, w}
          (normalizedAdjunction R A)).unit.app M) ≫
          lambda.inv.app ((extension R A).mapDerivedCategory.{w, w}.obj M) ≫
          (restriction S A).mapDerivedCategory.{w, w}.map (beta.hom.app M) =
        (OpenTensorNormalization.exactDerivedAdjunction.{u + 1, u, w}
        (normalizedAdjunction S A)).unit.app
          (EV.T.obj M)) ∧
      (∀ M : DerivedCategory (ringedSiteModules.{u}
          (derivedChangeRingIndependentCoefficients (elementTopology A) (presentationElementRing
            R A))),
        (OpenTensorNormalization.exactDerivedAdjunction.{u + 1, u, w}
        (normalizedAdjunction S A)).homEquiv
          _ _ (beta.inv.app M) =
        EV.T.map ((OpenTensorNormalization.exactDerivedAdjunction.{u + 1, u, w}
          (normalizedAdjunction R A)).unit.app M) ≫
          lambda.inv.app ((extension R A).mapDerivedCategory.{w, w}.obj M)) := by
  set_option backward.isDefEq.respectTransparency true in
    classical
    have ho : ∃ tau : extension R A ⋙ ET.E ≅ EV.E ⋙ extension S A,
        ∀ (M : ringedSiteModules.{u}
            (derivedChangeRingIndependentCoefficients (elementTopology A)
              (presentationElementRing R A)))
          (U : Cᵒᵖ) (f : A.obj.obj U) (m : M.val.obj (elementObj A U f))
          (t : S.obj.obj U),
          (tau.hom.app M).val.app U
              (tensorSection a ET _ U (extensionSection R A M U f m) t) =
            extensionSection S A (EV.E.obj M) U f
              (tensorSection (sliceMap A a) EV M (elementObj A U f) m t) :=
      ordinaryExtensionComparison A a ET EV
    obtain ⟨tau, htau⟩ := ho
    obtain ⟨rho, hrho⟩ := exists_toposOpenScalarRestriction A a ET EV
    obtain ⟨lambda, beta, hlambda, hbeta, hunit⟩ :=
      exists_toposOpenScalarDerivedFromOrdinary A a ET EV rho hrho tau htau
    have hR := toposOpenDerivedUnit_isIso A R hA
    have hS := toposOpenDerivedUnit_isIso A S hA
    refine ⟨rho, tau, lambda, beta, hrho, htau, hlambda, hbeta, hR, hS, hunit, ?_⟩
    intro M
    set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
        exact adjunct_of_unit
          (OpenTensorNormalization.exactDerivedAdjunction (normalizedAdjunction S A))
          (beta.app M) _ (by
            simpa only [Category.assoc, Iso.app_hom, Functor.comp_obj, Functor.id_obj]
              using hunit M)

end SheafOfModules.ToposOpenScalar
