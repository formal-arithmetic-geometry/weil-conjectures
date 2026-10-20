/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Sheaf.CategoryTheory.ScalarLocalization
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.CategoryTheory.ScalarLocalizationDerivedHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.CategoryTheory.Preadditive.Opposite


/-!
# Rational degree-zero sheaf Hom comparison

Source: Stacks Project, Cohomology on Sites, Tag 08JI, extended to scalar-localized
retractions as in the proof of the current blueprint `prop-sf-dualizable`.
(blueprint: lem-sf-rational-term-hom-comparison).
The degree-zero identification is normalized by the product projection of the existing
Hom complex. The comparison is explicitly postcomposition with the given resolution.
-/

@[expose] public noncomputable section

set_option autoImplicit false
attribute [local instance 10000] CategoryTheory.functorCategoryPreadditive
attribute [local instance 10000] SheafOfModules.instPreadditive
attribute [local instance 10000] HomologicalComplex.instPreadditive
attribute [local instance 10000] HomologicalComplex.instLinear
attribute [local instance 10000] CategoryTheory.Functor.preservesZeroMorphisms_of_additive


attribute [local irreducible] CategoryTheory.homComplexFunctor
attribute [local irreducible] CategoryTheory.scalarLocalizationCoefficientLinear
set_option backward.isDefEq.respectTransparency true

universe u v w r x y z

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RationalTermHom

/-- A shared proof of coefficient sheaf composition on the small site.
Source: Mathlib's limit-preserving sheaf composition
(blueprint: lem-sf-rational-term-hom-comparison). -/
theorem coefficientCompose {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance

attribute [local instance] coefficientCompose

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})

/-- Sheafification of coefficient groups on the small site.
Source: Mathlib's concrete sheafification
(blueprint: lem-sf-rational-term-hom-comparison). -/
theorem coefficientSheafify : HasSheafify J AddCommGrpCat.{u} := inferInstance

attribute [local instance 10000] coefficientSheafify

/-- Sheafification detects precisely the locally bijective coefficient-group maps.
Source: Mathlib's concrete sheafification
(blueprint: lem-sf-rational-term-hom-comparison). -/
theorem coefficientLocallyBijective : J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstance

attribute [local instance 10000] coefficientLocallyBijective

/-- Module sheaves have a zero object, computed using their sectionwise finite limits.
Source: Mathlib, limits in categories of sheaves of modules
(blueprint: lem-sf-rational-term-hom-comparison). -/
theorem coefficientZero : HasZeroObject (ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) := by
  let : HasFiniteLimits (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :=
    SheafOfModules.Finite.hasFiniteLimits _
  exact hasZeroObject_of_hasTerminal_object

attribute [local instance 10000] coefficientZero

/-- The existing abelian structure of module sheaves, shared across the derived constructions.
Source: Mathlib's abelian category of sheaves of modules
(blueprint: lem-sf-rational-term-hom-comparison). -/
abbrev coefficientAbelian : Abelian (ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) := inferInstance

attribute [local instance 10000] coefficientAbelian

/-- The degree-zero complex of a module sheaf. Source: Stacks, Tag 08JI
(blueprint: lem-sf-rational-term-hom-comparison). -/
def single
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) (0 : ℤ)).obj F

/-- The coefficient sheaf as a module over itself. Source: Stacks, Tag 08JI
(blueprint: lem-sf-rational-term-hom-comparison). -/
def coefficients :
    ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) :=
  SheafOfModules.unit.{u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- The complex B(F) = Hom(F,R)[0]. Source: Stacks, Tag 08JI
(blueprint: lem-sf-rational-term-hom-comparison). -/
def ordinary
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ :=
  single R (SheafOfModules.homObj.{u, u, u, u} (R := R) F (coefficients R))

/-- The complex T(F) = Hom-complex(F[0],I). Source: Stacks, Sections 08J7 and 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
def resolved
    (I : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ :=
  ((homComplexFunctor.{u, u, u, u} (R := R)).obj (op (single R F))).obj I

/-- Precomposition on B. Source: Stacks, Section 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
def ordinaryMap
    {F G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (f : F ⟶ G) : ordinary R G ⟶ ordinary R F :=
  (HomologicalComplex.single (ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ) (0 : ℤ)).map
    (SheafOfModules.homObjMap.{u, u, u, u} (R := R) f (𝟙 (coefficients R)))

/-- Precomposition on T. Source: Stacks, Section 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
def resolvedMap
    (I : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    {F G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (f : F ⟶ G) : resolved R I G ⟶ resolved R I F :=
  ((homComplexFunctor.{u, u, u, u} (R := R)).map
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) (0 : ℤ)).map f).op).app I

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- A compact package for the already chosen Hom-complex projections. The equality
field fixes its data, so choosing this package makes no new choice of projections.
Source: Stacks, Section 0A8X (blueprint: lem-sf-rational-term-hom-comparison). -/
structure ProjectionData where
  value : ∀ (L M : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n p q : ℤ), p + n = q →
      ((((homComplexFunctor.{u, u, u, u} (R := R)).obj (op L)).obj M).X n ⟶
        SheafOfModules.homObj.{u, u, u, u} (R := R) (L.X p) (M.X q))
  eq_chosen : value = Classical.choose
    (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))
  isLimit : ∀ (L M : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (n : ℤ),
    Nonempty (IsLimit (Fan.mk
      ((((homComplexFunctor.{u, u, u, u} (R := R)).obj (op L)).obj M).X n)
      (fun p : ℤ ↦ value L M n p (p + n) rfl)))
  map : ∀ (L L' M M' : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (f : L' ⟶ L) (g : M ⟶ M') (n p q : ℤ) (h : p + n = q),
    ((((homComplexFunctor.{u, u, u, u} (R := R)).map f.op).app M) ≫
      ((homComplexFunctor.{u, u, u, u} (R := R)).obj (op L')).map g).f n ≫
        value L' M' n p q h =
      value L M n p q h ≫
        SheafOfModules.homObjMap.{u, u, u, u} (R := R) (f.f p) (g.f q)

/-- The compact projection package exists with exactly the existing chosen family.
Source: Stacks, Section 0A8X (blueprint: lem-sf-rational-term-hom-comparison).
Proof: put the existing family in the value field, use reflexivity for its equality,
and take both laws from its already proved specification. -/
theorem projectionData_exists : Nonempty (ProjectionData R) := by
  let h := homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R)
  exact ⟨⟨Classical.choose h, rfl, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2.2⟩⟩

/-- The existing product projection, obtained through its compact, uniquely fixed package.
Source: Stacks, Section 0A8X (blueprint: lem-sf-rational-term-hom-comparison). -/
def projection
    (L M : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (((homComplexFunctor.{u, u, u, u} (R := R)).obj (op L)).obj M).X n ⟶
      SheafOfModules.homObj.{u, u, u, u} (R := R) (L.X p) (M.X q) :=
  (Classical.choice (projectionData_exists R)).value L M n p q h

/-- Projection to the (0,0) factor of the existing Hom complex. Its product projections
are those in the specification of `homComplexFunctor`. Source: Stacks, Section 0A8X
(blueprint: lem-sf-rational-term-hom-comparison). -/
def zeroProjection
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    (resolved R (single R (coefficients R)) F).X 0 ⟶
      SheafOfModules.homObj.{u, u, u, u} (R := R) ((single R F).X 0)
        ((single R (coefficients R)).X 0) :=
  projection R (single R F) (single R (coefficients R)) 0 0 0 rfl

/-- The normalized degree-zero identification with the Hom complex. Source: Stacks,
Section 0A8X (blueprint: lem-sf-rational-term-hom-comparison).
The displayed projection is the identity on ordinary local linear maps, transported
through the canonical degree-zero isomorphisms of the single complexes. -/
def IsNormalized
    (e : ∀ F : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ordinary R F ≅ resolved R (single R (coefficients R)) F) : Prop :=
  ∀ F, (e F).hom.f 0 ≫ zeroProjection R F =
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (SheafOfModules.homObj.{u, u, u, u} (R := R) F (coefficients R))).hom ≫
        SheafOfModules.homObjMap.{u, u, u, u} (R := R)
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (coefficients R)).inv

/-- Postcomposition with j, following the normalized identification. Source: Stacks,
Tag 08JI (blueprint: lem-sf-rational-term-hom-comparison). -/
def comparison
    (e : ∀ F : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ordinary R F ≅ resolved R (single R (coefficients R)) F)
    {I : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (j : single R (coefficients R) ⟶ I)
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    ordinary R F ⟶ resolved R I F :=
  (e F).hom ≫ ((homComplexFunctor.{u, u, u, u} (R := R)).obj (op (single R F))).map j

private lemma projection_isLimit
    (L M : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (n : ℤ) :
    Nonempty (IsLimit (Fan.mk
      ((((homComplexFunctor.{u, u, u, u} (R := R)).obj (op L)).obj M).X n)
      (fun p : ℤ ↦ projection R L M n p (p + n) rfl))) :=
  (Classical.choice (projectionData_exists R)).isLimit L M n

private lemma projection_map
    {L L' M M' : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (f : L' ⟶ L) (g : M ⟶ M') (n p q : ℤ) (h : p + n = q) :
    ((((homComplexFunctor.{u, u, u, u} (R := R)).map f.op).app M) ≫
      ((homComplexFunctor.{u, u, u, u} (R := R)).obj (op L')).map g).f n ≫
        projection R L' M' n p q h =
      projection R L M n p q h ≫
        SheafOfModules.homObjMap.{u, u, u, u} (R := R) (f.f p) (g.f q) :=
  (Classical.choice (projectionData_exists R)).map L L' M M' f g n p q h

attribute [local irreducible] projection

private instance homFunctor_additive
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    ((SheafOfModules.homFunctor.{u, u, u, u} R).obj (op F)).Additive where
  map_add := by
    intro X Y f g
    apply SheafOfModules.hom_ext
    ext U φ : 3
    rfl

private lemma soleFactorIsIso {D : Type*} [Category D] [HasZeroMorphisms D]
    {f : ℤ → D} (c : Fan f) (hc : IsLimit c) (i : ℤ)
    (hz : ∀ j, j ≠ i → IsZero (f j)) : IsIso (c.proj i) := by
  classical
  let v := hc.lift (Fan.mk (f i)
    (fun j ↦ if h : j = i then eqToHom (congrArg f h.symm) else 0))
  have hv : v ≫ c.proj i = 𝟙 _ := by
    dsimp [v]
    change hc.lift _ ≫ c.π.app (Discrete.mk i) = _
    rw [hc.fac]
    simp
  refine ⟨⟨v, ?_, hv⟩⟩
  apply Fan.IsLimit.hom_ext hc
  intro j
  by_cases h : j = i
  · subst j
    simp [Category.assoc, hv]
  · exact (hz j h).eq_of_tgt _ _

private abbrev projections := projection R

private lemma resolved_single_isZero
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((resolved R (single R (coefficients R)) F).X n) := by
  let π := projections R
  let c := Fan.mk ((resolved R (single R (coefficients R)) F).X n)
    (fun p : ℤ ↦ π (single R F) (single R (coefficients R)) n p (p + n) rfl)
  have hc : IsLimit c := (projection_isLimit R (single R F) (single R (coefficients R)) n).some
  apply (IsZero.iff_id_eq_zero _).2
  apply Fan.IsLimit.hom_ext hc
  intro p
  have hz : IsZero (SheafOfModules.homObj.{u, u, u, u} (R := R)
      ((single R F).X p) ((single R (coefficients R)).X (p + n))) := by
    by_cases hp : p = 0
    · subst p
      exact ((SheafOfModules.homFunctor.{u, u, u, u} R).obj (op ((single R F).X 0))).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
          (coefficients R) (0 + n) (by simpa using hn))
    · exact ((SheafOfModules.homFunctor.{u, u, u, u} R).flip.obj _).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F p hp).op
  exact hz.eq_of_tgt _ _

private lemma zeroProjection_isIso
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    IsIso (zeroProjection R F) := by
  exact soleFactorIsIso _ (projection_isLimit R (single R F) (single R (coefficients R)) 0).some 0
    (fun p hp ↦ ((SheafOfModules.homFunctor.{u, u, u, u} R).flip.obj _).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F p hp).op)

private def normalizedIso
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    ordinary R F ≅ resolved R (single R (coefficients R)) F := by
  classical
  have : IsIso (zeroProjection R F) := zeroProjection_isIso R F
  let e : ∀ n, (ordinary R F).X n ≅
      (resolved R (single R (coefficients R)) F).X n := fun n ↦
    if h : n = 0 then by
      subst n
      exact (asIso (zeroProjection R F)).symm
    else (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ n h).iso
      (resolved_single_isZero R F n h)
  exact HomologicalComplex.Hom.isoOfComponents e (by
    intro n m hnm
    change n + 1 = m at hnm
    by_cases hn : n = 0
    · have hm : m ≠ 0 := by omega
      exact (resolved_single_isZero R F m hm).eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ n hn).eq_of_src
        _ _)

private lemma normalizedIso_normalized : IsNormalized R (normalizedIso R) := by
  intro F
  have : IsIso (zeroProjection R F) := zeroProjection_isIso R F
  change inv (zeroProjection R F) ≫ zeroProjection R F =
    (𝟙 _) ≫ SheafOfModules.homObjMap.{u, u, u, u} (R := R) (𝟙 F) (𝟙 (coefficients R))
  simp only [IsIso.inv_hom_id, SheafOfModules.homObjMap_id, Category.id_comp]
  rfl

private lemma normalizedIso_zero
    (F : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    (normalizedIso R F).hom.f 0 ≫ zeroProjection R F = 𝟙 _ := by
  have : IsIso (zeroProjection R F) := zeroProjection_isIso R F
  change inv (zeroProjection R F) ≫ zeroProjection R F = 𝟙 _
  simp

set_option backward.isDefEq.respectTransparency false in
private lemma normalizedIso_natural
    {F G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (f : F ⟶ G) :
    ordinaryMap R f ≫ (normalizedIso R F).hom =
      (normalizedIso R G).hom ≫ resolvedMap R (single R (coefficients R)) f := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    have : IsIso (zeroProjection R F) := zeroProjection_isIso R F
    apply (cancel_mono (zeroProjection R F)).1
    simp only [HomologicalComplex.comp_f, Category.assoc, normalizedIso_zero]
    have hp := projection_map R
      (L := single R G) (L' := single R F)
      (M := single R (coefficients R)) (M' := single R (coefficients R))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) (0 : ℤ)).map f) (𝟙 _) 0 0 0 rfl
    simp only [Functor.map_id, Category.comp_id] at hp
    change (resolvedMap R (single R (coefficients R)) f).f 0 ≫ zeroProjection R F =
      zeroProjection R G ≫ SheafOfModules.homObjMap.{u, u, u, u} (R := R)
        (((HomologicalComplex.single _ (ComplexShape.up ℤ) (0 : ℤ)).map f).f 0) (𝟙 _) at hp
    rw [hp, ← Category.assoc, normalizedIso_zero]
    change SheafOfModules.homObjMap.{u, u, u, u} (R := R) f (𝟙 (coefficients R)) ≫ 𝟙 _ =
      𝟙 _ ≫ SheafOfModules.homObjMap.{u, u, u, u} (R := R) f (𝟙 (coefficients R))
    simp
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ n hn).eq_of_src
      _ _

set_option backward.isDefEq.respectTransparency false in
private lemma comparison_natural
    {I : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (j : single R (coefficients R) ⟶ I)
    {F G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (f : F ⟶ G) :
    ordinaryMap R f ≫ comparison R (normalizedIso R) j F =
      comparison R (normalizedIso R) j G ≫ resolvedMap R I f := by
  dsimp only [comparison]
  rw [← Category.assoc, normalizedIso_natural]
  simp only [Category.assoc]
  exact congrArg ((normalizedIso R G).hom ≫ ·)
    (((homComplexFunctor.{u, u, u, u} (R := R)).map
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) (0 : ℤ)).map f).op).naturality j).symm

private abbrev Modules := ringedSiteModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

section CoefficientAction
attribute [local irreducible] coefficients
variable (A : Type v) [CommRing A]
    (a : A →+* RingCat.sectionsSubring
      (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}))

section
attribute [local semireducible] scalarLocalizationCoefficientLinear

set_option backward.isDefEq.respectTransparency false in
private lemma homMap_smul_left :
    (fun [_linear : Linear A (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))] ↦
      ∀ {F G : ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
        (N : ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
        (f : F ⟶ G) (r : A),
        SheafOfModules.homObjMap.{u, u, u, u} (R := R) (r • f) (𝟙 N) =
          r • SheafOfModules.homObjMap.{u, u, u, u} (R := R) f (𝟙 N))
      (_linear := scalarLocalizationCoefficientLinear A R a) := by
  let := scalarLocalizationCoefficientLinear A R a
  intro F G N f r
  apply SheafOfModules.hom_ext
  ext U φ : 3
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  change (φ.app W).hom ((a r).val (op W.unop.left) • (f.val.app _).hom x) =
    (R.obj.map W.unop.hom.op ((a r).val U)) •
      (φ.app W).hom ((f.val.app _).hom x)
  rw [map_smul]
  have h : R.obj.map W.unop.hom.op ((a r).val U) =
      (a r).val (op W.unop.left) := (a r).property W.unop.hom.op
  rw [h]

end

private instance single_linear (V : Type x) [Category.{y} V] [Preadditive V]
    [HasZeroObject V] (A₀ : Type r) [CommRing A₀] [Linear A₀ V] :
    (HomologicalComplex.single V (ComplexShape.up ℤ) 0).Linear A₀ where
  map_smul f r := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.single_map_f_self, HomologicalComplex.smul_f_apply,
      HomologicalComplex.single_map_f_self]
    simp only [Linear.comp_smul, Linear.smul_comp]

private abbrev ordinaryFunctor : (Modules R)ᵒᵖ ⥤ CochainComplex (Modules R) ℤ :=
  ((SheafOfModules.homFunctor.{u, u, u, u} R).flip.obj (coefficients R)) ⋙
    HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0

private abbrev resolvedFunctor (I : CochainComplex (Modules R) ℤ) :
    (Modules R)ᵒᵖ ⥤ CochainComplex (Modules R) ℤ :=
  (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).op ⋙
    ((homComplexFunctor.{u, u, u, u} (R := R)).flip.obj I)

private instance ordinaryFunctor_additive : (ordinaryFunctor R).Additive :=
  inferInstanceAs (((SheafOfModules.homFunctor.{u, u, u, u} R).flip.obj
    (coefficients R)) ⋙ HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).Additive

private lemma ordinaryFunctor_smul_of_smul [Linear A (Modules R)]
    (hHom : ∀ {F G : Modules R} (N : Modules R) (f : F ⟶ G) (r : A),
      SheafOfModules.homObjMap.{u, u, u, u} (R := R) (r • f) (𝟙 N) =
        r • SheafOfModules.homObjMap.{u, u, u, u} (R := R) f (𝟙 N))
    {F G : Modules R} (f : F ⟶ G) (r : A) :
    (ordinaryFunctor R).map (r • f).op = r • (ordinaryFunctor R).map f.op := by
  change (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) (0 : ℤ)).map
    (SheafOfModules.homObjMap.{u, u, u, u} (R := R) (r • f) (𝟙 _)) = _
  rw [hHom]
  exact Functor.map_smul _ r _


private lemma ordinaryFunctor_smul :
    (fun [_linear : Linear A (Modules R)] ↦
      ∀ {F G : Modules R} (f : F ⟶ G) (r : A),
        (ordinaryFunctor R).map (r • f).op = r • (ordinaryFunctor R).map f.op)
      (_linear := scalarLocalizationCoefficientLinear A R a) := by
  let := scalarLocalizationCoefficientLinear A R a
  intro F G f r
  exact ordinaryFunctor_smul_of_smul R A
    (fun N f r ↦ homMap_smul_left R A a N f r) f r

private lemma homComplex_projection_left
    {L L' : (CochainComplex (Modules R) ℤ)ᵒᵖ} {I : CochainComplex (Modules R) ℤ}
    (f : L ⟶ L') (n p q : ℤ) (h : p + n = q) :
    (((homComplexFunctor.{u, u, u, u} (R := R)).map f).app I).f n ≫
      projection R L'.unop I n p q h =
      projection R L.unop I n p q h ≫
        SheafOfModules.homObjMap.{u, u, u, u} (R := R) (f.unop.f p) (𝟙 _) := by
  simpa only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f,
    op_unop, Quiver.Hom.op_unop] using
    projection_map R f.unop (𝟙 I) n p q h

private instance homComplex_left_additive (I : CochainComplex (Modules R) ℤ) :
    ((homComplexFunctor.{u, u, u, u} (R := R)).flip.obj I).Additive where
  map_add {L M} f g := by
    apply HomologicalComplex.hom_ext
    intro n
    apply Fan.IsLimit.hom_ext (projection_isLimit R M.unop I n).some
    intro p
    change (((homComplexFunctor.{u, u, u, u} (R := R)).map (f + g)).app I).f n ≫
        projection R M.unop I n p (p + n) rfl =
      ((((homComplexFunctor.{u, u, u, u} (R := R)).map f).app I).f n +
        (((homComplexFunctor.{u, u, u, u} (R := R)).map g).app I).f n) ≫
          projection R M.unop I n p (p + n) rfl
    have hadd :
        SheafOfModules.homObjMap.{u, u, u, u} (R := R) ((f + g).unop.f p) (𝟙 _) =
          SheafOfModules.homObjMap.{u, u, u, u} (R := R) (f.unop.f p) (𝟙 _) +
            SheafOfModules.homObjMap.{u, u, u, u} (R := R) (g.unop.f p) (𝟙 _) :=
      SheafOfModules.homObjMap_add_left (R := R)
        (f.unop.f p) (g.unop.f p) (𝟙 (I.X (p + n)))
    calc
      _ = projection R L.unop I n p (p + n) rfl ≫
          SheafOfModules.homObjMap.{u, u, u, u} (R := R) ((f + g).unop.f p) (𝟙 _) :=
        homComplex_projection_left R (f + g) n p (p + n) rfl
      _ = projection R L.unop I n p (p + n) rfl ≫
          (SheafOfModules.homObjMap.{u, u, u, u} (R := R) (f.unop.f p) (𝟙 _) +
            SheafOfModules.homObjMap.{u, u, u, u} (R := R) (g.unop.f p) (𝟙 _)) :=
        congrArg (projection R L.unop I n p (p + n) rfl ≫ ·) hadd
      _ = _ := (Preadditive.comp_add _ _ _ _ _ _).trans
        ((congrArg₂ (· + ·)
          (homComplex_projection_left R f n p (p + n) rfl).symm
          (homComplex_projection_left R g n p (p + n) rfl).symm).trans
            (Preadditive.add_comp _ _ _ _ _ _).symm)

private instance resolvedFunctor_additive (I : CochainComplex (Modules R) ℤ) :
    (resolvedFunctor R I).Additive :=
  inferInstanceAs ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) (0 : ℤ)).op ⋙
    (homComplexFunctor.{u, u, u, u} (R := R)).flip.obj I).Additive

private lemma homComplex_left_smul_of_smul [Linear A (Modules R)]
    (hHom : ∀ {F G : Modules R} (N : Modules R) (f : F ⟶ G) (r : A),
      SheafOfModules.homObjMap.{u, u, u, u} (R := R) (r • f) (𝟙 N) =
        r • SheafOfModules.homObjMap.{u, u, u, u} (R := R) f (𝟙 N))
    {L L' I : CochainComplex (Modules R) ℤ} (f : L' ⟶ L) (r : A) :
    ((homComplexFunctor.{u, u, u, u} (R := R)).map (r • f).op).app I =
      r • ((homComplexFunctor.{u, u, u, u} (R := R)).map f.op).app I := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Fan.IsLimit.hom_ext (projection_isLimit R L' I n).some
  intro p
  change (((homComplexFunctor.{u, u, u, u} (R := R)).map (r • f).op).app I).f n ≫
      projection R L' I n p (p + n) rfl =
    (r • (((homComplexFunctor.{u, u, u, u} (R := R)).map f.op).app I).f n) ≫
      projection R L' I n p (p + n) rfl
  calc
    _ = projection R L I n p (p + n) rfl ≫
        SheafOfModules.homObjMap.{u, u, u, u} (R := R) ((r • f).f p) (𝟙 _) :=
      homComplex_projection_left R (r • f).op n p (p + n) rfl
    _ = projection R L I n p (p + n) rfl ≫
        (r • SheafOfModules.homObjMap.{u, u, u, u} (R := R) (f.f p) (𝟙 _)) :=
      congrArg (projection R L I n p (p + n) rfl ≫ ·)
        (hHom _ (f.f p) r)
    _ = r • (projection R L I n p (p + n) rfl ≫
        SheafOfModules.homObjMap.{u, u, u, u} (R := R) (f.f p) (𝟙 _)) :=
      Linear.comp_smul _ _ _ _ r _
    _ = r • ((((homComplexFunctor.{u, u, u, u} (R := R)).map f.op).app I).f n ≫
        projection R L' I n p (p + n) rfl) :=
      congrArg (r • ·) (homComplex_projection_left R f.op n p (p + n) rfl).symm
    _ = _ := (Linear.smul_comp _ _ _ r _ _).symm

private lemma resolvedFunctor_smul_of_smul [Linear A (Modules R)]
    (hHom : ∀ {F G : Modules R} (N : Modules R) (f : F ⟶ G) (r : A),
      SheafOfModules.homObjMap.{u, u, u, u} (R := R) (r • f) (𝟙 N) =
        r • SheafOfModules.homObjMap.{u, u, u, u} (R := R) f (𝟙 N))
    (I : CochainComplex (Modules R) ℤ) {F G : Modules R} (f : F ⟶ G) (r : A) :
    (resolvedFunctor R I).map (r • f).op = r • (resolvedFunctor R I).map f.op := by
  change ((homComplexFunctor.{u, u, u, u} (R := R)).map
    ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) (0 : ℤ)).map (r • f)).op).app I = _
  rw [Functor.map_smul]
  exact homComplex_left_smul_of_smul R A hHom _ r

private lemma resolvedFunctor_smul (I : CochainComplex (Modules R) ℤ) :
    (fun [_linear : Linear A (Modules R)] ↦
      ∀ {F G : Modules R} (f : F ⟶ G) (r : A),
        (resolvedFunctor R I).map (r • f).op = r • (resolvedFunctor R I).map f.op)
      (_linear := scalarLocalizationCoefficientLinear A R a) := by
  let := scalarLocalizationCoefficientLinear A R a
  intro F G f r
  exact resolvedFunctor_smul_of_smul R A
    (fun N f r ↦ homMap_smul_left R A a N f r) I f r

end CoefficientAction

variable [HasDerivedCategory.{w}
  (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]

/-- The image of a complex in the scalar localization of D(R). Source: blueprint,
scalar rationalization (blueprint: lem-sf-rational-term-hom-comparison). -/
def localizedObject (A : Type v) [CommRing A]
    (t : A) (K : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) :
    ScalarLocalization A (DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t :=
  ⟨DerivedCategory.Q.obj K⟩

/-- The image of a chain map in the scalar localization of D(R). Source: blueprint,
scalar rationalization (blueprint: lem-sf-rational-term-hom-comparison). -/
def localizedMap (A : Type v) [CommRing A]
    [Linear A
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    (t : A) {K L : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (f : K ⟶ L) : localizedObject R A t K ⟶ localizedObject R A t L :=
  TensorProduct.tmul A (1 : Localization.Away t) (DerivedCategory.Q.map f)

set_option backward.isDefEq.respectTransparency false in
private lemma free_comparison_iso
    (e : ∀ F : Modules R, ordinary R F ≅ resolved R (single R (coefficients R)) F)
    (I : CochainComplex (Modules R) ℤ) [I.IsKInjective]
    (j : single R (coefficients R) ⟶ I) [QuasiIso j] (m : ℕ) :
    IsIso (DerivedCategory.Q.map (comparison R e j
      (SheafOfModules.free (R := (sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (ULift.{u} (Fin m))))) := by
  let E : Modules R := SheafOfModules.free (ULift.{u} (Fin m))
  have hfinite (n : ℤ) : ∃ r : ℕ, ∃ i : (single R E).X n ⟶
      SheafOfModules.free (R := (sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (ULift.{u} (Fin r)),
      ∃ p : SheafOfModules.free (R := (sheafCompose J
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (ULift.{u} (Fin r)) ⟶
        (single R E).X n, i ≫ p = 𝟙 _ := by
    by_cases hn : n = 0
    · subst n
      exact ⟨m, (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E).hom,
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E).inv,
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 E).hom_inv_id⟩
    · refine ⟨0, 0, 0, ?_⟩
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 E n hn).eq_of_src _ _
  have h := (ringedSite_boundedFree_rhom_model J R
    (single R E) (single R (coefficients R)) 0 0
    (fun n hn ↦ HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 E n
      (by omega))
    (fun n hn ↦ HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (coefficients R) n (by omega)) hfinite).2.1 I j
  change IsIso (DerivedCategory.Q.map ((e E).hom ≫ _))
  rw [Functor.map_comp]
  infer_instance


section Generic
variable {A : Type r} [CommRing A] {D : Type x} [Category.{y} D]
    [Preadditive D] [Linear A D] (t : A)
    {E : Type z} (S B T : E → D)

private def extendAction
    (b : ∀ X Y, (S X ⟶ S Y) →ₗ[A] (B Y ⟶ B X)) (X Y : E) :
    ((⟨S X⟩ : ScalarLocalization A D t) ⟶ ⟨S Y⟩) →ₗ[Localization.Away t]
      ((⟨B Y⟩ : ScalarLocalization A D t) ⟶ ⟨B X⟩) :=
  (b X Y).baseChange (Localization.Away t)

private lemma extendAction_id
    (b : ∀ X Y, (S X ⟶ S Y) →ₗ[A] (B Y ⟶ B X))
    (hb : ∀ X, b X X (𝟙 _) = 𝟙 _) (X : E) :
    extendAction t S B b X X (𝟙 _) = 𝟙 _ := by
  change (b X X).baseChange _ (1 ⊗ₜ[A] 𝟙 _) = 1 ⊗ₜ[A] 𝟙 _
  rw [LinearMap.baseChange_tmul, hb]

private lemma extendAction_comp
    (b : ∀ X Y, (S X ⟶ S Y) →ₗ[A] (B Y ⟶ B X))
    (hb : ∀ X Y Z (f : S X ⟶ S Y) (g : S Y ⟶ S Z),
      b X Z (f ≫ g) = b Y Z g ≫ b X Y f)
    (X Y Z : E)
    (f : (⟨S X⟩ : ScalarLocalization A D t) ⟶ ⟨S Y⟩)
    (g : (⟨S Y⟩ : ScalarLocalization A D t) ⟶ ⟨S Z⟩) :
    extendAction t S B b X Z (f ≫ g) =
      extendAction t S B b Y Z g ≫ extendAction t S B b X Y f := by
  change (b X Z).baseChange _
      (ScalarLocalization.composition A D t (S X) (S Y) (S Z) g f) =
    ScalarLocalization.composition A D t (B Z) (B Y) (B X)
      ((b X Y).baseChange _ f) ((b Y Z).baseChange _ g)
  induction g using TensorProduct.induction_on with
  | zero => simp
  | tmul a g =>
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul c f =>
      simp only [ScalarLocalization.composition_tmul, LinearMap.baseChange_tmul, hb]
      rw [mul_comm a c]
    | add f f' hf hf' => simp [map_add, hf, hf']
  | add g g' hg hg' => simp [map_add, hg, hg']

private lemma extendAction_natural
    (b : ∀ X Y, (S X ⟶ S Y) →ₗ[A] (B Y ⟶ B X))
    (z : ∀ X Y, (S X ⟶ S Y) →ₗ[A] (T Y ⟶ T X))
    (c : ∀ X, B X ⟶ T X)
    (hc : ∀ X Y (f : S X ⟶ S Y), b X Y f ≫ c X = c Y ≫ z X Y f)
    (X Y : E) (f : (⟨S X⟩ : ScalarLocalization A D t) ⟶ ⟨S Y⟩) :
    extendAction t S B b X Y f ≫ (1 ⊗ₜ[A] c X) =
      (1 ⊗ₜ[A] c Y) ≫ extendAction t S T z X Y f := by
  change ScalarLocalization.composition A D t (B Y) (B X) (T X)
      (1 ⊗ₜ[A] c X) ((b X Y).baseChange _ f) =
    ScalarLocalization.composition A D t (B Y) (T Y) (T X)
      ((z X Y).baseChange _ f) (1 ⊗ₜ[A] c Y)
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul a f => simp only [LinearMap.baseChange_tmul, ScalarLocalization.composition_tmul,
      one_mul, mul_one, hc]
  | add f g hf hg => simp [map_add, hf, hg]

end Generic
section FullyFaithful
variable {A : Type r} [CommRing A] {D : Type x} [Category.{y} D]
    [Preadditive D] [Linear A D]
    {M : Type z} [Category M] [Preadditive M] [Linear A M]
    (S : M ⥤ D) [S.Full] [S.Faithful] [S.Additive] [S.Linear A]

private def contraLinear (B : Mᵒᵖ ⥤ D) [B.Additive]
    (hB : ∀ {X Y : M} (f : X ⟶ Y) (a : A), B.map (a • f).op = a • B.map f.op)
    (X Y : M) : (S.obj X ⟶ S.obj Y) →ₗ[A] (B.obj (op Y) ⟶ B.obj (op X)) where
  toFun f := B.map (S.preimage f).op
  map_add' f g := by
    have hp : S.preimage (f + g) = S.preimage f + S.preimage g := by
      apply S.map_injective
      simp
    simp only [hp, op_add, B.map_add]
  map_smul' a f := by
    have hp : S.preimage (a • f) = a • S.preimage f := by
      apply S.map_injective
      simp
    rw [hp, hB]
    rfl

private lemma contraLinear_id (B : Mᵒᵖ ⥤ D) [B.Additive]
    (hB : ∀ {X Y : M} (f : X ⟶ Y) (a : A), B.map (a • f).op = a • B.map f.op)
    (X : M) : contraLinear S B hB X X (𝟙 _) = 𝟙 _ := by
  simp [contraLinear, S.preimage_id]

private lemma contraLinear_comp (B : Mᵒᵖ ⥤ D) [B.Additive]
    (hB : ∀ {X Y : M} (f : X ⟶ Y) (a : A), B.map (a • f).op = a • B.map f.op)
    (X Y Z : M) (f : S.obj X ⟶ S.obj Y) (g : S.obj Y ⟶ S.obj Z) :
    contraLinear S B hB X Z (f ≫ g) =
      contraLinear S B hB Y Z g ≫ contraLinear S B hB X Y f := by
  simp [contraLinear, S.preimage_comp, op_comp]
end FullyFaithful

section Retraction
variable {D : Type x} [Category.{y} D]
    {M : Type z} {S B T : M → D}
    (b : ∀ X Y, (S X ⟶ S Y) → (B Y ⟶ B X))
    (z : ∀ X Y, (S X ⟶ S Y) → (T Y ⟶ T X))
    (hb : ∀ X, b X X (𝟙 _) = 𝟙 _)
    (hz : ∀ X, z X X (𝟙 _) = 𝟙 _)
    (hbc : ∀ X Y Z (f : S X ⟶ S Y) (g : S Y ⟶ S Z),
      b X Z (f ≫ g) = b Y Z g ≫ b X Y f)
    (hzc : ∀ X Y Z (f : S X ⟶ S Y) (g : S Y ⟶ S Z),
      z X Z (f ≫ g) = z Y Z g ≫ z X Y f)
    (c : ∀ X, B X ⟶ T X)
    (hc : ∀ X Y (f : S X ⟶ S Y), b X Y f ≫ c X = c Y ≫ z X Y f)

include b z hb hz hbc hzc hc in
private lemma iso_on_retract (F E : M) (i : S F ⟶ S E) (p : S E ⟶ S F)
    (h : i ≫ p = 𝟙 _) [IsIso (c E)] : IsIso (c F) := by
  have hB : b E F p ≫ b F E i = 𝟙 _ := by rw [← hbc, h, hb]
  have hT : z E F p ≫ z F E i = 𝟙 _ := by rw [← hzc, h, hz]
  refine ⟨⟨z E F p ≫ inv (c E) ≫ b F E i, ?_, ?_⟩⟩
  · calc
      c F ≫ z E F p ≫ inv (c E) ≫ b F E i =
          (c F ≫ z E F p) ≫ inv (c E) ≫ b F E i := by simp [Category.assoc]
      _ = (b E F p ≫ c E) ≫ inv (c E) ≫ b F E i := by rw [hc E F p]
      _ = 𝟙 _ := by simpa [Category.assoc] using hB
  · calc
      (z E F p ≫ inv (c E) ≫ b F E i) ≫ c F =
          z E F p ≫ inv (c E) ≫ (b F E i ≫ c F) := by simp [Category.assoc]
      _ = z E F p ≫ inv (c E) ≫ (c E ≫ z F E i) := by rw [hc F E i]
      _ = 𝟙 _ := by simpa [Category.assoc] using hT
end Retraction

/-- A finite free retract after scalar localization has the expected ordinary dual and
Hom comparison. Source: Stacks, Tag 08JI and the scalar-retraction extension used in
blueprint `prop-sf-dualizable` (blueprint: lem-sf-rational-term-hom-comparison).

Proof:
1. The product Hom formula has only the (0,0) factor for two single complexes.
   Projection to it is an isomorphism; e is its inverse, uniquely normalized above.
   Composing e.hom with Hom(F[0],j) is exactly postcomposition with j.
2. For E = R^m, evaluation on the standard basis identifies c_E with m copies of j.
   Hence it is invertible in D(R), also for m=0; alternatively specialize
   lem-weil-pbc-ringed-site-bounded-free-rhom-model to bounds 0,0.
3. Precomposition commutes with postcomposition with j, so c is natural under every
   module map. Both precomposition actions are A-linear. The A-linear derived Q
   (lem-weil-linear-abelian-derived-category) preserves these equations.
   Full faithfulness of the degree-zero embedding
   (lem-weil-pbc-derived-single-fully-faithful) identifies every degree-zero derived
   map with a module map. Tensoring its Hom maps with A[1/t] therefore extends both
   actions linearly and the naturality square holds on every localized morphism.
4. Apply these contravariant actions to i,p. Naturality and p i = 1 show that
   B(i) c_E^{-1} T(p) is a two-sided inverse of c_F. Similarly B(p),B(i) exhibit
   B(F) as a retract of B(E); the standard-basis duality B(E) ≅ E transports this
   to the asserted retract of the very same free object. No complementary object
   or idempotent completeness is assumed. -/
theorem rational_term_hom_comparison (A : Type v) [CommRing A]
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A)
    (I : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    [I.IsKInjective] (j : single R (coefficients R) ⟶ I) [QuasiIso j] :
    (fun [_linear : Linear A
        (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))] ↦
      ∃ e : ∀ F : ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
          ordinary R F ≅ resolved R (single R (coefficients R)) F,
        IsNormalized R e ∧
        (∀ (F G : ringedSiteModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (f : F ⟶ G),
          ordinaryMap R f ≫ comparison R e j F =
            comparison R e j G ≫ resolvedMap R I f) ∧
        (∀ (F : ringedSiteModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (m : ℕ)
          (i : localizedObject R A t (single R F) ⟶
            localizedObject R A t (single R (SheafOfModules.free
              (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
              (ULift.{u} (Fin m)))))
          (p : localizedObject R A t (single R (SheafOfModules.free
              (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
              (ULift.{u} (Fin m)))) ⟶
            localizedObject R A t (single R F)),
          i ≫ p = 𝟙 _ →
            IsIso (localizedMap R A t (comparison R e j F)) ∧
            ∃ i' : localizedObject R A t (ordinary R F) ⟶
                localizedObject R A t (single R (SheafOfModules.free
                  (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
                  (ULift.{u} (Fin m)))),
              ∃ p' : localizedObject R A t (single R (SheafOfModules.free
                  (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
                  (ULift.{u} (Fin m)))) ⟶ localizedObject R A t (ordinary R F),
                i' ≫ p' = 𝟙 _) ∧
        ∃ b : ∀ F G : ringedSiteModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
            (localizedObject R A t (single R F) ⟶ localizedObject R A t (single R G)) →ₗ[
              Localization.Away t]
              (localizedObject R A t (ordinary R G) ⟶ localizedObject R A t (ordinary R F)),
          ∃ z : ∀ F G : ringedSiteModules.{u}
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
              (localizedObject R A t (single R F) ⟶ localizedObject R A t (single R G)) →ₗ[
                Localization.Away t]
                (localizedObject R A t (resolved R I G) ⟶
                  localizedObject R A t (resolved R I F)),
            (∀ (F G : ringedSiteModules.{u}
                ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (f : F ⟶ G),
              b F G (localizedMap R A t ((CochainComplex.singleFunctor _ 0).map f)) =
                localizedMap R A t (ordinaryMap R f) ∧
              z F G (localizedMap R A t ((CochainComplex.singleFunctor _ 0).map f)) =
                localizedMap R A t (resolvedMap R I f)) ∧
            (∀ (F G : ringedSiteModules.{u}
                ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
              (f : localizedObject R A t (single R F) ⟶ localizedObject R A t (single R G)),
              b F G f ≫ localizedMap R A t (comparison R e j F) =
                localizedMap R A t (comparison R e j G) ≫ z F G f))
      (_linear := scalarLocalizationCoefficientLinear A R a) := by
  let := scalarLocalizationCoefficientLinear A R a
  let M := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let D := DerivedCategory M
  let S : M ⥤ D := DerivedCategory.singleFunctor M 0
  let B : Mᵒᵖ ⥤ D := ordinaryFunctor R ⋙ DerivedCategory.Q
  let T : Mᵒᵖ ⥤ D := resolvedFunctor R I ⋙ DerivedCategory.Q
  have hB : ∀ {F G : M} (f : F ⟶ G) (r : A), B.map (r • f).op = r • B.map f.op := by
    intro F G f r
    change DerivedCategory.Q.map ((ordinaryFunctor R).map (r • f).op) = _
    rw [ordinaryFunctor_smul R A a, Functor.map_smul]
    rfl
  have hT : ∀ {F G : M} (f : F ⟶ G) (r : A), T.map (r • f).op = r • T.map f.op := by
    intro F G f r
    change DerivedCategory.Q.map ((resolvedFunctor R I).map (r • f).op) = _
    rw [resolvedFunctor_smul R A a, Functor.map_smul]
    rfl
  let b₀ := contraLinear S B hB
  let z₀ := contraLinear S T hT
  let c := fun F : M ↦ DerivedCategory.Q.map (comparison R (normalizedIso R) j F)
  have hc : ∀ F G (f : S.obj F ⟶ S.obj G), b₀ F G f ≫ c F = c G ≫ z₀ F G f := by
    intro F G f
    obtain ⟨g, rfl⟩ := S.map_surjective f
    change B.map (S.preimage (S.map g)).op ≫ c F =
      c G ≫ T.map (S.preimage (S.map g)).op
    rw [S.preimage_map]
    change DerivedCategory.Q.map (ordinaryMap R g) ≫
        DerivedCategory.Q.map (comparison R (normalizedIso R) j F) =
      DerivedCategory.Q.map (comparison R (normalizedIso R) j G) ≫
        DerivedCategory.Q.map (resolvedMap R I g)
    rw [← Functor.map_comp, ← Functor.map_comp, comparison_natural]
  let b := extendAction t S.obj (fun F ↦ B.obj (op F)) b₀
  let z := extendAction t S.obj (fun F ↦ T.obj (op F)) z₀
  have hb := extendAction_id t S.obj (fun F ↦ B.obj (op F)) b₀
    (contraLinear_id S B hB)
  have hz := extendAction_id t S.obj (fun F ↦ T.obj (op F)) z₀
    (contraLinear_id S T hT)
  have hbc := extendAction_comp t S.obj (fun F ↦ B.obj (op F)) b₀
    (contraLinear_comp S B hB)
  have hzc := extendAction_comp t S.obj (fun F ↦ T.obj (op F)) z₀
    (contraLinear_comp S T hT)
  have hcn := extendAction_natural t S.obj (fun F ↦ B.obj (op F))
    (fun F ↦ T.obj (op F)) b₀ z₀ c hc
  refine ⟨normalizedIso R, normalizedIso_normalized R, ?_, ?_, b, z, ?_, ?_⟩
  · exact fun F G f ↦ comparison_natural R j f
  · intro F m i p hip
    let E : M := SheafOfModules.free (ULift.{u} (Fin m))
    let L : D ⥤ ScalarLocalization A D t := ScalarLocalization.localization A D t
    let i₀ : (⟨S.obj F⟩ : ScalarLocalization A D t) ⟶ ⟨S.obj E⟩ := i
    let p₀ : (⟨S.obj E⟩ : ScalarLocalization A D t) ⟶ ⟨S.obj F⟩ := p
    have hip₀ : i₀ ≫ p₀ = 𝟙 _ := hip
    let cloc : ∀ X : M, (⟨B.obj (op X)⟩ : ScalarLocalization A D t) ⟶
        ⟨T.obj (op X)⟩ := fun X ↦ L.map (c X)
    have hcE : IsIso (c E) := free_comparison_iso R (normalizedIso R) I j m
    have hclocE : IsIso (cloc E) := by
      change IsIso (L.map (c E))
      infer_instance
    have hcf : IsIso (cloc F) :=
      iso_on_retract (fun X Y f ↦ b X Y f) (fun X Y f ↦ z X Y f)
        hb hz hbc hzc cloc hcn F E i₀ p₀ hip₀
    refine ⟨hcf, ?_⟩
    let d : (⟨B.obj (op E)⟩ : ScalarLocalization A D t) ≅ ⟨S.obj E⟩ :=
      L.mapIso (DerivedCategory.Q.mapIso
        ((CochainComplex.singleFunctor _ 0).mapIso
          (SheafOfModules.homObjFreeUnitIso (R := R) (ULift.{u} (Fin m)))))
    refine ⟨b E F p₀ ≫ d.hom, d.inv ≫ b F E i₀, ?_⟩
    calc
      (b E F p₀ ≫ d.hom) ≫ d.inv ≫ b F E i₀ = b E F p₀ ≫ b F E i₀ := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = b F F (i₀ ≫ p₀) := (hbc F E F i₀ p₀).symm
      _ = 𝟙 _ := by rw [hip₀, hb]
  · intro F G f
    constructor
    · change (b₀ F G).baseChange _ (1 ⊗ₜ[A] S.map f) =
        1 ⊗ₜ[A] DerivedCategory.Q.map (ordinaryMap R f)
      rw [LinearMap.baseChange_tmul]
      change 1 ⊗ₜ[A] B.map (S.preimage (S.map f)).op = _
      rw [S.preimage_map]
      rfl
    · change (z₀ F G).baseChange _ (1 ⊗ₜ[A] S.map f) =
        1 ⊗ₜ[A] DerivedCategory.Q.map (resolvedMap R I f)
      rw [LinearMap.baseChange_tmul]
      change 1 ⊗ₜ[A] T.map (S.preimage (S.map f)).op = _
      rw [S.preimage_map]
      rfl
  · exact hcn

end CategoryTheory.RationalTermHom
