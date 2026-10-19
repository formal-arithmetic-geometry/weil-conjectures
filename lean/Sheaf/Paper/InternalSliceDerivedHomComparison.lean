/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.InternalSectionDerivedTensorComparison
public import Sheaf.Paper.InternalSectionTotalComparison
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Module objects and derived Hom on a slice

Source: Stacks Project, Tags 03DH, 08J9 and 08JB; Step 5 of the module-object
comparison (blueprint: def-sfb-internal-slice-derived-hom-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.InternalAbelianSheafModule WeilConjectures

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃

/-- The tensor-Hom evaluation comparison, written once with abstract category endpoints.
Source: Stacks 08J9 (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def homEvaluationSquare
    {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
    (t : C × C ⥤ C) (h : Cᵒᵖ × C ⥤ C)
    (ev : ∀ K N : C, t.obj (h.obj (op K, N), K) ⟶ N)
    (f : C ⥤ D) (s : D × D ⥤ D) (H : Dᵒᵖ × D ⥤ D)
    (Ev : ∀ K N : D, s.obj (H.obj (op K, N), K) ⟶ N)
    (tensorIso : t ⋙ f ≅ (f.prod f) ⋙ s)
    (homIso : h ⋙ f ≅ (f.op.prod f) ⋙ H) : Prop :=
  ∀ K N : C,
    f.map (ev K N) = tensorIso.hom.app (h.obj (op K, N), K) ≫
      s.map (X := (f.obj (h.obj (op K, N)), f.obj K))
        (Y := (H.obj (op (f.obj K), f.obj N), f.obj K))
        (homIso.hom.app (op K, N), 𝟙 (f.obj K)) ≫ Ev (f.obj K) (f.obj N)

/-- The restriction square with its section-comparison isomorphisms in both Hom slots.
Source: Stacks 08JB, Step 5
(blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def homRestrictionSquare
    {C : Type u₀} [Category.{v₀} C] {E : Type u₁} [Category.{v₁} E]
    {D : Type u₂} [Category.{v₂} D] {F : Type u₃} [Category.{v₃} F]
    (h : Cᵒᵖ × C ⥤ C) (hu : Eᵒᵖ × E ⥤ E)
    (H : Dᵒᵖ × D ⥤ D) (HU : Fᵒᵖ × F ⥤ F)
    (e : C ⥤ D) (eu : E ⥤ F) (r : C ⥤ E) (rs : D ⥤ F)
    (c : ∀ K : C, eu.obj (r.obj K) ≅ rs.obj (e.obj K))
    (theta : h ⋙ e ≅ (e.op.prod e) ⋙ H)
    (thetaU : hu ⋙ eu ≅ (eu.op.prod eu) ⋙ HU)
    (rho : ∀ K N : D, rs.obj (H.obj (op K, N)) ≅ HU.obj (op (rs.obj K), rs.obj N))
    (restriction : h ⋙ r ≅ (r.op.prod r) ⋙ hu) : Prop :=
  ∀ K N : C,
    eu.map (restriction.hom.app (op K, N)) ≫
      thetaU.hom.app (op (r.obj K), r.obj N) ≫
      HU.map (X := (op (eu.obj (r.obj K)), eu.obj (r.obj N)))
        (Y := (op (rs.obj (e.obj K)), rs.obj (e.obj N)))
        ((c K).inv.op, (c N).hom) =
      (c (h.obj (op K, N))).hom ≫ rs.map (theta.hom.app (op K, N)) ≫
        (rho (e.obj K) (e.obj N)).hom

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (U : X.ProEt)

/-- Literal restriction of the coefficient ring object, with its induced multiplication.
Source: Stacks 03DH (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceRingObject :
    Sheaf ((Scheme.ProEt.topology X).over U) AddCommGrpCat.{u + 1} :=
  ((Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} U).obj
    (condensedRingObj Λ X)

/-- The functor-induced monoid structure, named with instance transparency so
native constructions can reuse it without unfolding the whole restriction functor.
Source: Stacks 03DH (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
@[instance_reducible] instance sliceRingMonObj : MonObj (sliceRingObject Λ X U) :=
  ((Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} U).monObjObj _

/-- Restriction preserves commutativity of the coefficient multiplication.
Source: Stacks 03DH (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
instance sliceRingComm : IsCommMonObj (sliceRingObject Λ X U) :=
  Functor.isCommMonObj_obj
    (F := (Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} U)

/-- Module objects over the restricted ring, on the actual slice site.
Source: Stacks 03DH (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
abbrev SliceInternal := Mod
  (Sheaf ((Scheme.ProEt.topology X).over U) AddCommGrpCat.{u + 1}) (sliceRingObject Λ X U)

/-- Section rings commute with literal restriction.
Source: Stacks 03DH (blueprint: def-sfb-internal-slice-derived-hom-comparison).
Proof: both underlying presheaves send V over U to B(V); their units and products
are the same sectionwise unit and product. Extensionality of ring structures and
presheaf natural transformations identifies the two bundled ring sheaves. -/
theorem sliceSectionRing_eq :
    sectionRingSheaf.{u + 1, u + 1, u} ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U) = (ring Λ X).over U := by
  sorry

/-- The actual section-action equivalence for B restricted to U. Equality transport
changes only the two presentations of its section ring, retaining the functor's data.
Source: Stacks 00YV, 03DH (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceEquivalence : SliceInternal Λ X U ≌ SheafOfModules.{u + 1}
    ((sheafCompose ((Scheme.ProEt.topology X).over U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((ring Λ X).over U)) :=
  Eq.mp (congrArg (fun R ↦ SliceInternal Λ X U ≌ SheafOfModules.{u + 1}
    ((sheafCompose ((Scheme.ProEt.topology X).over U)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (sliceSectionRing_eq Λ X U))
    (sectionModuleEquivalence.{u + 1, u + 1, u} ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U))

/-- The local section equivalence is additive, including equality transport.
Source: Stacks 00YV, 03DH (blueprint: def-sfb-internal-slice-derived-hom-comparison).
Proof: the untransported section functor is additive by comparison_additive.
Eliminate sliceSectionRing_eq to identify the two target presentations; equality
transport preserves the same addition on morphisms. -/
@[instance] theorem sliceEquivalence_additive :
    (sliceEquivalence Λ X U).functor.Additive := by
  sorry

/-- Sectionwise modules over the literally restricted section ring.
Source: Stacks 03DH (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
abbrev SliceModules := SheafOfModules.{u + 1}
  ((sheafCompose ((Scheme.ProEt.topology X).over U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((ring Λ X).over U))

/-- The same exact equivalence on ordinary unbounded derived categories.
Source: Stacks 05RU (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceDerivedEquivalence :
    DerivedCategory (SliceInternal Λ X U) ≌ DerivedCategory (SliceModules Λ X U) :=
  (sliceEquivalence Λ X U).mapDerivedCategory

/-- The direct derived section functor. Naming it avoids unfolding the equivalence
and both its coherence isomorphisms when checking representative endpoints.
Source: Stacks 05RU (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceForward :
    DerivedCategory (SliceInternal Λ X U) ⥤ DerivedCategory (SliceModules Λ X U) :=
  (sliceEquivalence Λ X U).functor.mapDerivedCategory

/-- Termwise extension of the fixed local section-action equivalence.
Source: Stacks 05RU (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceComplexForward :
    CochainComplex (SliceInternal Λ X U) ℤ ⥤ CochainComplex (SliceModules Λ X U) ℤ :=
  (sliceEquivalence Λ X U).functor.mapHomologicalComplex (.up ℤ)

/-- The actual localization comparison for the termwise local section functor.
Source: Stacks 05RU (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceLocalizationIso :
    DerivedCategory.Q ⋙ sliceForward Λ X U ≅
      sliceComplexForward Λ X U ⋙ DerivedCategory.Q :=
  (sliceEquivalence Λ X U).functor.mapDerivedCategoryFactors

/-- Derived module restriction, expressed through the section equivalences. Its
underlying sections and maps are the literal slice restriction, by their counits.
Source: Stacks 03DH, 08JB (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceInternalRestriction :
    DerivedCategory (Internal Λ X) ⥤ DerivedCategory (SliceInternal Λ X U) :=
  forward Λ X ⋙
  ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
    (Scheme.ProEt.topology X) (ring Λ X) U ⋙ (sliceDerivedEquivalence Λ X U).inverse

set_option backward.isDefEq.respectTransparency false in
/-- Fix the existing relative module tensor instance for this actual slice ring.
Source: Stacks 03EK; native Mod.monoidalCategory
(blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
@[instance_reducible, instance] def sliceModuleMonoidal :
    MonoidalCategory (SliceInternal Λ X U) :=
  CategoryTheory.Mod.monoidalCategory

set_option backward.isDefEq.respectTransparency false in
/-- Fix the existing native total tensor instance once for local cochains.
Source: Stacks 06YL; native Mod.monoidalCategoryCochainComplex
(blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
@[instance_reducible, instance] def sliceCochainMonoidal :
    MonoidalCategory (CochainComplex (SliceInternal Λ X U) ℤ) :=
  CategoryTheory.Mod.monoidalCategoryCochainComplex

set_option backward.isDefEq.respectTransparency false in
/-- Fix the existing native K-flat derived tensor instance once on this slice.
Source: Stacks 06YS; native Mod.derivedMonoidalCategory
(blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
@[instance_reducible, instance] def sliceDerivedMonoidal :
    MonoidalCategory (DerivedCategory (SliceInternal Λ X U)) :=
  CategoryTheory.Mod.derivedMonoidalCategory

set_option backward.isDefEq.respectTransparency false in
/-- Fix the existing native derived closed structure, without using ringed Hom.
Source: Stacks 08J9; native DerivedCategory.monoidalClosed
(blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
@[instance_reducible, instance] def sliceDerivedClosed :
    MonoidalClosed (DerivedCategory (SliceInternal Λ X U)) :=
  DerivedCategory.monoidalClosed (SliceInternal Λ X U)

/-- The framework's native local derived internal Hom, independent of the ringed
K-injective model. Source: Stacks 08J9; blueprint derived tensor--Hom
(blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceNativeHom :
    (DerivedCategory (SliceInternal Λ X U))ᵒᵖ ×
      DerivedCategory (SliceInternal Λ X U) ⥤ DerivedCategory (SliceInternal Λ X U) :=
  Functor.uncurry.obj (MonoidalClosed.internalHom
    (C := DerivedCategory (SliceInternal Λ X U)))

/-- The native K-flat derived relative tensor for the actual restricted monoid.
Source: Stacks 06YS (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceNativeTensor :
    DerivedCategory (SliceInternal Λ X U) × DerivedCategory (SliceInternal Λ X U) ⥤
      DerivedCategory (SliceInternal Λ X U) :=
  MonoidalCategory.tensor (DerivedCategory (SliceInternal Λ X U))

/-- The native total tensor on local internal complexes.
Source: Stacks 06YL (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
abbrev sliceTotalTensor (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    CochainComplex (SliceInternal Λ X U) ℤ :=
  (sliceCochainMonoidal Λ X U).tensorObj P Q

set_option backward.isDefEq.respectTransparency false in
/-- Fix the dependency's coproduct instance rather than rediscovering it by search.
Source: Stacks 012Z (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
instance sliceTotalExists (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    P.HasMapBifunctor Q (curriedTensor (SliceInternal Λ X U)) :=
  comparison_internalTotalExists ((Scheme.ProEt.topology X).over U) (sliceRingObject Λ X U) P Q

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary local tensor comparison with the dependency's pure-tensor normalization.
Its target uses the reconstructed presentation of the restricted section ring.
Source: Stacks 03EK (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceOrdinaryTensorIso (M N : SliceInternal Λ X U) :
    (sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U)).functor.obj (M ⊗ N) ≅
    (sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U)).functor.obj M ⊗
    (sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U)).functor.obj N :=
  (internal_section_tensor_comparison ((Scheme.ProEt.topology X).over U)
    (sliceRingObject Λ X U)).2.choose M N

set_option backward.isDefEq.respectTransparency false in
/-- The local sum-total comparison with the dependency's fixed ordinary witness.
Source: Stacks 03EK, 06YL; internal_section_tensor_comparison
(blueprint: def-sfb-internal-slice-derived-hom-comparison).
Proof: specialize the eighth conjunct of internal_section_tensor_comparison to
B restricted to U, retaining the preceding chosen ordinary tensor witness. Its
summand equations are precisely the displayed equations. Each total degree is
a coproduct of these summands, so these equations determine the isomorphism
uniquely, and the ordinary witness is fixed by its pure-tensor formula. -/
theorem sliceRawComplexTensorComparison (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    ∃ t : ((sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
        (sliceRingObject Λ X U)).functor.mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q (curriedTensor (SliceInternal Λ X U))) ≅
      CochainComplex.mapBifunctor
        (((sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
          (sliceRingObject Λ X U)).functor.mapHomologicalComplex (.up ℤ)).obj P)
        (((sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
          (sliceRingObject Λ X U)).functor.mapHomologicalComplex (.up ℤ)).obj Q)
        (curriedTensor _),
      ∀ (p q n : ℤ) (h : p + q = n),
        (sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
          (sliceRingObject Λ X U)).functor.map
            (CochainComplex.ιMapBifunctor P Q (curriedTensor _) p q n h) ≫ t.hom.f n =
          (sliceOrdinaryTensorIso Λ X U (P.X p) (Q.X q)).hom ≫
            CochainComplex.ιMapBifunctor
              (((sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
                (sliceRingObject Λ X U)).functor.mapHomologicalComplex (.up ℤ)).obj P)
              (((sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
                (sliceRingObject Λ X U)).functor.mapHomologicalComplex (.up ℤ)).obj Q)
              (curriedTensor _) p q n h := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- The actual summand-normalized comparison supplied by the dependency. Every
summand equation in sliceRawComplexTensorComparison determines this map uniquely.
Source: Stacks 03EK, 06YL (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceRawComplexTensorIso (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    ((sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U)).functor.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q (curriedTensor (SliceInternal Λ X U))) ≅
    CochainComplex.mapBifunctor
      (((sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
        (sliceRingObject Λ X U)).functor.mapHomologicalComplex (.up ℤ)).obj P)
      (((sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
        (sliceRingObject Λ X U)).functor.mapHomologicalComplex (.up ℤ)).obj Q)
      (curriedTensor _) :=
  (sliceRawComplexTensorComparison Λ X U P Q).choose

/-- The uniquely transported local total comparison, retaining every summand map.
HEq bridges only the explicit/native totals and the two presentations of the same
section ring; it compares with the entire fixed raw isomorphism.
Source: Stacks 03EK, 06YL (blueprint: def-sfb-internal-slice-derived-hom-comparison).
Proof: unfold the native cochain tensor to identify it with the explicit sum total.
Eliminate sliceSectionRing_eq to identify the raw and literal section equivalences.
The sectionwise explicit total is coefficientTotalTensor. Transport the fixed
sliceRawComplexTensorIso across these equalities; equality with this fixed map
after endpoint transport is precisely HEq and determines the result uniquely. -/
theorem sliceTotalComparison_existsUnique (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    ∃! c : (sliceComplexForward Λ X U).obj (sliceTotalTensor Λ X U P Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} ((Scheme.ProEt.topology X).over U)
        ((ring Λ X).over U)).obj
        ((sliceComplexForward Λ X U).obj P, (sliceComplexForward Λ X U).obj Q),
      HEq c (sliceRawComplexTensorIso Λ X U P Q) := by
  sorry

/-- The uniquely summand-normalized local total comparison.
Source: Stacks 03EK, 06YL (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceTotalComparison (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    (sliceComplexForward Λ X U).obj (sliceTotalTensor Λ X U P Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} ((Scheme.ProEt.topology X).over U)
        ((ring Λ X).over U)).obj
        ((sliceComplexForward Λ X U).obj P, (sliceComplexForward Λ X U).obj Q) :=
  (sliceTotalComparison_existsUnique Λ X U P Q).choose

set_option backward.isDefEq.respectTransparency false in
/-- The actual lax localization map for the native local tensor.
Source: Stacks 06YS (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceLocalizationTensorMap (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    (sliceNativeTensor Λ X U).obj
      ((DerivedCategory.Q (C := SliceInternal Λ X U)).obj P,
        (DerivedCategory.Q (C := SliceInternal Λ X U)).obj Q) ⟶
      (DerivedCategory.Q (C := SliceInternal Λ X U)).obj (sliceTotalTensor Λ X U P Q) :=
  Functor.LaxMonoidal.μ (DerivedCategory.Q (C := SliceInternal Λ X U)) P Q

set_option backward.isDefEq.respectTransparency true

/-- Representative normalization of the local derived tensor comparison, for every
pair with K-flat section images. No derived input is required to be flat.
Source: Stacks 06YS, 08J9 (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceTensorComparisonNormalized
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)))
    (TU : CoefficientTensorModels.{u, u + 1, u, u + 1}
      ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) SU)
    (iso : sliceNativeTensor Λ X U ⋙ (sliceForward Λ X U) ≅
      ((sliceForward Λ X U).prod
        (sliceForward Λ X U)) ⋙ SU.tensor) : Prop :=
  ∀ (P Q : CochainComplex (SliceInternal Λ X U) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (J := (Scheme.ProEt.topology X).over U) (R := (ring Λ X).over U)
        ((sliceComplexForward Λ X U).obj P))
      (hQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := (Scheme.ProEt.topology X).over U) (R := (ring Λ X).over U)
        ((sliceComplexForward Λ X U).obj Q)),
    HEq (iso.hom.app ((DerivedCategory.Q (C := SliceInternal Λ X U)).obj P,
        (DerivedCategory.Q (C := SliceInternal Λ X U)).obj Q) ≫
      SU.tensor.map
        (X := ((sliceForward Λ X U).obj
            ((DerivedCategory.Q (C := SliceInternal Λ X U)).obj P),
          (sliceForward Λ X U).obj
            ((DerivedCategory.Q (C := SliceInternal Λ X U)).obj Q)))
        (Y := ((DerivedCategory.Q (C := SliceModules Λ X U)).obj
            ((sliceComplexForward Λ X U).obj P),
          (DerivedCategory.Q (C := SliceModules Λ X U)).obj
            ((sliceComplexForward Λ X U).obj Q)))
        ((sliceLocalizationIso Λ X U).hom.app P, (sliceLocalizationIso Λ X U).hom.app Q))
      ((sliceForward Λ X U).map (sliceLocalizationTensorMap Λ X U P Q) ≫
        (sliceLocalizationIso Λ X U).hom.app (sliceTotalTensor Λ X U P Q) ≫
        (DerivedCategory.Q (C := SliceModules Λ X U)).map
          (sliceTotalComparison Λ X U P Q).hom ≫
        (CoefficientTensorModels.iso.{u, u + 1, u, u + 1}
          ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) SU TU
          ((sliceComplexForward Λ X U).obj P) ((sliceComplexForward Λ X U).obj Q) hP hQ).hom)

/-- Comparison of native local derived tensors, fixed by their K-flat models.
Source: Stacks 06YS, 08J9 (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
structure SliceTensorComparison
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)))
    (TU : CoefficientTensorModels.{u, u + 1, u, u + 1}
      ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) SU) where
  /-- Natural tensor comparison for all local derived objects. -/
  iso : sliceNativeTensor Λ X U ⋙ (sliceForward Λ X U) ≅
    ((sliceForward Λ X U).prod
      (sliceForward Λ X U)) ⋙ SU.tensor
  /-- The localization square with the canonical summand comparison. -/
  normalization : sliceTensorComparisonNormalized Λ X U SU TU iso

set_option backward.isDefEq.respectTransparency false in
/-- The framework's local monoidal structure is its K-flat localization structure.
Source: Stacks 06YS (blueprint: def-sfb-internal-slice-derived-hom-comparison).
Proof: unfold Mod.derivedMonoidalCategory; both instances use the same native
K-flat derivability structure and total tensor, hence identical monoidal data. -/
theorem sliceMonoidal_eq_localization :
    (inferInstance : MonoidalCategory (DerivedCategory (SliceInternal Λ X U))) =
      DerivedMonoidal.instMonoidalCategory DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SliceInternal Λ X U) (.up ℤ)) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- The actual localized Koszul braiding on the native local derived tensor.
Source: Stacks 06YL (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
instance sliceBraiding : BraidedCategory (DerivedCategory (SliceInternal Λ X U)) :=
  Eq.mp (congrArg (fun m ↦ @BraidedCategory (DerivedCategory (SliceInternal Λ X U)) _ m)
    (sliceMonoidal_eq_localization Λ X U).symm)
    (DerivedMonoidal.braidedCategory' DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SliceInternal Λ X U) (.up ℤ)))

/-- The native closed-structure counit, written with Hom as the first tensor factor.
Source: Stacks 08J9 (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceNativeEvaluation (K N : DerivedCategory (SliceInternal Λ X U)) :
    (sliceNativeTensor Λ X U).obj ((sliceNativeHom Λ X U).obj (op K, N), K) ⟶ N :=
  (@BraidedCategory.braiding _ _ _ (sliceBraiding Λ X U)
    ((sliceNativeHom Λ X U).obj (op K, N)) K).hom ≫
      (MonoidalClosed.internalHomAdjunction₂.adj K).counit.app N

/-- The local section functor commutes with restriction through its fixed counit.
Source: Stacks 03DH, 08JB (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceRestrictionSectionIso (K : DerivedCategory (Internal Λ X)) :
    (sliceForward Λ X U).obj ((sliceInternalRestriction Λ X U).obj K) ≅
      (ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) U).obj ((forward Λ X).obj K) :=
  (sliceDerivedEquivalence Λ X U).counitIso.app _

set_option maxHeartbeats 600000 in
-- The dependent counit and restriction equations have large derived-category endpoint types.
/-- The local comparison identifies the native local tensor-Hom counit.
Source: Stacks 08J9, Step 5 (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceHomEvaluationNormalized
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)))
    (TU : CoefficientTensorModels.{u, u + 1, u, u + 1}
      ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) SU)
    (tU : SliceTensorComparison Λ X U SU TU)
    (iso : sliceNativeHom Λ X U ⋙ (sliceForward Λ X U) ≅
    (((sliceForward Λ X U).op).prod
      (sliceForward Λ X U)) ⋙
      derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)) : Prop :=
  homEvaluationSquare (sliceNativeTensor Λ X U) (sliceNativeHom Λ X U)
    (sliceNativeEvaluation Λ X U) (sliceForward Λ X U) SU.tensor
    (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
      ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U))
    SU.evaluation tU.iso iso

set_option maxHeartbeats 600000 in
-- The dependent counit and restriction equations have large derived-category endpoint types.
/-- The module-side restriction is the unique lift of the normalized ringed Hom
square through the local section equivalence, with its canonical counits.
Source: Stacks 08JB, Step 5 (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
def sliceHomRestrictionCompatible
    (S : CoefficientClosedStructure (hom Λ X))
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)))
    (d : RingedSliceEvaluationComparisons (hom Λ X)
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U))
      (ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) U) S SU
      (RingedSliceFlatRestriction.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ring Λ X) U))
    (θ : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
      ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X)
    (iso : sliceNativeHom Λ X U ⋙ (sliceForward Λ X U) ≅
    (((sliceForward Λ X U).op).prod
      (sliceForward Λ X U)) ⋙
      derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U))
    (restriction : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙
      sliceInternalRestriction Λ X U ≅
    ((sliceInternalRestriction Λ X U).op.prod (sliceInternalRestriction Λ X U)) ⋙
      sliceNativeHom Λ X U) : Prop :=
  homRestrictionSquare (Functor.uncurry.obj (CondensedRing.derivedHom Λ X))
    (sliceNativeHom Λ X U) (hom Λ X)
    (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
      ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U))
    (forward Λ X) (sliceForward Λ X U) (sliceInternalRestriction Λ X U)
    (ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
      (Scheme.ProEt.topology X) (ring Λ X) U)
    (sliceRestrictionSectionIso Λ X U) θ iso d.eta restriction

/-- Evaluation-normalized comparison for every local module object, and its
compatibility with restriction of the global comparison. The two named predicates
retain the local counit equation and the full module-object restriction square.
Source: Stacks 08J9, 08JB (blueprint: def-sfb-internal-slice-derived-hom-comparison). -/
structure SliceHomComparison
    (S : CoefficientClosedStructure (hom Λ X))
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)))
    (TU : CoefficientTensorModels.{u, u + 1, u, u + 1}
      ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) SU)
    (tU : SliceTensorComparison Λ X U SU TU)
    (d : RingedSliceEvaluationComparisons (hom Λ X)
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U))
      (ringedSliceDerivedRestriction.{u + 1, u, u, u + 1, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) U) S SU
      (RingedSliceFlatRestriction.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ring Λ X) U))
    (θ : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
      ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X) where
  /-- The comparison on all B|U-module objects, in both derived variables. -/
  iso : sliceNativeHom Λ X U ⋙ (sliceForward Λ X U) ≅
    (((sliceForward Λ X U).op).prod
      (sliceForward Λ X U)) ⋙
      derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)
  /-- The local isomorphism identifies the two actual adjunction counits. -/
  evaluation : sliceHomEvaluationNormalized Λ X U SU TU tU iso
  /-- Restriction of the actual global module-object Hom to the actual local Hom. -/
  restriction : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙
      sliceInternalRestriction Λ X U ≅
    ((sliceInternalRestriction Λ X U).op.prod (sliceInternalRestriction Λ X U)) ⋙
      sliceNativeHom Λ X U
  /-- The module-side restriction and both Hom comparisons form the source square. -/
  compatibility : sliceHomRestrictionCompatible Λ X U S SU d θ iso restriction

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
