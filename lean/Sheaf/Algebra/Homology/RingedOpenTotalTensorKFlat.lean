/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.CategoryTheory.RingedSliceExtensionTensor
public import Sheaf.CategoryTheory.RingedSliceExtensionTensorHomData
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Total tensor and K-flatness for ringed slice extension

Source: Stacks Project, Modules on Sites, Tag 0E8I (lemma-j-shriek-and-tensor),
Homology, Tag 012Z, and Cohomology on Sites, Tags 06YN and 06YS
(blueprint: lem-sf-ringed-open-total-tensor-kflat).

The total tensor is Mathlib's direct-sum total cochain complex. Both module functors
are the existing localized-system functors, applied termwise. The site object and
morphism universes remain independent; coefficients live in a universe containing both.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe c v r

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SheafOfModules

variable {S : Type c} [Category.{v} S] {J : GrothendieckTopology S}
  (R : Sheaf J CommRingCat.{max c v r}) (U : S)

/-- The recorded ringed-slice functor, with canonical sheafification instances explicit.
Source: Stacks Project, Modules on Sites, Tags 03DJ and 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenExtension :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  localizedSystemExtension.{c, v, r} R U

/-- The recorded ringed-slice functor, with canonical sheafification instances explicit.
Source: Stacks Project, Modules on Sites, Tags 03DJ and 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenRestriction :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  localizedSystemRestriction.{c, v, r} R U

/-- The recorded ringed-slice functor, with canonical sheafification instances explicit.
Source: Stacks Project, Modules on Sites, Tags 03DJ and 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenSheafTensorLeft :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  ringedSliceTensorLeft.{c, max c r, v} J R U

/-- The recorded ringed-slice functor, with canonical sheafification instances explicit.
Source: Stacks Project, Modules on Sites, Tags 03DJ and 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenSheafTensorRight :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  ringedSliceTensorRight.{c, max c r, v} J R U

/-- Termwise application of the actual direct-sum extension followed by sheafification.
Source: Stacks Project, Modules on Sites, Tags 03DI--03DJ and 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
abbrev ringedOpenExtensionOnComplexes :
    CochainComplex (SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj
        R).over U)) ℤ ⥤
    CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI := localizedSystemExtensionAdditive.{c, v, r} R U
  (localizedSystemExtension.{c, v, r} R U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Termwise restriction to the localized ringed site.
Source: Stacks Project, Modules on Sites, Tags 04IX and 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
abbrev ringedOpenRestrictionOnComplexes :
    CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ ⥤
    CochainComplex (SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj
        R).over U)) ℤ :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI := localizedSystemRestrictionAdditive.{c, v, r} R U
  (localizedSystemRestriction.{c, v, r} R U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The existing sheaf tensor with its coefficient ring specified explicitly.
Source: Stacks Project, Modules on Sites, Section 03EK
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenTensor {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r}) :=
  @curriedTensor (SheafOfModules.{max c v r}
    ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) _
    (cochainModulesMonoidal.{c, v, max c v r} A)

/-- Zero-map preservation for the specified existing tensor.
Source: Stacks Project, Modules on Sites, Section 03EK
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
instance ringedOpenTensorZero {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r}) :
    (ringedOpenTensor.{c, v, r} A).PreservesZeroMorphisms :=
  letI := cochainModulesMonoidal.{c, v, max c v r} A
  letI := cochainModulesPreadditive.{c, v, max c v r} A
  inferInstanceAs ((curriedTensor (SheafOfModules.{max c v r}
    ((sheafCompose K
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A))).PreservesZeroMorphisms)

/-- Zero-map preservation in the second variable of the existing tensor.
Source: Stacks Project, Modules on Sites, Section 03EK
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
instance ringedOpenTensorObjZero {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r})
    (M : SheafOfModules.{max c v r}
      ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) :
    ((ringedOpenTensor.{c, v, r} A).obj M).PreservesZeroMorphisms :=
  letI := cochainModulesMonoidal.{c, v, max c v r} A
  letI := cochainModulesPreadditive.{c, v, max c v r} A
  inferInstanceAs (((curriedTensor (SheafOfModules.{max c v r}
    ((sheafCompose K
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A))).obj M).PreservesZeroMorphisms)

/-- The existing total tensor has the required direct sums on this small ringed site.
Source: Stacks Project, Homology, Tag 012Z
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
instance ringedOpenHasTotalTensor {T : Type c} [Category.{v} T]
    {K : GrothendieckTopology T} (A : Sheaf K CommRingCat.{max c v r})
    (P C : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) ℤ) :
    P.HasMapBifunctor C (ringedOpenTensor.{c, v, r} A) :=
  letI : HasSheafify K AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := K)
  letI : K.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := K)
  inferInstance

/-- The existing total tensor bifunctor, with its canonical instances supplied explicitly.
Source: Stacks Project, Homology, Tag 012Z
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenTotalTensor {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r}) :=
  letI := ringedOpenTensorZero.{c, v, r} A
  letI := ringedOpenTensorObjZero.{c, v, r} A
  letI := ringedOpenHasTotalTensor.{c, v, r} A
  (ringedOpenTensor.{c, v, r} A).map₂CochainComplex

/-- The canonical insertion of one bidegree into the existing direct-sum total tensor.
Source: Stacks Project, Homology, Tag 012Z
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenTensorι {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r})
    (P C : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    ((ringedOpenTensor.{c, v, r} A).obj (P.X p)).obj (C.X q) ⟶
      (((ringedOpenTotalTensor.{c, v, r} A).obj P).obj C).X n :=
  letI := ringedOpenTensorZero.{c, v, r} A
  letI := ringedOpenTensorObjZero.{c, v, r} A
  letI := ringedOpenHasTotalTensor.{c, v, r} A
  CochainComplex.ιMapBifunctor P C (ringedOpenTensor.{c, v, r} A) p q n h

/-- The simultaneous map of the existing total tensor bifunctor on two chain maps.
Source: Stacks Project, Homology, Tag 012Z
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenTotalTensorMap {T : Type c} [Category.{v} T] {K : GrothendieckTopology T}
    (A : Sheaf K CommRingCat.{max c v r})
    {P P' C C' : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose K (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj A)) ℤ}
    (a : P ⟶ P') (b : C ⟶ C') :
    ((ringedOpenTotalTensor.{c, v, r} A).obj P).obj C ⟶
      ((ringedOpenTotalTensor.{c, v, r} A).obj P').obj C' :=
  (((ringedOpenTotalTensor.{c, v, r} A).map a).app C) ≫
    ((ringedOpenTotalTensor.{c, v, r} A).obj P').map b

/-- The recorded sheaf comparison, expressed in the existing monoidal tensor.
Source: Stacks Project, Modules on Sites, Tag 0E8I
(blueprint: lem-sf-ringed-open-total-tensor-kflat). -/
def ringedOpenSheafComparison
    (θ : ringedOpenSheafTensorLeft.{c, v, r} R U ≅
      ringedOpenSheafTensorRight.{c, v, r} R U)
    (M : SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U))
    (N : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
    (ringedOpenExtension.{c, v, r} R U).obj
        (((ringedOpenTensor.{max c v, v, r} (R.over U)).obj M).obj
          ((ringedOpenRestriction.{c, v, r} R U).obj N)) ≅
      ((ringedOpenTensor.{c, v, r} R).obj
        ((ringedOpenExtension.{c, v, r} R U).obj M)).obj N :=
  letI : HasSheafify J AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    hasSheafify_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  letI : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{c, v, max c v r} (J := J)
  letI : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} :=
    wEqualsLocallyBijective_coefficientUniverse.{max c v, v, max c v r} (J := J.over U)
  letI := cochainTensorLocalizationIsMonoidal.{c, v, max c v r} R
  letI := cochainTensorLocalizationIsMonoidal.{max c v, v, max c v r} (R.over U)
  (ringedOpenExtension.{c, v, r} R U).mapIso
      (tensorObjIsoSheafification.{v, max c v, max c v r} (R := R.over U) M
        ((ringedOpenRestriction.{c, v, r} R U).obj N)) ≪≫
    θ.app (M, N) ≪≫
    (tensorObjIsoSheafification.{v, c, max c v r} (R := R)
      ((ringedOpenExtension.{c, v, r} R U).obj M) N).symm

/-- The sheaf tensor comparison extends to unbounded direct-sum total tensor complexes,
with its prescribed map on every summand and naturality in both chain maps. Extension
also preserves K-flat complexes and K-flat resolutions.

Source: Stacks Project, Modules on Sites, Tag 0E8I (lemma-j-shriek-and-tensor),
Homology, Tags 012Z and 010N, and Cohomology on Sites, Tags 06YN and 06YS
(blueprint: lem-sf-ringed-open-total-tensor-kflat).

Proof:
1. In each degree n use the extension/restriction adjunction
   (lem-pur-site-restriction-module-adjunction-exact) and preservation of colimits by
   a left adjoint (lem-weil-pbc-left-adjoint-preserves-colimits) to commute extension
   with the sum over p+q=n. Compose the inverse coproduct comparison with the sum of
   the sheaf tensor isomorphisms (lem-weil-pbc-ringed-slice-extension-tensor). This
   gives precisely the displayed equation on each insertion of a tensor summand.
2. Naturality of the sheaf comparison for (d_P,1) and (1,d_C) identifies the two
   differential components. Additivity of extension preserves the sign (-1)^p.
   Thus these degreewise isomorphisms commute with d_P tensor 1 + (-1)^p 1 tensor d_C
   (def-pc-tensor-complex-sheaves). The same equations for arbitrary chain maps give
   the displayed naturality. Each source summand has just these two differential
   components, so no infinite sum into a fixed summand occurs.
3. The tensor symmetry sends the (a,b) summand to (b,a), multiplying the ordinary
   sheaf tensor interchange (def-pur-sheaf-tensor-product) by (-1)^(ab). For dy tensor x
   the two differential coefficients are (-1)^(ab), and for y tensor dx they are
   (-1)^(ab+b)=(-1)^((a+1)b). The composite of two interchanges is the identity.
4. For acyclic C, exact restriction makes j^*C acyclic by the natural homology
   comparison (lem-sp-exact-functor-preserves-homology). K-flatness of P makes
   Tot(j^*C tensor P) acyclic (def-pc-kflat-complex). Apply the signed interchange,
   exact extension, the total comparison, and the signed interchange again. This
   proves Tot(C tensor j_!P) acyclic, the defining K-flatness test.
5. For a K-flat resolution f:P -> H, exact extension preserves the quasi-isomorphism:
   the homology comparison identifies H^n(j_!f) with j_!H^n(f), which is invertible.
   Step 4 supplies K-flatness of its source. All sums are direct sums indexed by
   integer pairs; neither boundedness nor constancy of R has been used. -/
theorem ringedOpen_totalTensor_kFlat :
    (∃ θ : ringedOpenSheafTensorLeft.{c, v, r} R U ≅
        ringedOpenSheafTensorRight.{c, v, r} R U,
      ∃ Φ : ∀ (P : CochainComplex (SheafOfModules.{max c v r}
          (((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ)
          (C : CochainComplex (SheafOfModules.{max c v r}
            ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ),
        (ringedOpenExtensionOnComplexes.{c, v, r} R U).obj
            (((ringedOpenTotalTensor.{max c v, v, r} (R.over U)).obj P).obj
              ((ringedOpenRestrictionOnComplexes.{c, v, r} R U).obj C)) ≅
          ((ringedOpenTotalTensor.{c, v, r} R).obj
            ((ringedOpenExtensionOnComplexes.{c, v, r} R U).obj P)).obj C,
      (∀ P C (p q n : ℤ) (h : p + q = n),
        (ringedOpenExtension.{c, v, r} R U).map
            (ringedOpenTensorι.{max c v, v, r} (R.over U) P
              ((ringedOpenRestrictionOnComplexes.{c, v, r} R U).obj C) p q n h) ≫
            (Φ P C).hom.f n =
          (ringedOpenSheafComparison.{c, v, r} R U θ (P.X p) (C.X q)).hom ≫
            ringedOpenTensorι.{c, v, r} R
              ((ringedOpenExtensionOnComplexes.{c, v, r} R U).obj P) C p q n h) ∧
      (∀ P P' C C' (a : P ⟶ P') (b : C ⟶ C'),
        (ringedOpenExtensionOnComplexes.{c, v, r} R U).map
            (ringedOpenTotalTensorMap.{max c v, v, r} (R.over U) a
              ((ringedOpenRestrictionOnComplexes.{c, v, r} R U).map b)) ≫ (Φ P' C').hom =
          (Φ P C).hom ≫ ringedOpenTotalTensorMap.{c, v, r} R
            ((ringedOpenExtensionOnComplexes.{c, v, r} R U).map a) b)) ∧
    (∀ P : CochainComplex (SheafOfModules.{max c v r}
        (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := R.over U) P →
        CochainComplex.IsKFlatIndependentCoefficients (R := R)
          ((ringedOpenExtensionOnComplexes.{c, v, r} R U).obj P)) ∧
    (∀ (P H : CochainComplex (SheafOfModules.{max c v r}
        (((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U)) ℤ) (f : P ⟶ H),
      CochainComplex.IsKFlatResolutionIndependentCoefficients (R := R.over U) f →
        CochainComplex.IsKFlatResolutionIndependentCoefficients (R := R)
          ((ringedOpenExtensionOnComplexes.{c, v, r} R U).map f)) := by
  sorry

end SheafOfModules
