/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.CondensedScalarRealization
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsDerived
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

import Sheaf.Paper.CondensedAffineOrdinaryScalarSections
import Sheaf.CategoryTheory.ConstantModuleKFlat
import Sheaf.CategoryTheory.DerivedCategory.NormalizedLeftExtension
import all Sheaf.RingTheory.DerivedModuleScalarAdjunction
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutionsExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Condensed scalar extension on w-contractible affines

Source: Hemo–Richarz–Scholbach, Section 3, equations (3.1), (3.2), Remark 3.2;
Lemma 4.1(1), Proposition 4.3(1)
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation).

The scalar ring, canonical scalar map and scalar realization are imported from
`Sheaf.AlgebraicGeometry.CondensedScalarRealization`. The only coefficient transport
is the existing equivalence between internal and sectionwise module sheaves.

## Main definitions

- `condensedCoefficientRing`: section rings of the recorded internal coefficient object.
- `condensedSectionModuleTransport`: the existing module equivalence on derived categories.
- `condensedDerivedSections`: the existing unbounded K-injective section functor.
- `scalarAffineComponents`: the actual profinite component quotient.

## Main statements

- `wContractible_condensed_scalar_evaluation`: coefficient and derived comparisons,
  naturality on D(R), and t-exactness of derived sections on the affine.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u wS wB
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Section rings of the existing internal coefficient pullback Λ_X.
Source: HRS, Section 3; Stacks, Tag 00YV
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
abbrev condensedCoefficientRing (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj.{u} Λ X))

/-- The existing exact internal/sectionwise module equivalence, localized termwise.
This changes only the presentation of modules, not the scalar realization.
Source: Stacks, Tag 00YV; HRS, equation (3.1)
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
def condensedSectionModuleTransport (X : Scheme.{u})
    [HasDerivedCategory.{wS} (SheafOfModules.{u + 1} (condensedCoefficientRing Λ X))] :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj.{u} Λ X)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (condensedCoefficientRing Λ X)) :=
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj.{u} Λ X)
  haveI := Functor.additive_of_preserves_binary_products e.functor
  e.functor.mapDerivedCategory

/-- Unbounded derived sections at a site object, defined by the existing K-injective
right-derived construction. This is RΓ(U,-|_U): restriction to the slice followed by
sections has precisely this sectionwise evaluation functor.
Source: HRS, Section 3, equation (3.2)
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
def condensedDerivedSections (X : Scheme.{u}) (U : X.ProEt)
    [HasDerivedCategory.{wS} (SheafOfModules.{u + 1} (condensedCoefficientRing Λ X))]
    [HasDerivedCategory.{wB}
      (ModuleCat.{u + 1} ((condensedCoefficientRing Λ X).obj.obj (op U)))] :
    DerivedCategory (SheafOfModules.{u + 1} (condensedCoefficientRing Λ X)) ⥤
      DerivedCategory (ModuleCat.{u + 1}
        ((condensedCoefficientRing Λ X).obj.obj (op U))) :=
  haveI := Scheme.ProEt.moduleEvaluation_additive.{u, u + 1, 0}
    X (condensedCoefficientRing Λ X) U
  Functor.rightDerivedFunctorOfQuasiIsoResolutions
    (SheafOfModules.evaluation.{u + 1} (condensedCoefficientRing Λ X) (op U))
      (Scheme.ProEt.moduleQuasiIsoKInjectiveResolutions.{u, u + 1, 0}
        X (condensedCoefficientRing Λ X))

/-- The component quotient of an affine scheme, with its quotient topology.
Source: HRS, Proposition 4.3; Bhatt–Scholze, Lemma 2.4.8
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
def scalarAffineComponents (A : Type u) [CommRing A] : Profinite.{u} :=
  Profinite.of (ConnectedComponents (PrimeSpectrum A))

/-- The scalar map R = Λ(*) → Λ(S) induced by the unique map S → *.
Source: HRS, Definition 3.5 (blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
def condensedComponentScalar (A : Type u) [CommRing A] :
    condensedScalarRing Λ ⟶ (condensedSectionRing Λ).obj.obj (op (scalarAffineComponents A)) :=
  (condensedSectionRing Λ).obj.map (terminal.from (scalarAffineComponents A)).op

/-- Evaluation of the actual coefficient section-ring sheaf on a site object.
Source: HRS, Proposition 4.3(1)
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
abbrev scalarCoefficientEvaluation (X : Scheme.{u}) (U : X.ProEt) :=
  (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj.{u} Λ X)).obj.obj (op U)

/-- Evaluation of the existing condensed section-ring sheaf on the component quotient.
Source: HRS, Proposition 4.3(1)
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
abbrev scalarComponentEvaluation (A : Type u) [CommRing A] :=
  (condensedSectionRing Λ).obj.obj (op (scalarAffineComponents A))

/-- Additivity of the prescribed ordinary scalar extension, at the explicit module size.
It follows directly from its actual extension/restriction adjunction.
Source: HRS, Remark 3.2; Stacks, Tag 06YY
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation). -/
instance condensedComponentExtension_additive (A : Type u) [CommRing A] :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (condensedComponentScalar Λ A).hom).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
    (condensedComponentScalar Λ A).hom).left_adjoint_additive

universe wV wBV wBT

private theorem scalarSections_tExact
    (X : Scheme.{u}) (A : Type u) [CommRing A] [IsWContractibleRing A]
    (f : Spec (CommRingCat.of A) ⟶ X) [WeaklyEtale f]
    [HasDerivedCategory.{wS} (SheafOfModules.{u + 1} (condensedCoefficientRing Λ X))]
    [HasDerivedCategory.{wBT} (ModuleCat.{u + 1}
      ((condensedCoefficientRing Λ X).obj.obj (op (Scheme.ProEt.mk f))))]
    (B : CommRingCat.{u + 1}) [HasDerivedCategory.{wB} (ModuleCat.{u + 1} B)]
    (e : scalarCoefficientEvaluation Λ X (Scheme.ProEt.mk f) ≅ B) :
    (∀ (M : DerivedCategory (SheafOfModules.{u + 1} (condensedCoefficientRing Λ X)))
        (n : ℤ), M.IsLE n →
      ((condensedDerivedSections Λ X (Scheme.ProEt.mk f) ⋙
        Functor.mapDerivedCategory.{wBT, wB}
          (C₁ := ModuleCat.{u + 1}
            ((condensedCoefficientRing Λ X).obj.obj (op (Scheme.ProEt.mk f))))
          (C₂ := ModuleCat.{u + 1} B)
          (ModuleCat.restrictScalars.{u + 1} e.inv.hom)).obj M).IsLE n) ∧
    (∀ (M : DerivedCategory (SheafOfModules.{u + 1} (condensedCoefficientRing Λ X)))
        (n : ℤ), M.IsGE n →
      ((condensedDerivedSections Λ X (Scheme.ProEt.mk f) ⋙
        Functor.mapDerivedCategory.{wBT, wB}
          (C₁ := ModuleCat.{u + 1}
            ((condensedCoefficientRing Λ X).obj.obj (op (Scheme.ProEt.mk f))))
          (C₂ := ModuleCat.{u + 1} B)
          (ModuleCat.restrictScalars.{u + 1} e.inv.hom)).obj M).IsGE n) := by
  let ev := SheafOfModules.evaluation.{u + 1}
    (condensedCoefficientRing Λ X) (op (Scheme.ProEt.mk f))
  have := (Scheme.ProEt.wContractible_sections_exact.{u, u + 1, 0}
    X A f (condensedCoefficientRing Λ X)).2.2.1
  have := (Scheme.ProEt.wContractible_sections_exact.{u, u + 1, 0}
    X A f (condensedCoefficientRing Λ X)).2.2.2
  have : ev.Additive := Scheme.ProEt.moduleEvaluation_additive.{u, u + 1, 0} X _ _
  let i : condensedDerivedSections Λ X (Scheme.ProEt.mk f) ≅ ev.mapDerivedCategory :=
    ev.rightDerivedFunctorOfQuasiIsoResolutionsIsoMapDerivedCategory
      (Scheme.ProEt.moduleQuasiIsoKInjectiveResolutions.{u, u + 1, 0} X _)
  constructor
  · intro M n hM
    have := hM
    have h := ev.isLE_mapDerivedCategory_obj M n
    have := DerivedCategory.TStructure.t.isLE_of_iso (i.app M).symm n
    exact Functor.isLE_mapDerivedCategory_obj
      (C := ModuleCat.{u + 1}
        ((condensedCoefficientRing Λ X).obj.obj (op (Scheme.ProEt.mk f))))
      (ModuleCat.restrictScalars.{u + 1} e.inv.hom)
      ((condensedDerivedSections Λ X (Scheme.ProEt.mk f)).obj M) n
  · intro M n hM
    have := hM
    have h := ev.isGE_mapDerivedCategory_obj M n
    have := DerivedCategory.TStructure.t.isGE_of_iso (i.app M).symm n
    exact Functor.isGE_mapDerivedCategory_obj
      (C := ModuleCat.{u + 1}
        ((condensedCoefficientRing Λ X).obj.obj (op (Scheme.ProEt.mk f))))
      (ModuleCat.restrictScalars.{u + 1} e.inv.hom)
      ((condensedDerivedSections Λ X (Scheme.ProEt.mk f)).obj M) n

private theorem scalarSections_leftDerived
    (X : Scheme.{u}) (A : Type u) [CommRing A] [IsWContractibleRing A]
    (f : Spec (CommRingCat.of A) ⟶ X) [WeaklyEtale f]
    [HasDerivedCategory.{wS} (SheafOfModules.{u + 1} (condensedCoefficientRing Λ X))]
    [HasDerivedCategory.{wBT} (ModuleCat.{u + 1}
      ((condensedCoefficientRing Λ X).obj.obj (op (Scheme.ProEt.mk f))))]
    [HasDerivedCategory.{wB} (ModuleCat.{u + 1} (scalarComponentEvaluation Λ A))]
    (e : scalarCoefficientEvaluation Λ X (Scheme.ProEt.mk f) ≅
      scalarComponentEvaluation Λ A)
    (hθ : Nonempty
      ((commutativeSiteConstantModuleFunctor (coherentTopology Profinite.{u})
          (condensedScalarRing Λ) ⋙ (condensedScalarExtensionModel Λ).E) ⋙
        (InternalAbelianSheafModule.sectionModuleEquivalence
          (coherentTopology Profinite.{u}) Λ).inverse ⋙
        (upperStarFromPoint X).mapMod Λ ⋙
        (InternalAbelianSheafModule.sectionModuleEquivalence
          (Scheme.ProEt.topology X) (condensedRingObj Λ X)).functor ⋙
        SheafOfModules.evaluation _ (op (Scheme.ProEt.mk f)) ⋙
        ModuleCat.restrictScalars.{u + 1} e.inv.hom ≅
        ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (condensedComponentScalar Λ A).hom)) :
    ∃ (E : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)) ⥤
        DerivedCategory (ModuleCat.{u + 1} (scalarComponentEvaluation Λ A)))
      (ε : DerivedCategory.Q ⋙ E ⟶
        (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (condensedComponentScalar Λ A).hom).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      E.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ)) ∧
      Nonempty (condensedScalarRealization Λ X ⋙ condensedSectionModuleTransport Λ X ⋙
        condensedDerivedSections Λ X (Scheme.ProEt.mk f) ⋙
        Functor.mapDerivedCategory.{wBT, wB}
          (C₁ := ModuleCat.{u + 1}
            ((condensedCoefficientRing Λ X).obj.obj (op (Scheme.ProEt.mk f))))
          (C₂ := ModuleCat.{u + 1} (scalarComponentEvaluation Λ A))
          (ModuleCat.restrictScalars.{u + 1} e.inv.hom) ≅ E) := by
  classical
  let R := condensedScalarRing Λ
  let B := scalarComponentEvaluation Λ A
  let c := commutativeSiteConstantModuleFunctor (coherentTopology Profinite.{u}) R
  let m := condensedScalarExtensionModel Λ
  let p := (InternalAbelianSheafModule.sectionModuleEquivalence
    (coherentTopology Profinite.{u}) Λ).inverse
  let q := (upperStarFromPoint X).mapMod Λ
  let t := (InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)).functor
  let ev := SheafOfModules.evaluation.{u + 1}
    (condensedCoefficientRing Λ X) (op (Scheme.ProEt.mk f))
  let r := ModuleCat.restrictScalars.{u + 1} e.inv.hom
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    let : pointUpperStar.{u}.IsLeftAdjoint :=
      pointUpperStarLowerStarAdjunction.isLeftAdjoint
    unfold upperStarFromPoint
    infer_instance
  have : p.Additive := Functor.additive_of_preserves_binary_products p
  have : q.Additive := Functor.additive_of_preserves_binary_products q
  have : t.Additive := Functor.additive_of_preserves_binary_products t
  have : ev.Additive := Scheme.ProEt.moduleEvaluation_additive.{u, u + 1, 0} X _ _
  have : PreservesFiniteLimits ev :=
    (Scheme.ProEt.wContractible_sections_exact.{u, u + 1, 0}
      X A f (condensedCoefficientRing Λ X)).2.2.1
  have : PreservesFiniteColimits ev :=
    (Scheme.ProEt.wContractible_sections_exact.{u, u + 1, 0}
      X A f (condensedCoefficientRing Λ X)).2.2.2
  let φ := p ⋙ q ⋙ t ⋙ ev ⋙ r
  have : PreservesFiniteLimits (ev ⋙ r) := comp_preservesFiniteLimits ev r
  have : PreservesFiniteLimits (t ⋙ ev ⋙ r) := comp_preservesFiniteLimits t (ev ⋙ r)
  have : PreservesFiniteLimits (q ⋙ t ⋙ ev ⋙ r) :=
    comp_preservesFiniteLimits q (t ⋙ ev ⋙ r)
  have : PreservesFiniteLimits φ := comp_preservesFiniteLimits p (q ⋙ t ⋙ ev ⋙ r)
  have : PreservesFiniteColimits (ev ⋙ r) := comp_preservesFiniteColimits ev r
  have : PreservesFiniteColimits (t ⋙ ev ⋙ r) := comp_preservesFiniteColimits t (ev ⋙ r)
  have : PreservesFiniteColimits (q ⋙ t ⋙ ev ⋙ r) :=
    comp_preservesFiniteColimits q (t ⋙ ev ⋙ r)
  have : PreservesFiniteColimits φ := comp_preservesFiniteColimits p (q ⋙ t ⋙ ev ⋙ r)
  let F := ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (condensedComponentScalar Λ A).hom
  let H := c.mapDerivedCategory ⋙ m.T ⋙ φ.mapDerivedCategory
  let θ : (c ⋙ m.E) ⋙ φ ≅ F := hθ.some
  let β : DerivedCategory.Q ⋙ H ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight c.mapDerivedCategoryFactors.hom (m.T ⋙ φ.mapDerivedCategory) ≫
    Functor.whiskerLeft (c.mapHomologicalComplex (.up ℤ))
      (Functor.whiskerRight m.ε φ.mapDerivedCategory ≫
        Functor.whiskerLeft (m.E.mapHomologicalComplex (.up ℤ))
          φ.mapDerivedCategoryFactors.hom) ≫
    Functor.whiskerRight
      (Functor.whiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl (c ⋙ m.E)) (.up ℤ)).hom
        (φ.mapHomologicalComplex (.up ℤ)) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl ((c ⋙ m.E) ⋙ φ))
          (.up ℤ)).hom ≫
        (NatIso.mapHomologicalComplex θ (.up ℤ)).hom) DerivedCategory.Q
  have βiso (P : CochainComplex (ModuleCat.{u + 1} R) ℤ)
      (hP : P.IsKFlatForTotalTensor) (hf : ∀ n, Module.Flat R (P.X n)) :
      IsIso (β.app P) := by
    have hc := isKFlat_constantModule (coherentTopology Profinite.{u}) R P hP hf
    have := m.computes ((c.mapHomologicalComplex (.up ℤ)).obj P) hc
    dsimp [β]
    infer_instance
  have := ModuleCat.hasFunctorialFlatResolution_sameUniverse R
  let good (P : CochainComplex (ModuleCat.{u + 1} R) ℤ) :=
    P.IsKFlatForTotalTensor ∧ ∀ n, Module.Flat R (P.X n)
  have res (K : CochainComplex (ModuleCat.{u + 1} R) ℤ) :
      ∃ (P : CochainComplex (ModuleCat.{u + 1} R) ℤ) (a : P ⟶ K), good P ∧ QuasiIso a := by
    obtain ⟨P, a, ha, hf, hP⟩ := K.exists_quasiIso_flat_kFlat
    exact ⟨P, a, ⟨hP, fun n ↦ (ModuleCat.flat_iff_flat _).1 (hf n)⟩, ha⟩
  have hinv := ModuleCat.extendScalars_preservesKFlatQuasiIso
    (condensedComponentScalar Λ A).hom
  obtain ⟨d⟩ := SheafOfModules.nonempty_normalizedLeftExtension
    (A := ModuleCat.{u + 1} R) (D := ModuleCat.{u + 1} B)
    (ModuleCat.restrictScalars.{u + 1} (condensedComponentScalar Λ A).hom) F
    (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
      (condensedComponentScalar Λ A).hom) good res
    (fun a hP hQ ha ↦ by
      have := ha
      exact hinv.quasiIso_map hP.1 hQ.1 a)
  have := d.universal
  let η := d.derived.leftDerivedLift d.comparison
    (HomologicalComplex.quasiIso _ (.up ℤ)) H β
  have ηiso (P : CochainComplex (ModuleCat.{u + 1} R) ℤ) (hP : good P) :
      IsIso (η.app (DerivedCategory.Q.obj P)) := by
    have := d.computes P hP
    have := βiso P hP.1 hP.2
    have h := d.derived.leftDerived_fac_app d.comparison
      (HomologicalComplex.quasiIso _ (.up ℤ)) H β P
    have : IsIso (η.app (DerivedCategory.Q.obj P) ≫ d.comparison.app P) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (d.comparison.app P)
  have : IsIso η := by
    apply (NatTrans.isIso_iff_isIso_app η).2
    intro M
    obtain ⟨P, a, hP, ha⟩ := res (DerivedCategory.Q.objPreimage M)
    have := ha
    let i : DerivedCategory.Q.obj P ≅ M :=
      asIso (DerivedCategory.Q.map a) ≪≫ DerivedCategory.Q.objObjPreimageIso M
    have := ηiso P hP
    exact IsIso.of_isIso_fac_left (η.naturality i.hom)
  refine ⟨d.derived, d.comparison, d.universal, ⟨?_⟩⟩
  have hr : condensedDerivedSections Λ X (Scheme.ProEt.mk f) ≅ ev.mapDerivedCategory :=
    ev.rightDerivedFunctorOfQuasiIsoResolutionsIsoMapDerivedCategory
      (Scheme.ProEt.moduleQuasiIsoKInjectiveResolutions.{u, u + 1, 0} X _)
  have he : condensedScalarRealization Λ X ⋙ condensedSectionModuleTransport Λ X ⋙
      condensedDerivedSections Λ X (Scheme.ProEt.mk f) ⋙
      Functor.mapDerivedCategory.{wBT, wB}
        (C₁ := ModuleCat.{u + 1}
          ((condensedCoefficientRing Λ X).obj.obj (op (Scheme.ProEt.mk f))))
        (C₂ := ModuleCat.{u + 1} B) r ≅ H := by
    let ed := Functor.mapDerivedCategory.{wS, wBT}
      (C₁ := SheafOfModules.{u + 1} (condensedCoefficientRing Λ X))
      (C₂ := ModuleCat.{u + 1}
        ((condensedCoefficientRing Λ X).obj.obj (op (Scheme.ProEt.mk f)))) ev
    let rd := Functor.mapDerivedCategory.{wBT, wB}
      (C₁ := ModuleCat.{u + 1}
        ((condensedCoefficientRing Λ X).obj.obj (op (Scheme.ProEt.mk f))))
      (C₂ := ModuleCat.{u + 1} B) r
    let td := Functor.mapDerivedCategory.{u + 1, wS} t
    let k : φ.mapDerivedCategory ≅
        p.mapDerivedCategory ⋙ q.mapDerivedCategory ⋙ td ⋙ ed ⋙ rd :=
      Functor.mapDerivedCategoryCompIso p (q ⋙ t ⋙ ev ⋙ r) ≪≫
        Functor.isoWhiskerLeft p.mapDerivedCategory
          (Functor.mapDerivedCategoryCompIso q (t ⋙ ev ⋙ r) ≪≫
            Functor.isoWhiskerLeft q.mapDerivedCategory
              (Functor.mapDerivedCategoryCompIso t (ev ⋙ r) ≪≫
                Functor.isoWhiskerLeft td (Functor.mapDerivedCategoryCompIso ev r)))
    change (c.mapDerivedCategory ⋙ m.T) ⋙ p.mapDerivedCategory ⋙
      q.mapDerivedCategory ⋙ td ⋙ condensedDerivedSections Λ X (Scheme.ProEt.mk f) ⋙
      rd ≅ H
    exact Functor.isoWhiskerLeft
      (c.mapDerivedCategory ⋙ m.T ⋙ p.mapDerivedCategory ⋙ q.mapDerivedCategory ⋙ td)
      (Functor.isoWhiskerRight hr rd) ≪≫
      Functor.isoWhiskerLeft (c.mapDerivedCategory ⋙ m.T) k.symm
  exact he ≪≫ asIso η

/-- Evaluation of ordinary condensed scalar extension on a w-contractible affine,
with no t-admissibility hypothesis. The coefficients are the recorded internal ring objects.
The existing scalar realization is used without a second construction.
The universal left-derived pair E, ε means ordinary derived tensor over R;
the comparison is a natural isomorphism on all of D(R), without boundedness.
The last two clauses give both halves of t-exactness of RΓ(V,-).

Source: Hemo–Richarz–Scholbach, equations (3.1), (3.2), Remark 3.2,
Lemma 4.1(1), Proposition 4.3(1); Bhatt–Scholze, Lemma 2.4.8
(blueprint: lem-zl-wcontractible-condensed-scalar-evaluation).

Proof for stage 3:
1. Apply condensed_affine_ordinary_scalar_sections on T and V. This identifies the
actual coefficient section rings with Λ(pi_0 V) and supplies a natural comparison
of the prescribed ordinary scalar extension with extension from R to Λ(pi_0 V).
2. Weak contractibility makes affine evaluation exact. Identify its recorded
right-derived functor with its termwise derived functor. Exact evaluation and exact
restriction of scalars preserve both truncation bounds, proving the final clauses.
3. Compose the ordinary comparison with the counit of the fixed change-of-rings
model and the exact derived-factorization isomorphisms. This gives a transformation
from the localized scalar-realization composite to ordinary extension on complexes.
For a K-flat complex P with flat terms, constant realization remains K-flat, so the
fixed change-of-rings model computes termwise and this transformation is invertible.
4. Resolve every complex by a K-flat flat-term complex. Ordinary extension preserves
quasi-isomorphisms between these complexes. The normalized left-extension theorem
therefore constructs a universal left-derived extension E with invertible counit
on these resolutions. Its universal property gives a comparison from the recorded
scalar-realization composite to E. The factorization equation makes it invertible
on resolutions, and naturality along each resolution makes it invertible everywhere.
5. The exact derived-composition isomorphisms identify this composite with precisely
the functor in the statement, including the given independent localization universes.
There is no boundedness, flatness of Λ(pi_0 V), or t-admissibility hypothesis. -/
theorem wContractible_condensed_scalar_evaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (T : Scheme.{u})
    (A : Type u) [CommRing A] [IsWContractibleRing A]
    (f : Spec (CommRingCat.of A) ⟶ T) [WeaklyEtale f]
    [HasDerivedCategory.{wS} (SheafOfModules.{u + 1} (condensedCoefficientRing Λ T))]
    [HasDerivedCategory.{wV} (SheafOfModules.{u + 1}
      (condensedCoefficientRing Λ (Spec (CommRingCat.of A))))]
    [HasDerivedCategory.{wBT} (ModuleCat.{u + 1}
      ((condensedCoefficientRing Λ T).obj.obj (op (Scheme.ProEt.mk f))))]
    [HasDerivedCategory.{wBV} (ModuleCat.{u + 1}
      ((condensedCoefficientRing Λ (Spec (CommRingCat.of A))).obj.obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of A)))))))]
    [HasDerivedCategory.{wB} (ModuleCat.{u + 1} (scalarComponentEvaluation Λ A))] :
    ∃ (eT : scalarCoefficientEvaluation Λ T (Scheme.ProEt.mk f) ≅
        scalarComponentEvaluation Λ A)
      (eV : scalarCoefficientEvaluation Λ (Spec (CommRingCat.of A))
        (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of A)))) ≅ scalarComponentEvaluation Λ A),
      (∃ (E : DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)) ⥤
          DerivedCategory (ModuleCat.{u + 1} (scalarComponentEvaluation Λ A)))
        (ε : DerivedCategory.Q ⋙ E ⟶
          (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            (condensedComponentScalar Λ A).hom).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
        E.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ)) ∧
        Nonempty (condensedScalarRealization Λ T ⋙ condensedSectionModuleTransport Λ T ⋙
          condensedDerivedSections Λ T (Scheme.ProEt.mk f) ⋙
          Functor.mapDerivedCategory.{wBT, wB}
            (C₁ := ModuleCat.{u + 1}
              ((condensedCoefficientRing Λ T).obj.obj (op (Scheme.ProEt.mk f))))
            (C₂ := ModuleCat.{u + 1} (scalarComponentEvaluation Λ A))
            (ModuleCat.restrictScalars.{u + 1} eT.inv.hom) ≅ E)) ∧
      (∀ (M : DerivedCategory (SheafOfModules.{u + 1}
          (condensedCoefficientRing Λ (Spec (CommRingCat.of A))))) (n : ℤ),
        M.IsLE n → ((condensedDerivedSections Λ (Spec (CommRingCat.of A))
          (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of A)))) ⋙
          Functor.mapDerivedCategory.{wBV, wB}
            (C₁ := ModuleCat.{u + 1}
              ((condensedCoefficientRing Λ (Spec (CommRingCat.of A))).obj.obj
                (op (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of A)))))))
            (C₂ := ModuleCat.{u + 1} (scalarComponentEvaluation Λ A))
            (ModuleCat.restrictScalars.{u + 1} eV.inv.hom)).obj M).IsLE n) ∧
      (∀ (M : DerivedCategory (SheafOfModules.{u + 1}
          (condensedCoefficientRing Λ (Spec (CommRingCat.of A))))) (n : ℤ),
        M.IsGE n → ((condensedDerivedSections Λ (Spec (CommRingCat.of A))
          (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of A)))) ⋙
          Functor.mapDerivedCategory.{wBV, wB}
            (C₁ := ModuleCat.{u + 1}
              ((condensedCoefficientRing Λ (Spec (CommRingCat.of A))).obj.obj
                (op (Scheme.ProEt.mk (𝟙 (Spec (CommRingCat.of A)))))))
            (C₂ := ModuleCat.{u + 1} (scalarComponentEvaluation Λ A))
            (ModuleCat.restrictScalars.{u + 1} eV.inv.hom)).obj M).IsGE n) := by
  obtain ⟨eT, hT⟩ := condensed_affine_ordinary_scalar_sections Λ T A f
  obtain ⟨eV, _⟩ := condensed_affine_ordinary_scalar_sections Λ
    (Spec (CommRingCat.of A)) A (𝟙 _)
  refine ⟨eT, eV, scalarSections_leftDerived Λ T A f eT hT, ?_⟩
  exact scalarSections_tExact Λ (Spec (CommRingCat.of A)) A (𝟙 _)
    (scalarComponentEvaluation Λ A) eV

end AlgebraicGeometry.ProEtale
