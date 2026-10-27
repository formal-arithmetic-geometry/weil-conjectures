/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.Paper.PbcConstantWeilTwist
public import Sheaf.Paper.ConstantWeilStageCompatibility
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.EtaleWeilFundamentalRepresentation
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # Constant-line tensor and scalar Weil rescaling

Source: the first sentence of the constant-twist weight proof in the current blueprint,
sec-purity-real-sheaves/sk-r-real-linear/lem-wf-constant-twist-weight.proof.md
(blueprint: def-wf-completed-constant-right-unit).

All tensor products below are the recorded completed PBC tensor. The normalization
retains coefficient multiplication before completion, rather than choosing a tensor iso.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor
namespace WeilConjectures
attribute [local irreducible] wfRationalTensor wfConstructibleInclusion
  wfRationalTensorPullback wfWeilStructure
  ScalarLocalization.category ScalarLocalization.preadditive
  ScalarLocalization.linear ScalarLocalization.linearOriginal

/-- The actual coefficient ring as a degree-zero complex, on the original small site.
Source: item proof, step 4 (blueprint: def-wf-completed-constant-right-unit). -/
def constantTwistUnitComplex (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ :=
  (CochainComplex.singleFunctor _ 0).obj
    (SheafOfModules.unit ((adicLisseForget X).obj (pbcAdicCompletion X d)))

/-- The unit is among the actual flat-term K-flat representatives.
Source: item proof, step 4 (blueprint: def-wf-completed-constant-right-unit).
Proof: tensoring with the regular module is the identity, so it preserves acyclics.
The degree-zero regular module is flat, and the other terms vanish. -/
theorem constantTwistUnitComplex_flat (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    proEtaleFlatRepresentatives X (pbcAdicCompletion X d) (constantTwistUnitComplex X d) := by
  sorry

/-- The ordinary right unitor, uniquely normalized on every resolving representative.
Source: item proof, step 4 (blueprint: def-wf-completed-constant-right-unit).
Proof: tensor the identity resolution with the coefficient unit. On complexes the
right unitor sends x tensor a to ax and its inverse sends x to x tensor one.
The maps are natural and respect quasi-isomorphisms. Localization gives the family;
restriction to the resolving subcategory is fully faithful, proving uniqueness. -/
theorem constantTwistOrdinaryRightUnit_existsUnique
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ∃! r : ∀ M : PbcCompletedDerived X d,
        (wfOrdinaryDerivedTensor X d).obj
          (M, DerivedCategory.Q.obj (constantTwistUnitComplex X d)) ≅ M,
      (∀ (M N : PbcCompletedDerived X d) (f : M ⟶ N),
        (wfOrdinaryDerivedTensor X d).map (X := (M, _)) (Y := (N, _))
          (Prod.mkHom f (𝟙 _)) ≫ (r N).hom = (r M).hom ≫ f) ∧
      ∀ P : (proEtaleFlatRepresentatives X (pbcAdicCompletion X d)).FullSubcategory,
        ((wfTensorModel X d).representative.app
          (P, ⟨constantTwistUnitComplex X d, constantTwistUnitComplex_flat X d⟩)).hom ≫
            (r (DerivedCategory.Q.obj P.obj)).hom =
          DerivedCategory.Q.map (HomologicalComplex.rightUnitor P.obj).hom := by
  sorry

/-- The preceding uniquely normalized ordinary right unitor.
Source: item proof, step 4 (blueprint: def-wf-completed-constant-right-unit). -/
def constantTwistOrdinaryRightUnit
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :=
  (constantTwistOrdinaryRightUnit_existsUnique X d).exists.choose

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [IsSeparated X₀.hom]
  (S : FdCoefficientComparisonSystem.{u} c.l c.Qbar)

/-- The coefficient inclusion used by tensor, with no change of ambient category.
Source: item proof, step 4 (blueprint: def-wf-completed-constant-right-unit). -/
abbrev constantTwistAmbientInclusion (E : Padic.FiniteCoefficientFields c.l c.Qbar) :=
  wfConstructibleInclusion (D.geometricFiber X₀).left
    (pbcStageDatum.{u} c.l c.Qbar E) 1
    (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
    (wfUniformizer_generates D c E) (pbcStageUniformizer.{u} c.l c.Qbar E)

/-- The canonical degree-zero section of a single regular module.
Source: item proof, steps 2 and 4
(blueprint: def-wf-completed-constant-right-unit). -/
def constantTwistSingleSection {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (U : X.ProEtᵒᵖ) (x : R.obj.obj U) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
    (SheafOfModules.unit R)).inv.val.app U x

/-- J identifies the integral constant object with the actual completed ring in degree zero.
The map is fixed on coefficient sections, retaining the derived-transport comparison.
Source: item proof, step 2 (blueprint: def-wf-completed-constant-right-unit).
Proof: restriction along the normalized coefficient-ring isomorphism sends the regular
module to the regular module by the inverse ring isomorphism on sections. Apply the
single-complex functor and its derived comparison. The integral identity for J supplies
the displayed source. The section formula determines the cochain map and hence e. -/
theorem constantTwistIntegralUnit_existsUnique
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    ∃! e :
        (((S.coefficients (D.geometricFiber X₀).left).stage E).integral.functor.obj
          (constantWeilIntegralObject c.l (pbcFiniteField.{u} c.l c.Qbar E)
            D c.different (D.geometricFiber X₀).left)).obj ≅
        DerivedCategory.Q.obj (constantTwistUnitComplex (D.geometricFiber X₀).left
          (pbcStageDatum.{u} c.l c.Qbar E)),
      ∃ a : ((fdCoefficientTransport c.l (pbcFiniteField.{u} c.l c.Qbar E)
          (D.geometricFiber X₀).left).mapHomologicalComplex (.up ℤ)).obj
            (constantWeilIntegralComplex c.l (pbcFiniteField.{u} c.l c.Qbar E)
              (D.geometricFiber X₀).left) ≅
          constantTwistUnitComplex (D.geometricFiber X₀).left
            (pbcStageDatum.{u} c.l c.Qbar E),
        (∀ (U : (D.geometricFiber X₀).left.ProEtᵒᵖ)
          (x : (completedIntegralCoefficientSheafUnrestricted c.l
            (pbcFiniteField.{u} c.l c.Qbar E) (D.geometricFiber X₀).left).obj.obj U),
          (a.hom.f 0).val.app U
              (constantTwistSingleSection _ U x) =
            constantTwistSingleSection _ U
              ((integralDetailedCoefficientComparison (D.geometricFiber X₀).left c.l
                (pbcFiniteField.{u} c.l c.Qbar E)).inv.hom.app U x)) ∧
        HEq e.hom
          ((fdCoefficientTransportFactors c.l (pbcFiniteField.{u} c.l c.Qbar E)
            (D.geometricFiber X₀).left).hom.app
              (constantWeilIntegralComplex c.l (pbcFiniteField.{u} c.l c.Qbar E)
                (D.geometricFiber X₀).left) ≫ DerivedCategory.Q.map a.hom) := by
  sorry

/-- The uniquely section-normalized identification of J's integral coefficient object.
Source: item proof, step 2 (blueprint: def-wf-completed-constant-right-unit). -/
def constantTwistIntegralUnit (E : Padic.FiniteCoefficientFields c.l c.Qbar) :=
  (constantTwistIntegralUnit_existsUnique D c X₀ S E).exists.choose

/-- J's integral carrier in the intrinsically complete ambient category.
Source: item proof, step 4 (blueprint: def-wf-completed-constant-right-unit). -/
abbrev constantTwistIntegralCarrier (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (M : sfIntegralConstructibleCategory c.l (pbcFiniteField.{u} c.l c.Qbar E)
      (D.geometricFiber X₀).left) :=
  (wfIntegralConstructibleInclusion (D.geometricFiber X₀).left
    (pbcStageDatum.{u} c.l c.Qbar E) 1
    (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
    (wfUniformizer_generates D c E)).obj
      (((S.coefficients (D.geometricFiber X₀).left).stage E).integral.functor.obj M)

/-- The completed right-unit map is the unique extension of ordinary multiplication
across the Koszul completion unit. This is equivalently C(r) followed by u inverse.
Source: item proof, step 4 (blueprint: def-wf-completed-constant-right-unit).
Proof: tensor the canonical integral unit identification with M. Follow with ordinary
right multiplication. Completeness of J(M) gives a unique extension across completion.
The ordinary unitor and the completion unit on a complete object are invertible,
so this extension is an isomorphism; the reflector's Hom bijection gives uniqueness. -/
theorem constantTwistCompletedRightUnit_existsUnique
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    ∃! r : ∀ M : sfIntegralConstructibleCategory c.l
        (pbcFiniteField.{u} c.l c.Qbar E) (D.geometricFiber X₀).left,
      (wfIntegralTensor (D.geometricFiber X₀).left
        (pbcStageDatum.{u} c.l c.Qbar E) 1
        (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
        (wfUniformizer_generates D c E)).obj
          (constantTwistIntegralCarrier D c X₀ S E M,
            constantTwistIntegralCarrier D c X₀ S E
              (constantWeilIntegralObject c.l (pbcFiniteField.{u} c.l c.Qbar E)
                D c.different (D.geometricFiber X₀).left)) ≅
        constantTwistIntegralCarrier D c X₀ S E M,
      ∀ M, HEq (r M).hom.hom
        (wfCompletionExtend (D.geometricFiber X₀).left
          (pbcStageDatum.{u} c.l c.Qbar E) 1
          (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
          (wfUniformizer_generates D c E) _ (constantTwistIntegralCarrier D c X₀ S E M)
          ((wfOrdinaryDerivedTensor (D.geometricFiber X₀).left
            (pbcStageDatum.{u} c.l c.Qbar E)).map
              (X := ((constantTwistIntegralCarrier D c X₀ S E M).obj,
                (constantTwistIntegralCarrier D c X₀ S E
                  (constantWeilIntegralObject c.l (pbcFiniteField.{u} c.l c.Qbar E)
                    D c.different (D.geometricFiber X₀).left)).obj))
              (Y := ((constantTwistIntegralCarrier D c X₀ S E M).obj,
                DerivedCategory.Q.obj (constantTwistUnitComplex (D.geometricFiber X₀).left
                  (pbcStageDatum.{u} c.l c.Qbar E))))
              (Prod.mkHom (𝟙 _) (constantTwistIntegralUnit D c X₀ S E).hom) ≫
            (constantTwistOrdinaryRightUnit (D.geometricFiber X₀).left
              (pbcStageDatum.{u} c.l c.Qbar E)
              (constantTwistIntegralCarrier D c X₀ S E M).obj).hom)) := by
  sorry

/-- The uniquely completed coefficient multiplication.
Source: item proof, step 4 (blueprint: def-wf-completed-constant-right-unit). -/
def constantTwistCompletedRightUnit (E : Padic.FiniteCoefficientFields c.l c.Qbar) :=
  (constantTwistCompletedRightUnit_existsUnique D c X₀ S E).exists.choose

/-- Rationalization of the completed right-unit map, fixed on every integral object.
Source: item proof, step 4 (blueprint: def-wf-completed-constant-right-unit).
Proof: localize the completed integral map. J's object normalization gives the source
and target identifications. Every rational morphism is a fraction of integral arrows,
so this family is natural and uniquely determined by the displayed equation. -/
theorem constantTwistRationalRightUnit_existsUnique
    (E : Padic.FiniteCoefficientFields c.l c.Qbar) :
    ∃! r : ∀ M : sfRationalConstructibleCategory c.l
        (pbcFiniteField.{u} c.l c.Qbar E) (D.geometricFiber X₀).left,
      (wfTensor D c X₀ E).obj
        ((constantTwistAmbientInclusion D c X₀ E).obj
          (((S.coefficients (D.geometricFiber X₀).left).stage E).rational.functor.obj M),
          wfWeilCarrier D c X₀ E
            (pbcFiniteConstantWeilLine D c X₀ S E 1)) ≅
        (constantTwistAmbientInclusion D c X₀ E).obj
          (((S.coefficients (D.geometricFiber X₀).left).stage E).rational.functor.obj M),
      ∀ M, HEq (r M).hom
        ((ScalarLocalization.localization (PbcIntegralRing c.l
          (pbcFiniteField.{u} c.l c.Qbar E))
          (WfCompleteCategory (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)
            1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E)
            (wfUniformizer_generates D c E))
          (pbcStageUniformizer.{u} c.l c.Qbar E)).map
          (constantTwistCompletedRightUnit D c X₀ S E M.obj).hom) := by
  sorry

/-- The rationalized right-unit isomorphism with its unchanged integral normalization.
Source: item proof, step 4 (blueprint: def-wf-completed-constant-right-unit). -/
def constantTwistRationalRightUnit (E : Padic.FiniteCoefficientFields c.l c.Qbar) :=
  (constantTwistRationalRightUnit_existsUnique D c X₀ S E).exists.choose


end WeilConjectures
