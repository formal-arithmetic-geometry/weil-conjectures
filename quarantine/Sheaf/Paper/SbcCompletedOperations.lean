/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.CompletedPullbackReduction
import Sheaf.Paper.CompletedRlimFunctor
import Sheaf.Paper.CondensedAmbientExchange
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.IntrinsicCompletionCompleted
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.Paper.PerfectProjectionFormula
import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Paper.WeilCompletedTensorReflector
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-! # Linear completed operations and their canonical exchange
Source: blueprint order 1442, Stacks Tags 099N, 099K and 07A7
(blueprint: lem-sbc-completed-operations-linear-natural-exchange).
The units and comparison maps below are fixed by ordinary tensor and the completion
unit. No natural isomorphism is selected without its normalizing equation.

## Main statements

- `sbcPull`, `sbcPush`, `sbcAdjunction`: normalized linear complete operations.
- `sbcTheta`, `sbcExchange`: their canonical square comparison and mate.
- `sbcCompletedOperations_linear_natural_exchange`: finite-reduction compatibility.
- `sbcCompletedExchange_strictLimit`: equality with the strict derived-limit realization.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u r v w v' w'
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
/-- The published intrinsic completeness predicate on the actual completed ring.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev IsPbcComplete (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) : ObjectProperty (PbcCompletedDerived T (pbcIntegralDatum l E)) :=
  PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E)

/-- Full category of intrinsically complete complexes without a constructibility bound.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev PbcComplete (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) := (IsPbcComplete l E T).FullSubcategory

/-- Alias of the landed integral constructible category; no new predicate is defined.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev PbcIntegralConstructible (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) := PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)

/-- Alias of the landed raw rational constructible category.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev PbcRationalConstructible (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) := PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)

/-- Raw scalar localization of the complete ambient category, using the landed action.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev PbcRationalComplete (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) :=
  ScalarLocalization (PbcIntegralRing l E) (PbcComplete l E T) (pbcUniformizer l E)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The full integral inclusion with the completeness property already in membership.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def pbcConstructibleInclusion (T : Scheme.{u}) :
    PbcIntegralConstructible l E T ⥤ PbcComplete l E T :=
  (IsPbcComplete l E T).lift
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)))
    (fun K ↦ K.property.1)

/-- The full inclusion preserves addition and the published constant scalar action.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: both subcategories have exactly the ambient Hom groups and scalar actions.
The inclusion sends every morphism to itself, so preserves addition and multiplication
by every constant section. These are the additive and linear functor equations. -/
theorem pbcConstructibleInclusion_linear (T : Scheme.{u}) :
    (pbcConstructibleInclusion l E T).Additive ∧
      (pbcConstructibleInclusion l E T).Linear (PbcIntegralRing l E) := by
  constructor
  · exact ⟨fun {_ _} {_ _} ↦ rfl⟩
  · exact ⟨fun {_ _} _ _ ↦ rfl⟩

/-- Additivity of the full inclusion. Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance pbcConstructibleInclusion_additive (T : Scheme.{u}) :
    (pbcConstructibleInclusion l E T).Additive :=
  (pbcConstructibleInclusion_linear l E T).1

/-- Linearity of the full inclusion. Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance pbcConstructibleInclusion_scalarLinear (T : Scheme.{u}) :
    (pbcConstructibleInclusion l E T).Linear (PbcIntegralRing l E) :=
  (pbcConstructibleInclusion_linear l E T).2

end WeilConjectures

namespace CategoryTheory.ScalarLocalization
variable (R : Type r) [CommRing R] (p : R)
  {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]
  {D : Type v'} [Category.{w'} D] [Preadditive D] [Linear R D]
  (F : C ⥤ D) [F.Additive] [F.Linear R]

/-- The localized map is the linear base change of the original map on Hom modules.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def betweenHom (K L : C) := (F.mapLinearMap R (X := K) (Y := L)).baseChange (Localization.Away p)

/-- Base change of linear Hom maps preserves the category laws.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: check identity on 1 tensor id and composition on pairs of pure tensors, where
both sides are ab tensor F(fg). Extend by bilinearity and tensor induction. -/
theorem between_laws :
    (∀ K : C, betweenHom R p F K K ((1 : Localization.Away p) ⊗ₜ[R] 𝟙 K) =
      (1 : Localization.Away p) ⊗ₜ[R] 𝟙 (F.obj K)) ∧
    (∀ (K L M : C) (f : Localization.Away p ⊗[R] (K ⟶ L))
      (g : Localization.Away p ⊗[R] (L ⟶ M)),
      betweenHom R p F K M (composition R C p K L M g f) =
        composition R D p (F.obj K) (F.obj L) (F.obj M)
          (betweenHom R p F L M g) (betweenHom R p F K L f)) := by
  constructor
  · intro K
    simp [betweenHom]
  · intro K L M f g
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul b g =>
      induction f using TensorProduct.induction_on with
      | zero => simp
      | tmul a f => simp [betweenHom, composition_tmul]
      | add f f' hf hf' => simp [map_add, hf, hf']
    | add g g' hg hg' => simp [map_add, hg, hg']

/-- Scalar localization of a linear functor between two possibly different categories.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def between : ScalarLocalization R C p ⥤ ScalarLocalization R D p where
  obj K := ⟨F.obj K.obj⟩
  map {K L} f := betweenHom R p F K.obj L.obj f
  map_id K := (between_laws R p F).1 K.obj
  map_comp {K L M} f g := (between_laws R p F).2 K.obj L.obj M.obj f g

variable {F} {G : C ⥤ D} [G.Additive] [G.Linear R]

/-- Localized naturality follows on pure tensors from integral naturality.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: on a tensor a tensor f the two sides are a tensor of the naturality square
for f. The tensor maps and composition are additive, so tensor induction finishes. -/
theorem betweenNat_naturality (α : F ⟶ G) (K L : ScalarLocalization R C p)
    (f : K ⟶ L) :
    (between R p F).map f ≫ ((1 : Localization.Away p) ⊗ₜ[R] α.app L.obj) =
      ((1 : Localization.Away p) ⊗ₜ[R] α.app K.obj) ≫ (between R p G).map f := by
  change composition R D p _ _ _ _ (betweenHom R p F _ _ f) =
    composition R D p _ _ _ (betweenHom R p G _ _ f) _
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul a f => simp [betweenHom, composition_tmul, α.naturality f]
  | add f g hf hg => simp [map_add, hf, hg]

/-- Localize the specified natural transformation componentwise by tensoring with one.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def betweenNat (α : F ⟶ G) : between R p F ⟶ between R p G where
  app K := (1 : Localization.Away p) ⊗ₜ[R] α.app K.obj
  naturality := betweenNat_naturality R p α

end CategoryTheory.ScalarLocalization

namespace WeilConjectures
/-- Localize the full inclusion of the landed constructible category.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def pbcRationalInclusion (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) : PbcRationalConstructible l E T ⥤ PbcRationalComplete l E T :=
  ScalarLocalization.between (PbcIntegralRing l E)
    (pbcUniformizer l E) (pbcConstructibleInclusion l E T)
end WeilConjectures
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {U V : Scheme.{u}} (q : U ⟶ V)

/-- The canonical completed coefficient map is invertible.
Source: Stacks 099N (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: finite quotient sheaves are finite constant sheaves and their quotient maps
are the prescribed scalar maps. Profinite-coefficient inverse-image commutation applies
to this system. Its map agrees with completedCoefficientMap by every finite projection,
so the uniqueness of that limit-cone map identifies it with the given isomorphism. -/
theorem sbcCompletedCoefficientMap_isIso :
    IsIso (completedCoefficientMap q (pbcIntegralDatum l E)) := by
  let d := pbcIntegralDatum l E
  let Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1} := Functor.ofOpSequence
    (X := fun n ↦ CommRingCat.of (PbcIntegralRing l E ⧸ d.ideal ^ (n + 1)))
    (fun n ↦ CommRingCat.ofHom (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
  let : ∀ n : ℕᵒᵖ, Finite (Q.obj n) := fun n ↦ d.quotientFinite n.unop
  let e (W : Scheme.{u}) : proEtaleCoefficientTower W Q ≅ adicLisseRingSystem W d.ideal :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
      (fun f ↦ (NatTrans.ofOpSequence
        (F := proEtaleCoefficientTower W Q) (G := adicLisseRingSystem W d.ideal)
        (fun _ ↦ 𝟙 _) (fun n ↦ by
          simp [proEtaleCoefficientTower, Q, adicLisseRingSystem])).naturality f)
  let b (W : Scheme.{u}) := e W ≪≫ pbcConstantSystemComparison W d
  let c (W : Scheme.{u}) := HasLimit.isoOfNatIso (b W)
  let L := proEtaleSheafInverseImage q CommRingCat.{u + 1}
  let := (proEtale_profinite_coefficient_inverse_image Q).2.1 U V q
  let t := L.mapIso (c V).symm ≪≫ asIso (proEtaleProfiniteComparison q Q) ≪≫ c U
  suffices h : completedCoefficientMap q d = t.hom by
    rw [h]
    infer_instance
  apply limit.hom_ext
  rintro ⟨n⟩
  dsimp only [completedCoefficientMap, t, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [limit.lift_π, Category.assoc]
  dsimp only [c]
  rw [HasLimit.isoOfNatIso_hom_π]
  simp only [asIso_hom]
  rw [reassoc_of% (proEtale_profinite_coefficient_inverse_image Q).2.2.1 U V q (op n)]
  rw [← Category.assoc, ← Category.assoc, ← L.map_comp]
  rw [HasLimit.isoOfNatIso_inv_π]
  simp only [L.map_comp, Category.assoc]
  dsimp only [b, e, Iso.trans_hom, NatIso.ofComponents_hom_app, Iso.refl_hom,
    Category.id_comp, proEtaleConstantComparison]
  simp only [completedCoefficientComponent, completedFiniteCoefficientMap, Category.assoc,
    L, pbcConstantSystemComparison, pbcAdicProjection, Q, Iso.trans_inv,
    NatTrans.comp_app, NatIso.ofComponents_inv_app, NatIso.ofComponents_hom_app,
    Iso.refl_inv, Functor.map_comp]
  dsimp only [proEtaleCoefficientTower, Functor.comp_obj, Functor.ofOpSequence_obj]
  simp only [Iso.refl_hom, Category.id_comp]
  change L.map (pbcAdicProjection V d n) ≫
      L.map (pbcLevelConstantComparison V d n).inv ≫
      proEtaleConstantInverseImageMap q CommRingCat.{u + 1}
        (CommRingCat.of (PbcIntegralRing l E ⧸ d.ideal ^ (n + 1))) ≫
      (pbcLevelConstantComparison U d n).hom =
    L.map (pbcAdicProjection V d n) ≫
      L.map (pbcLevelConstantComparison V d n).inv ≫
      L.map (𝟙 (adicLisseConstantRing V
        (PbcIntegralRing l E ⧸ d.ideal ^ (n + 1)))) ≫
      proEtaleConstantInverseImageMap q CommRingCat.{u + 1}
        (CommRingCat.of (PbcIntegralRing l E ⧸ d.ideal ^ (n + 1))) ≫
      (pbcLevelConstantComparison U d n).hom
  rw [L.map_id, Category.id_comp]


/-- The actual finite-projection-normalized coefficient isomorphism.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcCoefficientIso :=
  letI := sbcCompletedCoefficientMap_isIso l E q
  asIso (completedCoefficientMap q (pbcIntegralDatum l E))

/-- Ordinary, uncompleted, canonical derived pullback.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev sbcOrdinaryPull := proEtaleRingDerivedPullback q
  (pbcAdicCompletion V (pbcIntegralDatum l E))
  (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q)

/-- The actual K-injective derived module direct image along the coefficient map.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev sbcAmbientPush := proEtaleRingDerivedDirectImage q
  (pbcAdicCompletion V (pbcIntegralDatum l E))
  (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q)

/-- The specified object equality gives the identity on sheafified tensors.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcOrdinaryModuleIsoApp
    (M : pbcModules V (pbcAdicCompletion V (pbcIntegralDatum l E))) :
    (completedModulePullback q (pbcIntegralDatum l E)).obj M ≅
      (proEtaleRingModulePullback q
        (pbcAdicCompletion V (pbcIntegralDatum l E))
        (pbcAdicCompletion U (pbcIntegralDatum l E))
        (sbcCoefficientIso l E q)).obj M :=
  eqToIso ((completedAdicChangeData U
    (completedCoefficientMap q (pbcIntegralDatum l E))).choose_spec.choose
      ((proEtaleModuleInverseImage q
        (pbcAdicCompletion V (pbcIntegralDatum l E))).obj M))

/-- The object equality in the normalized scalar-extension interface is natural.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: both maps are the sheafification of r tensor x maps to r tensor a(x),
by the morphism characterization in completedAdicChangeData. The tensor generators
and the sheafification universal property prove the naturality square. -/
theorem sbcOrdinaryModuleIso_naturality
    (M N : pbcModules V (pbcAdicCompletion V (pbcIntegralDatum l E)))
    (a : M ⟶ N) :
    (completedModulePullback q (pbcIntegralDatum l E)).map a ≫
      (sbcOrdinaryModuleIsoApp l E q N).hom =
    (sbcOrdinaryModuleIsoApp l E q M).hom ≫
      (proEtaleRingModulePullback q
        (pbcAdicCompletion V (pbcIntegralDatum l E))
        (pbcAdicCompletion U (pbcIntegralDatum l E))
        (sbcCoefficientIso l E q)).map a := by
  let h := (completedAdicChangeData U
    (completedCoefficientMap q (pbcIntegralDatum l E))).choose_spec.choose
  change (completedAdicChangeData U
    (completedCoefficientMap q (pbcIntegralDatum l E))).choose.map
      ((proEtaleModuleInverseImage q _).map a) ≫ eqToHom (h _) =
    eqToHom (h _) ≫ SheafOfModules.changeOfRingsHom
      (completedCoefficientMap q (pbcIntegralDatum l E)) _
      ((proEtaleModuleInverseImage q _).map a)
  rw [(completedAdicChangeData U
    (completedCoefficientMap q (pbcIntegralDatum l E))).choose_spec.choose_spec.choose
      ((proEtaleModuleInverseImage q _).map a)]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The ordinary module comparison is identity on the specified sheafified tensors.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcOrdinaryModuleIso : completedModulePullback q (pbcIntegralDatum l E) ≅
    proEtaleRingModulePullback q
      (pbcAdicCompletion V (pbcIntegralDatum l E))
      (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q) :=
  NatIso.ofComponents (fun M ↦ sbcOrdinaryModuleIsoApp l E q M)
    (fun {M N} a ↦ sbcOrdinaryModuleIso_naturality l E q M N a)

/-- Additivity of the exact ordinary tensor functor at these specified coefficients.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance sbcOrdinaryModule_additive :
    (proEtaleRingModulePullback q
      (pbcAdicCompletion V (pbcIntegralDatum l E))
      (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q)).Additive :=
  proEtaleRingModulePullback_additive q
    (pbcAdicCompletion V (pbcIntegralDatum l E))
    (pbcAdicCompletion U (pbcIntegralDatum l E)) (sbcCoefficientIso l E q)

/-- Zero-morphism preservation from the specified additive module pullback.
The explicit instance avoids an extra recursive instance search through coefficients.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance sbcOrdinaryModule_preservesZero :
    (proEtaleRingModulePullback q
      (pbcAdicCompletion V (pbcIntegralDatum l E))
      (pbcAdicCompletion U (pbcIntegralDatum l E))
      (sbcCoefficientIso l E q)).PreservesZeroMorphisms :=
  haveI := sbcOrdinaryModule_additive l E q
  Functor.preservesZeroMorphisms_of_additive _

/-- The canonical derived comparison retains the universal counit on every complex.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: the exact ordinary pullback is a total left derived functor of module pullback.
Its factorization composed with the normalized module comparison is the required
counit. Uniqueness of left derived functors gives the unique counit-preserving iso.
K-flat resolutions compute the same map, so this includes arbitrary unbounded objects. -/
theorem sbcOrdinaryDerivedIso_exists :
    ∃! e : completedOrdinaryPullback q (pbcIntegralDatum l E) ≅ sbcOrdinaryPull l E q,
      ∀ P : CochainComplex (pbcModules V (pbcAdicCompletion V (pbcIntegralDatum l E))) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (proEtaleRingDerivedPullbackFactors q
            (pbcAdicCompletion V (pbcIntegralDatum l E))
            (pbcAdicCompletion U (pbcIntegralDatum l E))
            (sbcCoefficientIso l E q)).hom.app P =
        Functor.leftDerivedCounitOnComplex
          (completedModulePullback q (pbcIntegralDatum l E))
          (completedOrdinaryPullback q (pbcIntegralDatum l E))
          (completedOrdinaryPullbackCounit q (pbcIntegralDatum l E)) P ≫
        DerivedCategory.Q.map ((@NatIso.mapHomologicalComplex ℤ _ _ _ _ _ _ _ _
          (Functor.preservesZeroMorphisms_of_additive
            (completedModulePullback q (pbcIntegralDatum l E)))
          (sbcOrdinaryModule_preservesZero l E q)
          (sbcOrdinaryModuleIso l E q) (.up ℤ)).hom.app P) := by
  sorry

/-- The ordinary comparison is fixed by the actual tensor counit, not an arbitrary iso.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcOrdinaryDerivedIso := (sbcOrdinaryDerivedIso_exists l E q).exists.choose

/-- Package the landed completed-pullback object construction with its actual maps.
This is the same reduction, strict tower pullback and derived limit composite.
Source: blueprint order 1442; Stacks 099N
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcCompletedPullbackFunctor :
    PbcCompletedDerived V (pbcIntegralDatum l E) ⥤
      PbcCompletedDerived U (pbcIntegralDatum l E) :=
  completedReductionTower V (pbcIntegralDatum l E) ⋙
    completedTowerPullback q (pbcIntegralDatum l E) ⋙
      completedTowerRlim (pbcIntegralDatum l E) U

/-- Ordinary pullback followed by the strict-reduction-tower completion unit.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcCompletionUnit (K : PbcCompletedDerived V (pbcIntegralDatum l E)) :
    (sbcOrdinaryPull l E q).obj K ⟶ completedPullbackObject q (pbcIntegralDatum l E) K :=
  (sbcOrdinaryDerivedIso l E q).inv.app K ≫
    completedPullbackComparison q (pbcIntegralDatum l E) K

/-- The actual operations preserve intrinsic completeness.
Source: Stacks 099N and 099K (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: completed pullback is the intrinsic completion by the constant/completed
comparison. For direct image, compute intrinsic completion by the Koszul products
and mapping fibres. Direct image commutes with limits and is linear in the generators;
its derived functor commutes with these homotopy limits. Thus it carries a complete
object to a complete object. No scheme finiteness or constructibility is used. -/
theorem sbcOperations_preserveComplete :
    (∀ K : PbcComplete l E V, IsPbcComplete l E U
      ((sbcCompletedPullbackFunctor l E q).obj K.obj)) ∧
    (∀ K : PbcComplete l E U, IsPbcComplete l E V
      ((sbcAmbientPush l E q).obj K.obj)) := by
  sorry

/-- Restrict the actual completed-pullback functor to complete objects.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcPull : PbcComplete l E V ⥤ PbcComplete l E U :=
  (IsPbcComplete l E U).lift
    (ObjectProperty.ι (IsPbcComplete l E V) ⋙ sbcCompletedPullbackFunctor l E q)
    (sbcOperations_preserveComplete l E q).1

/-- Restrict the actual derived direct-image functor to complete objects.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcPush : PbcComplete l E U ⥤ PbcComplete l E V :=
  (IsPbcComplete l E V).lift (ObjectProperty.ι (IsPbcComplete l E U) ⋙ sbcAmbientPush l E q)
    (sbcOperations_preserveComplete l E q).2

/-- Both restrictions are additive and linear for the specified constant sections.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: module inverse image and extension preserve addition and constant scalars on
pure tensors. Direct image does so sectionwise; on derived Hom groups compute with
K-injective representatives and chain maps. Completion uses products, tensor and
mapping fibres, which preserve the same scalar operations. The full subcategories
inherit exactly these Hom actions. -/
theorem sbcOperations_linear :
    (sbcPull l E q).Additive ∧ (sbcPush l E q).Additive ∧
      (sbcPull l E q).Linear (PbcIntegralRing l E) ∧
      (sbcPush l E q).Linear (PbcIntegralRing l E) := by
  sorry

/-- Additivity of completed pullback.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance sbcPull_additive : (sbcPull l E q).Additive := (sbcOperations_linear l E q).1
/-- Additivity of completed direct image.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance sbcPush_additive : (sbcPush l E q).Additive := (sbcOperations_linear l E q).2.1
/-- Constant-section scalar linearity of completed pullback.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance sbcPull_linear : (sbcPull l E q).Linear (PbcIntegralRing l E) :=
  (sbcOperations_linear l E q).2.2.1
/-- Constant-section scalar linearity of completed direct image.
Source: blueprint order 1442
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
instance sbcPush_linear : (sbcPush l E q).Linear (PbcIntegralRing l E) :=
  (sbcOperations_linear l E q).2.2.2

/-- The complete adjunction is uniquely normalized by the ordinary unit and completion.
Source: Stacks 099K (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: completion is the reflector onto intrinsic complete objects. For complete N,
precomposition by the completion unit gives Hom(PM,N)=Hom(LM,N). Compose with the
canonical ordinary derived module adjunction. The resulting Hom equivalence defines
an adjunction and its unit is the displayed composite. Its unit determines it uniquely. -/
theorem sbcAdjunction_exists :
    ∃! adj : sbcPull l E q ⊣ sbcPush l E q,
      ∀ M : PbcComplete l E V, (adj.unit.app M).hom =
        (proEtaleRingDerivedAdjunction q
          (pbcAdicCompletion V (pbcIntegralDatum l E))
          (pbcAdicCompletion U (pbcIntegralDatum l E))
          (sbcCoefficientIso l E q)).unit.app M.obj ≫
        (sbcAmbientPush l E q).map (sbcCompletionUnit l E q M.obj) := by
  sorry

/-- The canonical completed adjunction with its fixed tensor-unit normalization.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcAdjunction := (sbcAdjunction_exists l E q).exists.choose

variable {U V : Scheme.{u}} (q : U ⟶ V)

/-- Retain the prescribed finite coefficient identification, with no extra choice.
Source: blueprint order 1444 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcFiniteCoefficientIso (n : ℕ) :=
  letI := completedFiniteCoefficientMap_isIso q (pbcIntegralDatum l E) n
  asIso (completedFiniteCoefficientMap q (pbcIntegralDatum l E) n)

/-- Ordinary, uncompleted, quotient-coefficient inverse image.
Source: blueprint order 1444 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev sbcFinitePull (n : ℕ) := proEtaleRingDerivedPullback q
  (((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n)))
  (((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n))) (sbcFiniteCoefficientIso l E q n)

/-- Ordinary K-injective quotient-coefficient direct image, without completion.
Source: blueprint order 1444 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev sbcFinitePush (n : ℕ) := proEtaleRingDerivedDirectImage q
  (((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n)))
  (((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n))) (sbcFiniteCoefficientIso l E q n)


/-- Completed coefficient identifications commute with composition.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: project to any finite quotient. Both maps are the canonical successive
inverse-image maps of a constant finite sheaf. Their composition law agrees on
constant sections, hence everywhere; the completed limit projections are jointly monic. -/
theorem sbcCoefficientComp {Z : Scheme.{u}} (v : Z ⟶ U) :
    proEtaleRingCompositeCoefficients v q
      (pbcAdicCompletion V (pbcIntegralDatum l E))
      (pbcAdicCompletion U (pbcIntegralDatum l E))
      (pbcAdicCompletion Z (pbcIntegralDatum l E))
      (sbcCoefficientIso l E q) (sbcCoefficientIso l E v) =
        sbcCoefficientIso l E (v ≫ q) := by
  sorry

/-- Ordinary pullback composition, with the tensor and coefficient normalizations.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcOrdinaryComp {Z : Scheme.{u}} (v : Z ⟶ U) :
    sbcOrdinaryPull l E q ⋙ sbcOrdinaryPull l E v ≅ sbcOrdinaryPull l E (v ≫ q) :=
  (proEtaleCanonicalDerivedPullbackComparison v q
    (pbcAdicCompletion V (pbcIntegralDatum l E))
    (pbcAdicCompletion U (pbcIntegralDatum l E))
    (pbcAdicCompletion Z (pbcIntegralDatum l E))
    (sbcCoefficientIso l E q) (sbcCoefficientIso l E v)).symm ≪≫
      eqToIso (congrArg (fun c ↦ proEtaleRingDerivedPullback (v ≫ q)
        (pbcAdicCompletion V (pbcIntegralDatum l E))
        (pbcAdicCompletion Z (pbcIntegralDatum l E)) c)
        (sbcCoefficientComp l E q v))

/-- The canonical completed composition iso, characterized by the two completion units.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: completion of successive ordinary pullbacks agrees with successive completed
pullback by the reflector property. Extend the ordinary composition iso across the
units; extend its inverse in the reverse direction. Uniqueness of extension gives
the inverse identities and naturality. This is the unit-preserving conjugate of the
canonical derived direct-image composition, so agrees with composite adjunctions. -/
theorem sbcPullComp_exists {Z : Scheme.{u}} (v : Z ⟶ U) :
    ∃! t : sbcPull l E q ⋙ sbcPull l E v ≅ sbcPull l E (v ≫ q),
      ∀ K : PbcComplete l E V,
        (sbcOrdinaryPull l E v).map (sbcCompletionUnit l E q K.obj) ≫
          sbcCompletionUnit l E v ((sbcPull l E q).obj K).obj ≫
          (t.hom.app K).hom =
        (sbcOrdinaryComp l E q v).hom.app K.obj ≫ sbcCompletionUnit l E (v ≫ q) K.obj := by
  sorry

/-- Canonical natural composition comparison, with its unit characterization retained.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcPullComp {Z : Scheme.{u}} (v : Z ⟶ U) :=
  (sbcPullComp_exists l E q v).exists.choose

/-- Canonical quotient-linear reduction of an ambient completed complex.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev sbcReduction (W : Scheme.{u}) (n : ℕ) :=
  pbcCompletedReduction W (pbcIntegralDatum l E) n

/-- The completed and finite coefficient identifications form the projection square.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: this is precisely the finite-projection characterization of the completed
coefficient map; replacing the two invertible maps by asIso changes no homomorphism. -/
theorem sbcProjectionSquare (n : ℕ) :
    (sbcCoefficientIso l E q).hom ≫ pbcAdicProjection U (pbcIntegralDatum l E) n =
      (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map
        (pbcAdicProjection V (pbcIntegralDatum l E) n) ≫
          (sbcFiniteCoefficientIso l E q n).hom := by
  change completedCoefficientMap q (pbcIntegralDatum l E) ≫
    pbcAdicProjection U (pbcIntegralDatum l E) n = _
  exact limit.lift_π _ (op n)

/-- Restriction comparison is the recorded identity-on-sections coefficient square.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcRestrictionPull (n : ℕ) :=
  proEtaleRingRestrictionDerivedPullback q
    (pbcAdicCompletion V (pbcIntegralDatum l E))
    (((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n)))
    (pbcAdicCompletion U (pbcIntegralDatum l E))
    (((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n)))
    (pbcAdicProjection V (pbcIntegralDatum l E) n)
    (pbcAdicProjection U (pbcIntegralDatum l E) n)
    (sbcCoefficientIso l E q) (sbcFiniteCoefficientIso l E q n)
    (sbcProjectionSquare l E q n)

/-- Ordinary pullback/reduction comparison is the scalar-adjunction mate of restriction.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcOrdinaryReductionMap (n : ℕ) :
    sbcOrdinaryPull l E q ⋙ sbcReduction l E U n ⟶
      sbcReduction l E V n ⋙ sbcFinitePull l E q n :=
  ((mateEquiv
    (AlgebraicGeometry.Scheme.pbcDerivedScalarAdjunction
      (pbcAdicProjection V (pbcIntegralDatum l E) n))
    (AlgebraicGeometry.Scheme.pbcDerivedScalarAdjunction
      (pbcAdicProjection U (pbcIntegralDatum l E) n))).symm
        (TwoSquare.mk _ _ _ _ (sbcRestrictionPull l E q n).inv)).natTrans

/-- The ordinary comparison is tensor balancing on K-flat representatives.
Source: Stacks 07A4 and 06YY (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: take a flat-term K-flat resolution. Exact inverse image preserves the
corresponding acyclic tensor tests. Both composites are its pullback tensored with
the same quotient; their unit-normalized mate is balancing, whose reverse is its
inverse. Localization gives an isomorphism on every derived object. -/
theorem sbcOrdinaryReductionMap_isIso (n : ℕ) :
    IsIso (sbcOrdinaryReductionMap l E q n) := by
  sorry

/-- Reduction turns the completion unit into an isomorphism.
Source: Stacks 099N(5) (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: the quotient has a two-term finite-free resolution. Tensoring the intrinsic
Koszul completion tower with it kills all negative Koszul transition summands on a
cofinal tail. The remaining summand is the constant quotient reduction, with the
reduced completion unit its identity. The strict-tower comparison preserves this
unit, so the same assertion holds for completedPullback and sbcCompletionUnit. -/
theorem sbcCompletionUnit_reduction_isIso (n : ℕ) (K : PbcComplete l E V) :
    IsIso ((sbcReduction l E U n).map (sbcCompletionUnit l E q K.obj)) := by
  sorry

/-- The finite reduction of completed pullback, with its projection/unit normalization.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcPullReduction (n : ℕ) (K : PbcComplete l E V) :
    (sbcReduction l E U n).obj ((sbcPull l E q).obj K).obj ⟶
      (sbcFinitePull l E q n).obj ((sbcReduction l E V n).obj K.obj) :=
  letI := sbcCompletionUnit_reduction_isIso l E q n K
  inv ((sbcReduction l E U n).map (sbcCompletionUnit l E q K.obj)) ≫
    (sbcOrdinaryReductionMap l E q n).app K.obj

/-- The pushforward comparison is the canonical mate of ordinary pullback/reduction.
It is the finite-perfect projection-formula map, rather than a selected isomorphism.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcPushReduction (n : ℕ) (K : PbcComplete l E U) :
    (sbcReduction l E V n).obj ((sbcPush l E q).obj K).obj ⟶
      (sbcFinitePush l E q n).obj ((sbcReduction l E U n).obj K.obj) :=
  letI := sbcOrdinaryReductionMap_isIso l E q n
  (proEtaleRingDerivedAdjunction q
    (((pbcAdicRings V (pbcIntegralDatum l E)).obj (op n)))
    (((pbcAdicRings U (pbcIntegralDatum l E)).obj (op n)))
    (sbcFiniteCoefficientIso l E q n)).unit.app _ ≫
  (sbcFinitePush l E q n).map
    (inv ((sbcOrdinaryReductionMap l E q n).app ((sbcPush l E q).obj K).obj)) ≫
  (sbcFinitePush l E q n).map ((sbcReduction l E U n).map
    ((proEtaleRingDerivedAdjunction q
      (pbcAdicCompletion V (pbcIntegralDatum l E))
      (pbcAdicCompletion U (pbcIntegralDatum l E))
      (sbcCoefficientIso l E q)).counit.app K.obj))

/-- Both canonical finite comparisons are invertible.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: the pullback comparison is the composite of two already invertible maps.
The pushforward mate is the projection formula for the globally strict-perfect
coefficient quotient. Compute that quotient by the two-term free complex for the
uniformizer power. Derived direct image commutes with the finite sums, shifts and
cones in that complex, and the displayed mate is identity on the free generator.
This proves invertibility without any boundedness or finiteness condition on q. -/
theorem sbcReductionComparisons_isIso (n : ℕ) :
    (∀ K : PbcComplete l E V, IsIso (sbcPullReduction l E q n K)) ∧
      (∀ K : PbcComplete l E U, IsIso (sbcPushReduction l E q n K)) := by
  sorry

variable {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g)

/-- The two composite coefficient identifications agree on every finite projection.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: both send the constant residue of a to the same constant residue after inverse
image. This proves equality at each finite quotient, and the limit projections determine
the completed map. Transport along square commutativity gives the stated heterogeneous equality. -/
theorem sbcCoefficientSquare (_square : ChosenCartesianSquare h e f g) : HEq
    (proEtaleRingCompositeCoefficients h f
      (pbcAdicCompletion S (pbcIntegralDatum l E))
      (pbcAdicCompletion X (pbcIntegralDatum l E))
      (pbcAdicCompletion Y (pbcIntegralDatum l E))
      (sbcCoefficientIso l E f) (sbcCoefficientIso l E h))
    (proEtaleRingCompositeCoefficients e g
      (pbcAdicCompletion S (pbcIntegralDatum l E))
      (pbcAdicCompletion T (pbcIntegralDatum l E))
      (pbcAdicCompletion Y (pbcIntegralDatum l E))
      (sbcCoefficientIso l E g) (sbcCoefficientIso l E e)) := by
  rw [sbcCoefficientComp, sbcCoefficientComp]
  have aux : ∀ (a b : Y ⟶ S), a = b →
      HEq (sbcCoefficientIso l E a) (sbcCoefficientIso l E b) := by
    intro a b hab
    subst b
    rfl
  exact aux _ _ _square.w

/-- The ordinary tensor-normalized comparison, in the orientation used by exchange.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcOrdinaryTheta : sbcOrdinaryPull l E f ⋙ sbcOrdinaryPull l E h ≅
    sbcOrdinaryPull l E g ⋙ sbcOrdinaryPull l E e :=
  (proEtaleAmbientRingedPullbackComparison sq
    (pbcAdicCompletion X (pbcIntegralDatum l E))
    (pbcAdicCompletion S (pbcIntegralDatum l E))
    (pbcAdicCompletion Y (pbcIntegralDatum l E))
    (pbcAdicCompletion T (pbcIntegralDatum l E))
    (sbcCoefficientIso l E f) (sbcCoefficientIso l E g)
    (sbcCoefficientIso l E h) (sbcCoefficientIso l E e)
    (sbcCoefficientSquare l E sq)).symm

/-- The completed square comparison is fixed by ordinary pullback and the two units.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: successive completion is completion of successive ordinary pullback, by the
reflector property and compatibility of the coefficient ideals. The ordinary theta
therefore extends uniquely across the two completion units. Its inverse extends the
ordinary inverse, so the extension is an isomorphism. This is equivalently the
composition comparison obtained by uniqueness of the composite adjunction. -/
theorem sbcTheta_exists :
    ∃! t : sbcPull l E f ⋙ sbcPull l E h ≅ sbcPull l E g ⋙ sbcPull l E e,
      ∀ K : PbcComplete l E S,
        (sbcOrdinaryPull l E h).map (sbcCompletionUnit l E f K.obj) ≫
          sbcCompletionUnit l E h ((sbcPull l E f).obj K).obj ≫
          (t.hom.app K).hom =
        (sbcOrdinaryTheta l E sq).hom.app K.obj ≫
          (sbcOrdinaryPull l E e).map (sbcCompletionUnit l E g K.obj) ≫
          sbcCompletionUnit l E e ((sbcPull l E g).obj K).obj := by
  sorry

/-- The square comparison with the ordinary-unit normalization retained.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcTheta := (sbcTheta_exists l E sq).exists.choose

/-- The specified unit/comparison/counit mate, as an actual component morphism.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcExchangeApp (K : PbcComplete l E T) :
    (sbcPull l E f).obj ((sbcPush l E g).obj K) ⟶
      (sbcPush l E h).obj ((sbcPull l E e).obj K) :=
  (sbcAdjunction l E h).unit.app _ ≫
    (sbcPush l E h).map ((sbcTheta l E sq).hom.app ((sbcPush l E g).obj K)) ≫
    (sbcPush l E h).map ((sbcPull l E e).map ((sbcAdjunction l E g).counit.app K))

/-- The mate is natural, without an invertibility or finiteness assumption.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: apply the naturality equations for the unit, theta and counit, and functoriality
of the two operations. Associativity pastes the three squares into the required square.
Finite reduction preserves this construction: normalized pullback and direct-image
comparisons carry its unit and counit to the ordinary finite units and counits, and
carry theta to finite tensor balancing. Applying derived inverse limit gives the same
completed mate. Thus the construction agrees with finite-level completed exchange. -/
theorem sbcExchange_naturality {K K' : PbcComplete l E T} (a : K ⟶ K') :
    (sbcPush l E g ⋙ sbcPull l E f).map a ≫ sbcExchangeApp l E sq K' =
      sbcExchangeApp l E sq K ≫ (sbcPull l E e ⋙ sbcPush l E h).map a := by
  let η := Functor.whiskerLeft (sbcPush l E g ⋙ sbcPull l E f) (sbcAdjunction l E h).unit
  let θ := Functor.whiskerRight (Functor.whiskerLeft (sbcPush l E g) (sbcTheta l E sq).hom)
    (sbcPush l E h)
  let ε := Functor.whiskerRight (Functor.whiskerRight (sbcAdjunction l E g).counit (sbcPull l E e))
    (sbcPush l E h)
  exact (η ≫ θ ≫ ε).naturality a

/-- The integral natural exchange is the specified adjunction mate.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcExchange : sbcPush l E g ⋙ sbcPull l E f ⟶ sbcPull l E e ⋙ sbcPush l E h where
  app K := sbcExchangeApp l E sq K
  naturality {_K _K'} a := sbcExchange_naturality l E sq a

/-- The finite coefficient square commutes, with the same projection normalization.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: all four maps are inverse-image identifications of the constant finite
quotient ring. Both composites are equal on constant residues and hence equal after
sheafification; transport by square commutativity gives the heterogeneous equality. -/
theorem sbcFiniteCoefficientSquare (_square : ChosenCartesianSquare h e f g) (n : ℕ) : HEq
    (proEtaleRingCompositeCoefficients h f
      (((pbcAdicRings S (pbcIntegralDatum l E)).obj (op n)))
      (((pbcAdicRings X (pbcIntegralDatum l E)).obj (op n)))
      (((pbcAdicRings Y (pbcIntegralDatum l E)).obj (op n)))
      (sbcFiniteCoefficientIso l E f n) (sbcFiniteCoefficientIso l E h n))
    (proEtaleRingCompositeCoefficients e g
      (((pbcAdicRings S (pbcIntegralDatum l E)).obj (op n)))
      (((pbcAdicRings T (pbcIntegralDatum l E)).obj (op n)))
      (((pbcAdicRings Y (pbcIntegralDatum l E)).obj (op n)))
      (sbcFiniteCoefficientIso l E g n) (sbcFiniteCoefficientIso l E e n)) := by
  sorry

/-- Finite ordinary pullback comparison with the recorded tensor normalization.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcFiniteTheta (n : ℕ) :=
  (proEtaleAmbientRingedPullbackComparison sq
    (((pbcAdicRings X (pbcIntegralDatum l E)).obj (op n)))
    (((pbcAdicRings S (pbcIntegralDatum l E)).obj (op n)))
    (((pbcAdicRings Y (pbcIntegralDatum l E)).obj (op n)))
    (((pbcAdicRings T (pbcIntegralDatum l E)).obj (op n)))
    (sbcFiniteCoefficientIso l E f n) (sbcFiniteCoefficientIso l E g n)
    (sbcFiniteCoefficientIso l E h n) (sbcFiniteCoefficientIso l E e n)
    (sbcFiniteCoefficientSquare l E sq n)).symm

/-- The ordinary finite-level unit/comparison/counit exchange.
Source: Stacks 07A7 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcFiniteExchangeApp (n : ℕ)
    (K : DerivedCategory
      (pbcModules T ((pbcAdicRings T (pbcIntegralDatum l E)).obj (op n)))) :
    (sbcFinitePull l E f n).obj ((sbcFinitePush l E g n).obj K) ⟶
      (sbcFinitePush l E h n).obj ((sbcFinitePull l E e n).obj K) :=
  (proEtaleRingDerivedAdjunction h
    (((pbcAdicRings X (pbcIntegralDatum l E)).obj (op n)))
    (((pbcAdicRings Y (pbcIntegralDatum l E)).obj (op n)))
    (sbcFiniteCoefficientIso l E h n)).unit.app _ ≫
  (sbcFinitePush l E h n).map ((sbcFiniteTheta l E sq n).hom.app
    ((sbcFinitePush l E g n).obj K)) ≫
  (sbcFinitePush l E h n).map ((sbcFinitePull l E e n).map
    ((proEtaleRingDerivedAdjunction g
      (((pbcAdicRings S (pbcIntegralDatum l E)).obj (op n)))
      (((pbcAdicRings T (pbcIntegralDatum l E)).obj (op n)))
      (sbcFiniteCoefficientIso l E g n)).counit.app K))

/-- Finite reduction identifies the specified completed mate with finite exchange.
Source: blueprint order 1442; Stacks 099N and 07A7
(blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: expand the three-factor mate. The completed adjunction unit is the ordinary
unit followed by the completion unit, and its counit is characterized by the inverse
equation. Reduction inverts the completion unit. The ordinary scalar-extension
comparisons are mates of identity on sections, so they preserve the ordinary units
and counits. The normalization of theta reduces to finite tensor balancing. Substitute
these three identities in the composite, cancel the inverse reduced completion units,
and use functoriality to obtain exactly the displayed equation. Compatibility with
all quotient transitions follows on the same tensor representatives. The comparisons
with derived inverse limits preserve the defining projections, so their inverse-limit
mate is the same completed exchange, not another map with just isomorphic endpoints. -/
theorem sbcCompletedOperations_linear_natural_exchange
    (K : PbcComplete l E T) (n : ℕ) :
    (sbcReduction l E X n).map (sbcExchangeApp l E sq K).hom ≫
        sbcPushReduction l E h n ((sbcPull l E e).obj K) ≫
        (sbcFinitePush l E h n).map (sbcPullReduction l E e n K) =
      sbcPullReduction l E f n ((sbcPush l E g).obj K) ≫
        (sbcFinitePull l E f n).map (sbcPushReduction l E g n K) ≫
        sbcFiniteExchangeApp l E sq n ((sbcReduction l E T n).obj K.obj) := by
  sorry

/-- The ordinary ambient exchange, before completion, with its actual three factors.
Source: blueprint order 1442, proof steps 8-11; Stacks 07A7
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcOrdinaryExchangeApp (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    (sbcOrdinaryPull l E f).obj ((sbcAmbientPush l E g).obj K) ⟶
      (sbcAmbientPush l E h).obj ((sbcOrdinaryPull l E e).obj K) :=
  (proEtaleRingDerivedAdjunction h
    (pbcAdicCompletion X (pbcIntegralDatum l E))
    (pbcAdicCompletion Y (pbcIntegralDatum l E))
    (sbcCoefficientIso l E h)).unit.app _ ≫
  (sbcAmbientPush l E h).map ((sbcOrdinaryTheta l E sq).hom.app
    ((sbcAmbientPush l E g).obj K)) ≫
  (sbcAmbientPush l E h).map ((sbcOrdinaryPull l E e).map
    ((proEtaleRingDerivedAdjunction g
      (pbcAdicCompletion S (pbcIntegralDatum l E))
      (pbcAdicCompletion T (pbcIntegralDatum l E))
      (sbcCoefficientIso l E g)).counit.app K))

/-- The actual strict reduction tower followed by its derived inverse limit.
Source: blueprint order 1442, proof steps 8-10; Stacks 099N
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
abbrev sbcTowerCompletion (W : Scheme.{u}) :=
  completedReductionTower W (pbcIntegralDatum l E) ⋙
    completedTowerRlim (pbcIntegralDatum l E) W

/-- The strict quotient unit followed by derived limit, including its constant-tower unit.
Source: blueprint order 1442, proof step 10; Stacks 099N
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcTowerCompletionUnit (W : Scheme.{u})
    (M : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    M ⟶ (sbcTowerCompletion l E W).obj M :=
  (completedConstantRlimUnit (pbcIntegralDatum l E) W).app M ≫
    (completedTowerRlim (pbcIntegralDatum l E) W).map
      ((completedReductionTowerUnit (pbcIntegralDatum l E) W).app M)

/-- The source comparison is uniquely fixed by the ordinary completion unit.
Source: blueprint order 1442, proof steps 8-11; Stacks 099N
(blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: on a flat-term K-flat representative, tensor balancing identifies the pulled-back
strict reduction tower with the reduction tower of ordinary pullback, including every
transition. Derived limit carries its strict quotient unit to the displayed unit.
Both targets are derived completions of the same ordinary source. The reflector
bijection gives the unit-preserving isomorphism and its uniqueness. -/
theorem sbcStrictSourceComparison_exists (_sq : ChosenCartesianSquare h e f g)
    (K : PbcComplete l E T) :
    ∃! a : ((sbcPull l E f).obj ((sbcPush l E g).obj K)).obj ≅
        (sbcTowerCompletion l E X).obj
          ((sbcOrdinaryPull l E f).obj ((sbcAmbientPush l E g).obj K.obj)),
      sbcCompletionUnit l E f ((sbcAmbientPush l E g).obj K.obj) ≫ a.hom =
        sbcTowerCompletionUnit l E X
          ((sbcOrdinaryPull l E f).obj ((sbcAmbientPush l E g).obj K.obj)) := by
  sorry

/-- The source comparison retaining the strict quotient-unit normalization.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcStrictSourceComparison (K : PbcComplete l E T) :=
  (sbcStrictSourceComparison_exists l E sq K).exists.choose

/-- The target comparison is the perfect projection-formula and direct-image/limit map.
Source: blueprint order 1442, proof steps 8-11; Stacks 099N and 099K
(blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: the canonical scalar-adjunction mate compares the reduction of Rh_*M with
Rh_* of the reduction of M. The finite coefficient quotient is perfect by its two-term
free resolution, so this projection map is an isomorphism. Construct these maps on
the strict diagram site, where the quotient maps give their compatibility. Apply
Rlim and the canonical direct-image/limit comparison. The completion unit is taken
to Rh_* of the completion unit: at coefficient A the projection map is the adjunct
of the counit and hence the identity; naturality in every A-to-quotient map gives the
strict unit equation. Both targets are complete and the reduced comparison is an
isomorphism, giving an isomorphism by the completion comparison. Finally the source
is the reflector of the ordinary object, so this unit equation determines the map
uniquely. This uses no geometric or constructibility condition on the square. -/
theorem sbcStrictTargetComparison_exists (_sq : ChosenCartesianSquare h e f g)
    (K : PbcComplete l E T) :
    ∃! b : (sbcTowerCompletion l E X).obj
        ((sbcAmbientPush l E h).obj ((sbcOrdinaryPull l E e).obj K.obj)) ≅
          ((sbcPush l E h).obj ((sbcPull l E e).obj K)).obj,
      sbcTowerCompletionUnit l E X
          ((sbcAmbientPush l E h).obj ((sbcOrdinaryPull l E e).obj K.obj)) ≫ b.hom =
        (sbcAmbientPush l E h).map (sbcCompletionUnit l E e K.obj) := by
  sorry

/-- The target comparison with its fixed projection-formula normalization.
Source: blueprint order 1442 (blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcStrictTargetComparison (K : PbcComplete l E T) :=
  (sbcStrictTargetComparison_exists l E sq K).exists.choose

/-- Strict realization of finite exchange: apply reduction to the actual ordinary mate.
Its canonical projection-formula conjugates are the finite mates on the diagram site;
this specifies a strict derived map rather than selecting one from its evaluations.
Source: blueprint order 1442, proof steps 8-9
(blueprint: lem-sbc-completed-operations-linear-natural-exchange). -/
def sbcStrictExchange (K : PbcComplete l E T) :=
  (completedReductionTower X (pbcIntegralDatum l E)).map
    (sbcOrdinaryExchangeApp l E sq K.obj)

/-- The specified completed mate equals the derived inverse limit of strict exchange.
Together with the finite-reduction equality above, this records both clauses of the
node: the finite mates and their strict completed realization are the named map.
Source: blueprint order 1442, proof steps 8-11
(blueprint: lem-sbc-completed-operations-linear-natural-exchange).
Proof: the diagram-site unit-square-counit mate is conjugate to reduction of the
ordinary mate by the perfect projection-formula maps. Tensor-exchange coherence
proves this as an equality on the strict diagram site, with no inference from equal
finite evaluations. The canonical component calculations are exactly the finite
exchange equation already recorded above. Apply Rlim to this strict equality. The
source and target comparisons are the unit-normalized ones just defined. The
resulting arrow gamma satisfies gamma j_f = Rh_*(j_e) Ex_ordinary by the strict
quotient-unit equation. Expand the completed three-factor mate and use the
unit-normalized theta and adjunction to obtain the same equation for sbcExchangeApp.
Its target is complete, so the injective part of the completion reflector bijection
cancels j_f and proves the displayed equality. No finite exchange was inverted. -/
theorem sbcCompletedExchange_strictLimit (K : PbcComplete l E T) :
    (sbcExchangeApp l E sq K).hom =
      (sbcStrictSourceComparison l E sq K).hom ≫
        (completedTowerRlim (pbcIntegralDatum l E) X).map
          (sbcStrictExchange l E sq K) ≫
        (sbcStrictTargetComparison l E sq K).hom := by
  sorry

end WeilConjectures
