/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Paper.AdicLisseCohomologyCalculus
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.EtaleWeilFundamentalRepresentation
public import Sheaf.Paper.LisseAdicAutomorphismPullback
public import Sheaf.Paper.LisseRationalRealizationData
public import Sheaf.Paper.LissePullbackNormalization
public import Sheaf.Paper.LisseCompletedSystemData
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Normalized classical Weil realization data

The canonical Frobenius comparison is pinned by the ordinary-unit normalization
of BS 6.8.15 and the finite-level completed-system normalization of BS 6.8.4(4).
(blueprint: def-zl-normalized-classical-weil-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Endofunctor (IsoAlgebra)
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct
namespace WeilConjectures
open AlgebraicallyClosedCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

/-- Inherited noetherianity of the finite-type geometric fibre.
Source: BS 6.8.4 hypotheses
(blueprint: def-zl-normalized-classical-weil-realization). -/
instance zlClassicalNoetherian : IsNoetherian (D.geometricFiber Y₀).left :=
  { toIsLocallyNoetherian := by
      change IsLocallyNoetherian (Limits.pullback Y₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      infer_instance
    toCompactSpace := by
      exact QuasiCompact.compactSpace_of_compactSpace
        (Limits.pullback.snd Y₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) }

/-- Inherited separatedness of the geometric fibre.
Source: BS 6.8.4 hypotheses
(blueprint: def-zl-normalized-classical-weil-realization). -/
instance zlClassicalSeparated : (D.geometricFiber Y₀).left.IsSeparated := by
  change (Limits.pullback Y₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).IsSeparated
  refine ⟨?_⟩
  rw [← terminal.comp_from (Limits.pullback.snd Y₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))]
  infer_instance

/-- The existing residue-field unit supplies the stalk-unit convention of the
normalized adic realization. This is inherited data, not a geometric assumption.
Source: blueprint coefficient convention; BS 6.8.4
(blueprint: def-zl-normalized-classical-weil-realization). -/
@[instance_reducible]
def zlClassicalStalkInvertible (x : (D.geometricFiber Y₀).left) :
    Invertible (l : (D.geometricFiber Y₀).left.presheaf.stalk x) :=
  (isUnit_of_map_unit
    (IsLocalRing.residue ((D.geometricFiber Y₀).left.presheaf.stalk x))
    (l : (D.geometricFiber Y₀).left.presheaf.stalk x)
    (by
      simpa only [map_natCast] using
        (@isUnit_of_invertible ((D.geometricFiber Y₀).left.residueField x) _
          (l : (D.geometricFiber Y₀).left.residueField x)
          (sfWeilPrimeInvertible D l hl Y₀ x)))).invertible

variable [hUnits : Fact (∀ x : (D.geometricFiber Y₀).left,
  IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x))]

/-- The source is the recorded classical adic Weil category, with rational Weil maps.
Source: Weil II (1.1.1), (1.1.10)
(blueprint: def-zl-normalized-classical-weil-realization). -/
abbrev ZlClassicalWeil :=
  EtaleLisseWeilSheaf l Ω (D.geometricFrobenius Y₀)

/-- The actual geometric base used by the normalized finite-field realization.
Source: BS 6.8.14, geometric base convention
(blueprint: def-zl-normalized-classical-weil-realization). -/
def zlRealizationBase : LisseRealization.Base D l hl where
  scheme := (D.geometricFiber Y₀).left
  «over» := ⟨(D.geometricFiber Y₀).hom⟩
  finiteType := by
    change LocallyOfFiniteType (Limits.pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance
  quasiCompact := by
    change QuasiCompact (Limits.pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance

/-- The same base with the actual finite coefficient subfield, for completed systems.
Source: BS 6.8.4(1),(4)
(blueprint: def-zl-normalized-classical-weil-realization). -/
def zlCompletedBase (E : Padic.FiniteCoefficientFields l Ω) :
    AlgebraicGeometry.ProEtale.CompletedLisse.Base l where
  E := E.val
  field := inferInstance
  algebra := inferInstance
  finiteDimensional := inferInstance
  X := (D.geometricFiber Y₀).left
  noetherian := inferInstance
  separated := inferInstance
  invertible := adicCalculusPrimeInvertible l (D.geometricFiber Y₀).left

/-- The actual Frobenius map with identity on the finite coefficient field.
Source: BS 6.8.15
(blueprint: def-zl-normalized-classical-weil-realization). -/
def zlCompletedFrobenius (E : Padic.FiniteCoefficientFields l Ω) :
    AlgebraicGeometry.ProEtale.CompletedLisse.Arrow l
      (zlCompletedBase D l Ω Y₀ E) (zlCompletedBase D l Ω Y₀ E) :=
  ⟨(D.geometricFrobenius Y₀).hom, AlgHom.id _ _⟩

/-- The canonical etale pullback comparison with literal automorphism reindexing.
Source: Stacks 03Q1; the recorded automorphism pullback construction
(blueprint: def-zl-normalized-classical-weil-realization). -/
def zlClassicalFinitePullbackComparison (E : Padic.FiniteCoefficientFields l Ω)
    (F : Sheaf (D.geometricFiber Y₀).left.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val))) :
    (Etale.upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val))
      (D.geometricFrobenius Y₀).hom).obj F ≅
    (automorphismModuleSheafPullback (D.geometricFrobenius Y₀)
      (Padic.coefficientExtensionIntegers l E.val)).obj F :=
  ((GrothendieckTopology.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val)) @Etale @Etale
      le_rfl (D.geometricFrobenius Y₀).hom
      (inferInstance : Etale (D.geometricFrobenius Y₀).hom)).app F) ≪≫
    ObjectProperty.isoMk _ (Iso.refl _)

/-- The actual finite-level pullback unit into the classical reindexed sheaf.
This fixes the completed operation's tower identifications, including rawIntegral.
Source: Stacks 03Q1; BS 6.8.4(1),(4)
(blueprint: def-zl-normalized-classical-weil-realization). -/
def zlClassicalFiniteUnit (E : Padic.FiniteCoefficientFields l Ω)
    (F : Sheaf (D.geometricFiber Y₀).left.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val))) :
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1}
      (Padic.coefficientExtensionIntegers l E.val)) AddCommGrpCat)).obj F ⟶
    (Etale.lowerStar AddCommGrpCat.{u + 1} (D.geometricFrobenius Y₀).hom).obj
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1}
        (Padic.coefficientExtensionIntegers l E.val)) AddCommGrpCat)).obj
        ((automorphismModuleSheafPullback (D.geometricFrobenius Y₀)
          (Padic.coefficientExtensionIntegers l E.val)).obj F)) :=
  (sheafCompose _ (forget₂ (ModuleCat.{u + 1}
    (Padic.coefficientExtensionIntegers l E.val)) AddCommGrpCat)).map
      ((Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val))
          (D.geometricFrobenius Y₀).hom).unit.app F ≫
        (Etale.lowerStar (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E.val))
          (D.geometricFrobenius Y₀).hom).map
            (zlClassicalFinitePullbackComparison D l Ω Y₀ E F).hom)

/-- Include a finite-free rational system in the actual algebraic-coefficient category.
Source: Weil II (1.1.1)d); BS 6.8.4(4)
(blueprint: def-zl-normalized-classical-weil-realization). -/
def zlClassicalModel (E : Padic.FiniteCoefficientFields l Ω) :
    AlgebraicGeometry.ProEtale.CompletedLisse.RawRational l (zlCompletedBase D l Ω Y₀ E) ⥤
      LisseAlgebraicSheaf l (D.geometricFiber Y₀).left Ω :=
  ObjectProperty.ι _ ⋙ lisseAlgebraicModelFunctor l (D.geometricFiber Y₀).left Ω E

/-- Forget the completed rational module action, retaining its actual abelian sheaf.
Source: BS 6.8.4(4)
(blueprint: def-zl-normalized-classical-weil-realization). -/
def zlCompletedRationalForget (E : Padic.FiniteCoefficientFields l Ω) :
    AlgebraicGeometry.ProEtale.CompletedLisse.Rational l (zlCompletedBase D l Ω Y₀ E) ⥤
      Sheaf (ProEt.topology (D.geometricFiber Y₀).left) AddCommGrpCat.{u + 1} :=
  ObjectProperty.ι _ ⋙
    AlgebraicGeometry.ProEtale.CompletedLisse.rationalForget l (zlCompletedBase D l Ω Y₀ E)


/-- The underlying abelian sheaf of the recorded degree-zero realization.
Source: BS 6.8.14(2)
(blueprint: def-zl-normalized-classical-weil-realization). -/
def zlRealizedAbelianSheaf (E : Padic.FiniteCoefficientFields l Ω)
    (a : LisseRealization.At D l hl (Coefficient.{u} l Ω E)
      (zlRealizationBase D l hl Y₀)) :
    sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) (D.geometricFiber Y₀).left ⥤
      Sheaf (ProEt.topology (D.geometricFiber Y₀).left) AddCommGrpCat.{u + 1} :=
  a.sheaf D l hl (Coefficient.{u} l Ω E) ⋙
    SheafOfModules.toSheaf ((adicLisseForget (D.geometricFiber Y₀).left).obj
      (rationalCoefficientSheaf l (D.geometricFiber Y₀).left (Coefficient.{u} l Ω E)))


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Finite-stage pinning of the Weil transport. The two realization comparisons are
linked on ordinary sections: the unit of actual module pullback, followed by the
lem-tw PullNormalized comparison, is the projection/fraction-normalized completed-system
comparison. Coefficient transport is fixed pointwise by the specified Shrink equivalence.
The final square fixes the common-stage comparison, rather than merely asserting the
existence of some isomorphism of the two composite functors.
Source: BS 6.8.4(1),(4), 6.8.14(2), 6.8.15; lem-tw-lisse-rational-realization,
PullNormalized at geometric Frobenius; lem-per-lisse-completed-system-comparison,
Operation.rational_normalization
(blueprint: def-zl-normalized-classical-weil-realization). -/
structure ZlClassicalPullbackModels (E : Padic.FiniteCoefficientFields l Ω) where
  realization : LisseRealization.At D l hl (Coefficient.{u} l Ω E)
    (zlRealizationBase D l hl Y₀)
  along : LisseRealization.Along D l hl (Coefficient.{u} l Ω E)
    (D.geometricFrobenius Y₀).hom realization realization
  normalized : LisseRealization.PullNormalized D l hl (Coefficient.{u} l Ω E)
    (D.geometricFrobenius Y₀).hom realization realization along
  completed : AlgebraicGeometry.ProEtale.CompletedLisse.Comparison l
    (zlCompletedBase D l Ω Y₀ E)
  operation : AlgebraicGeometry.ProEtale.CompletedLisse.Operation l
    (zlCompletedFrobenius D l Ω Y₀ E) completed completed
  coefficient : AlgebraicGeometry.ProEtale.CompletedLisse.rationalRing l
      (zlCompletedBase D l Ω Y₀ E) ≅
    rationalCoefficientSheaf l (D.geometricFiber Y₀).left (Coefficient.{u} l Ω E)
  coefficient_values : ∀ (U : (D.geometricFiber Y₀).left.ProEtᵒᵖ)
    (s : (AlgebraicGeometry.ProEtale.CompletedLisse.rationalRing l
      (zlCompletedBase D l Ω Y₀ E)).obj.obj U) (x : U.unop.left),
    rationalCoefficientValue l (Coefficient.{u} l Ω E) (D.geometricFiber Y₀).left U
      (coefficient.hom.hom.app U s) x = (Shrink.algEquiv ℚ_[l] E.val).symm (s.down x)
  finite : AlgebraicGeometry.ProEtale.CompletedLisse.RawRational l
      (zlCompletedBase D l Ω Y₀ E) ⥤
    sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) (D.geometricFiber Y₀).left
  lisse : ∀ F, LisseRealization.Lisse D l hl (Coefficient.{u} l Ω E)
    (zlRealizationBase D l hl Y₀) (finite.obj F)
  sheaf : finite ⋙ zlRealizedAbelianSheaf D l hl Ω Y₀ E realization ≅
    completed.rationalRealization ⋙ zlCompletedRationalForget D l Ω Y₀ E
  sheaf_linear : ∀ F (U : (D.geometricFiber Y₀).left.ProEtᵒᵖ)
    (a : (rationalCoefficientSheaf l (D.geometricFiber Y₀).left
      (Coefficient.{u} l Ω E)).obj.obj U)
    (s : ((realization.sheaf D l hl (Coefficient.{u} l Ω E)).obj
      (finite.obj F)).val.obj U),
    (sheaf.hom.app F).hom.app U
      (@SMul.smul _ _
        (((realization.sheaf D l hl (Coefficient.{u} l Ω E)).obj
          (finite.obj F)).val.obj U).isModule.toSMul a s) =
      @SMul.smul _ _
        (((completed.rationalRealization.obj F).obj.val.obj U).isModule.toSMul)
        (coefficient.inv.hom.app U a) ((sheaf.hom.app F).hom.app U s)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Normalized pullback comparison on the prescribed finite model.
Source: BS 6.8.15 and the two normalized realization comparisons
(blueprint: def-zl-normalized-classical-weil-realization). -/
def ZlClassicalPullbackStage
    (T : LisseAlgebraicSheaf l (D.geometricFiber Y₀).left Ω ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
    (δ : T ⋙ sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ≅
      lisseAlgebraicAutomorphismPullback (D.geometricFrobenius Y₀) l Ω ⋙ T)
    (E : Padic.FiniteCoefficientFields l Ω) : Prop :=
  ∃ M : ZlClassicalPullbackModels D l hl Ω Y₀ E,
  let realization := M.realization
  let along := M.along
  let completed := M.completed
  let operation := M.operation
  let finite := M.finite
  let lisse := M.lisse
  let sheaf := M.sheaf
  ∃ finite_pullback : finite ⋙ LisseRealization.pull D l hl (Coefficient.{u} l Ω E)
      (X := zlRealizationBase D l hl Y₀) (Y := zlRealizationBase D l hl Y₀)
      (D.geometricFrobenius Y₀).hom ≅ operation.raw ⋙ finite,
  -- Sections: the normalized ordinary-unit square.
  (∀ (F : AlgebraicGeometry.ProEtale.CompletedLisse.RawRational l
      (zlCompletedBase D l Ω Y₀ E)) (U : (D.geometricFiber Y₀).left.ProEt)
    (s : ((realization.sheaf D l hl (Coefficient.{u} l Ω E)).obj
      (finite.obj F)).val.obj (op U)),
    ((sheaf.hom.app (operation.raw.obj F)).hom.app
        (op ((proEtaleBaseChange (D.geometricFrobenius Y₀).hom).obj U)))
      (((realization.sheaf D l hl (Coefficient.{u} l Ω E)).map
          (finite_pullback.hom.app F)).val.app
        (op ((proEtaleBaseChange (D.geometricFrobenius Y₀).hom).obj U))
        (((along.comparison (finite.obj F) (lisse F)).inv).val.app
          (op ((proEtaleBaseChange (D.geometricFrobenius Y₀).hom).obj U))
          (ContinuousRational.moduleUnit (D.geometricFrobenius Y₀).hom
            (LisseRealization.coefficientPull l (Coefficient.{u} l Ω E)
              (D.geometricFrobenius Y₀).hom)
            ((realization.sheaf D l hl (Coefficient.{u} l Ω E)).obj (finite.obj F)) U s))) =
    (operation.rational.hom.app F).hom.val.app
      (op ((proEtaleBaseChange (D.geometricFrobenius Y₀).hom).obj U))
      ((operation.modules.rationalUnit l (completed.rationalRealization.obj F)).hom.app
        (op U) ((sheaf.hom.app F).hom.app (op U) s))) ∧
  ∃ classical_objects : ∀ F,
    lisseAlgebraicOfModel l (D.geometricFiber Y₀).left Ω E (operation.raw.obj F).obj =
      (lisseAlgebraicAutomorphismPullback (D.geometricFrobenius Y₀) l Ω).obj
        (lisseAlgebraicOfModel l (D.geometricFiber Y₀).left Ω E F.obj),
  -- Classical units: no scalar twist in the finite-level identifications.
  (∀ F (m : ℕ),
    HEq (operation.etale.unit l ⟨F.obj.integral, F.property⟩ m ≫
      (Etale.lowerStar AddCommGrpCat.{u + 1} (D.geometricFrobenius Y₀).hom).map
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1}
          (Padic.coefficientExtensionIntegers l E.val)) AddCommGrpCat)).map
            (((operation.rawIntegral F).inv).hom.app (op m))))
      (zlClassicalFiniteUnit D l Ω Y₀ E (F.obj.integral.obj.obj (op m)))) ∧
  ∃ stage : zlClassicalModel D l Ω Y₀ E ⋙ T ≅
    finite ⋙ GeneralAlgebraicallyClosedCoefficients.inclusion E,
  ∃ stage_pullback_objects : ∀ K,
    (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K) =
      (GeneralAlgebraicallyClosedCoefficients.inclusion E).obj
        ((LisseRealization.pull D l hl (Coefficient.{u} l Ω E)
          (X := zlRealizationBase D l hl Y₀) (Y := zlRealizationBase D l hl Y₀)
          (D.geometricFrobenius Y₀).hom).obj K),
  -- Pinning: this equality fixes the actual common-stage comparison.
  ∀ F,
    δ.hom.app (lisseAlgebraicOfModel l (D.geometricFiber Y₀).left Ω E F.obj) =
      (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).map (stage.hom.app F) ≫
        eqToHom (stage_pullback_objects (finite.obj F)) ≫
        (GeneralAlgebraicallyClosedCoefficients.inclusion E).map
          (finite_pullback.hom.app F) ≫
        stage.inv.app (operation.raw.obj F) ≫ T.map (eqToHom (classical_objects F))

/-- The recorded normalized adic realization, transported to the common-stage
presentation. The model bundle fixes integral inverse limits, rational maps and fibres.
Source: BS 6.8.4(1),(4), 6.8.14(2), 6.8.15
(blueprint: def-zl-normalized-classical-weil-realization). -/
structure ZlClassicalRealization where
  dimension : ∃ n : ℕ, topologicalKrullDim (D.geometricFiber Y₀).left ≤
    (n : WithBot ℕ∞)
  models : letI : Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber Y₀).left ≤
      (n : WithBot ℕ∞)) := ⟨dimension⟩
    AdicLisseCalculusModels l Ω (D.geometricFiber Y₀).left
  functor : LisseAlgebraicSheaf l (D.geometricFiber Y₀).left Ω ⥤
    generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left
  normalization :
    letI : Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber Y₀).left ≤
      (n : WithBot ℕ∞)) := ⟨dimension⟩
    functor ≅ models.realization ⋙ models.comparison.functor
  heart : ∀ F, sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω (functor.obj F)
  pullback : functor ⋙ sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ≅
    lisseAlgebraicAutomorphismPullback (D.geometricFrobenius Y₀) l Ω ⋙ functor
  pullback_pinning : ∀ E : Padic.FiniteCoefficientFields l Ω,
    ZlClassicalPullbackStage D l hl Ω Y₀ functor pullback E

/-- Transport both Weil maps and their inverses through the realization comparison.
Source: BS 6.8.4(4), 6.8.15
(blueprint: def-zl-normalized-classical-weil-realization). -/
def ZlClassicalRealization.weil (R : ZlClassicalRealization D l hl Ω Y₀) :
    ZlClassicalWeil D l Ω Y₀ ⥤ sfCommonStageWeilSheaf D l hl Y₀ Ω :=
  ObjectProperty.lift _ (IsoAlgebra.mapOfNatIso R.pullback)
    (fun F ↦ R.heart F.carrier)

end WeilConjectures
