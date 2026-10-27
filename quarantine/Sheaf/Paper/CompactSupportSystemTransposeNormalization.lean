module

public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.Paper.SystemOperationExchangeRealization
public import Sheaf.Paper.MixedReductionUnit
public import Sheaf.Paper.SystemCompactSupportRestrictionCocycle
public import Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms
public import Sheaf.Paper.CoefficientExtensionReductionModel
public import Sheaf.CategoryTheory.SystemRingedSequenceSite
public import Sheaf.Paper.SemilinearDerivedSections

import all Sheaf.Paper.IntegralComparisonSequenceSystems
import Sheaf.Algebra.Homology.CochainDerivedAdjunction
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Whole-system transpose normalization of compact-support scalar change

Source: compact-support finite-field independence, first sentence, and
lem-fix-operation-reduction, compact-support and scalar paragraphs;
Stacks 03CZ, 03DI, 06YY, 07A6 and 0941
(blueprint: lem-weil-compact-support-system-transpose-normalization).
All equations live on entire derived quotient systems. The integral comparison
is the prescribed construction, and both realization maps use the fixed counits
and the normalized Roos comparisons, including the shifted cone coordinate.

## Main definitions

* `systemScalarAdjunction`: section- and cochain-normalized scalar adjunction in
  the fixed system realization coordinates.
* `wholeMixedCompletedReductionUnit`: simultaneous strict-system mixed unit,
  followed by the prescribed completion comparison.
* `realizedSystemCompactRestriction`: proper/open restriction comparison in the
  fixed operation coordinates, with the original resolution and unit squares.
* `compactSupportSystemTranspose`: the actual scalar-adjunction transpose.

## Main statements

* `compactSupportSystemTransposeNormalization`: the entire-system transpose,
  reduction and limit-realization equations with both counit squares.

The helper declarations belong to this item. The general-site adjunction, the
six finite mixed-unit declarations and the restriction cocycle remain owned by
and publicly imported from their original nodes, without changing those records.
-/

@[expose] public noncomputable section SystemScalarCoordinates
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived
  WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped ChangeOfRings
attribute [local irreducible] WeilConjectures.integralComparisonSequenceScalarModel
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u})

/-- Exact restriction along the actual quotient-system ring map.
Source: Stacks 03CZ (blueprint: lem-weil-compact-support-system-transpose-normalization). -/
abbrev systemScalarRestriction :=
  SheafOfModules.restrictScalars
    ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (integralComparisonSequenceScalarMap.{u, u} l E L ι W))

/-- Ordinary tensor-unit normalization on every section of the sequence site.
Source: Stacks 03CZ (blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def SystemScalarOrdinaryUnit
    (a : (integralComparisonSequenceScalarModel l E L ι W).E ⊣
      systemScalarRestriction l E L ι W) : Prop :=
  ∀ (M : coefficientSequenceModules l E W) (U : (ℕ × W.ProEt)ᵒᵖ) (x : M.val.obj U),
    (eqToHom ((integralComparisonSequenceScalarModel l E L ι W).obj_eq M)).val.app U
        ((a.unit.app M).val.app U x) =
      (CategoryTheory.toSheafify (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (SheafOfModules.changeOfRingsPresheaf
          (integralComparisonSequenceScalarMap.{u, u} l E L ι W) M).presheaf).app U
        ((1 : (coefficientSequenceCommRingSheaf.{u, u} l L W).obj.obj U) ⊗ₜ[
          (coefficientSequenceCommRingSheaf.{u, u} l E W).obj.obj U,
          ((integralComparisonSequenceScalarMap.{u, u} l E L ι W).hom.app U).hom] x)

/-- The section formula determines the ordinary scalar adjunction uniquely.
Source: Stacks 03CZ (blueprint: lem-weil-compact-support-system-transpose-normalization).
Proof: apply sheafRingCoefficientOrdinaryAdjunction to the fixed model.E and its
obj_eq/map_eq. The generator formula determines the unit, hence the Hom equivalence
and the adjunction. No arbitrary adjunction or ring map is chosen. -/
theorem systemScalarOrdinaryAdjunction_existsUnique :
    ∃! a : (integralComparisonSequenceScalarModel l E L ι W).E ⊣
      systemScalarRestriction l E L ι W, SystemScalarOrdinaryUnit l E L ι W a := by
  classical
  obtain ⟨_, _, h⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (integralComparisonSequenceScalarMap l E L ι W)
  obtain ⟨a, ha⟩ := h (integralComparisonSequenceScalarModel l E L ι W).E
    (integralComparisonSequenceScalarModel l E L ι W).obj_eq
    (integralComparisonSequenceScalarModel l E L ι W).map_eq
  have hunit : SystemScalarOrdinaryUnit l E L ι W a := by
    dsimp only [SystemScalarOrdinaryUnit]
    intro M U x
    have hu := ha M ((integralComparisonSequenceScalarModel l E L ι W).E.obj M)
      (eqToHom ((integralComparisonSequenceScalarModel l E L ι W).obj_eq M).symm) U x
    simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at hu
    erw [hu]
    have hc := congrArg (fun f ↦ f.val.app U
      ((CategoryTheory.toSheafify (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (SheafOfModules.changeOfRingsPresheaf
          (integralComparisonSequenceScalarMap l E L ι W) M).presheaf).app U
        ((1 : (coefficientSequenceCommRingSheaf l L W).obj.obj U) ⊗ₜ[
          (coefficientSequenceCommRingSheaf l E W).obj.obj U,
          ((integralComparisonSequenceScalarMap l E L ι W).hom.app U).hom] x)))
      (eqToHom_trans ((integralComparisonSequenceScalarModel l E L ι W).obj_eq M).symm
        ((integralComparisonSequenceScalarModel l E L ι W).obj_eq M))
    exact hc
  refine ⟨a, hunit, ?_⟩
  intro b hb
  apply Adjunction.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  ext U x
  have he := (hb M U x).trans (hunit M U x).symm
  have hi : Function.Injective
      (fun y ↦ (eqToHom
        ((integralComparisonSequenceScalarModel l E L ι W).obj_eq M)).val.app U y) := by
    apply Function.LeftInverse.injective (g := fun y ↦
      ((eqToHom ((integralComparisonSequenceScalarModel l E L ι W).obj_eq M).symm).val.app U) y)
    intro y
    exact congrArg (fun f ↦ f.val.app U y)
      (eqToHom_trans ((integralComparisonSequenceScalarModel l E L ι W).obj_eq M)
        ((integralComparisonSequenceScalarModel l E L ι W).obj_eq M).symm)
  exact hi he

/-- The ordinary adjunction determined by its section formula.
Source: Stacks 03CZ (blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def systemScalarOrdinaryAdjunction :=
  (systemScalarOrdinaryAdjunction_existsUnique l E L ι W).exists.choose

/-- The full cochain counit square fixes the derived unit before finite evaluation.
Source: Stacks 07A6 (blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def SystemScalarDerivedUnit
    (d : integralComparisonDerivedSequenceScalar l E L ι W ⊣
      (systemScalarRestriction l E L ι W).mapDerivedCategory) : Prop :=
  ∀ P : CochainComplex (coefficientSequenceModules l E W) ℤ,
    d.unit.app (DerivedCategory.Q.obj P) ≫
        (systemScalarRestriction l E L ι W).mapDerivedCategory.map
          ((integralComparisonSequenceScalarModel l E L ι W).ε.app P) ≫
        (systemScalarRestriction l E L ι W).mapDerivedCategoryFactors.hom.app
          (((integralComparisonSequenceScalarModel l E L ι W).E.mapHomologicalComplex
            (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((systemScalarOrdinaryAdjunction l E L ι W).mapHomologicalComplex (.up ℤ)).unit.app P)

/-- The existing cochain derived pair has the uniquely normalized scalar adjunction.
Source: Stacks 07A6, 0FND, 09T5
(blueprint: lem-weil-compact-support-system-transpose-normalization).
Proof: restriction is exact by sheafRingCoefficientOrdinaryAdjunction. Apply
exists_cochainDerivedAdjunction to the fixed model and its universal cochain counit,
using flat-term K-flat resolutions. Its equation holds on every complex. On K-flat
resolutions the counit is invertible, so it determines the unit uniquely; naturality
on roofs extends uniqueness to all objects. Units determine adjunction structures. -/
theorem systemScalarAdjunction_existsUnique :
    ∃! d : integralComparisonDerivedSequenceScalar l E L ι W ⊣
      (systemScalarRestriction l E L ι W).mapDerivedCategory,
      SystemScalarDerivedUnit l E L ι W d := by
  classical
  let D := integralComparisonSequenceScalarModel l E L ι W
  obtain ⟨hl, hc, _⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (integralComparisonSequenceScalarMap l E L ι W)
  let := hl
  let := hc
  let := D.universal
  let P : CochainComplex (coefficientSequenceModules l E W) ℤ → Prop :=
    fun K ↦ CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E W) K
  have hres : ∀ K, ∃ (L : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (p : L ⟶ K), P L ∧ QuasiIso p := by
    intro K
    obtain ⟨L, p, hL, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E W) K
    exact ⟨L, p, hL, hp⟩
  obtain ⟨d, hd⟩ := Functor.exists_cochainDerivedAdjunction D.E
    (systemScalarRestriction l E L ι W) (systemScalarOrdinaryAdjunction l E L ι W)
    D.T D.ε P hres D.computes
  refine ⟨d, hd, ?_⟩
  intro e he
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (coefficientSequenceModules l E W) (.up ℤ))
  intro K
  obtain ⟨P₀, p, hP₀, hp⟩ := hres K
  let := hp
  have hε := D.computes P₀ hP₀
  let := hε
  have hLunit : e.unit.app (DerivedCategory.Q.obj P₀) =
      d.unit.app (DerivedCategory.Q.obj P₀) := by
    let U := (systemScalarRestriction l E L ι W).mapDerivedCategory
    apply (Iso.cancel_iso_hom_right _ _ (U.mapIso (@asIso _ _ _ _ (D.ε.app P₀) hε))).1
    apply (Iso.cancel_iso_hom_right _ _
      ((systemScalarRestriction l E L ι W).mapDerivedCategoryFactors.app
        ((D.E.mapHomologicalComplex (.up ℤ)).obj P₀))).1
    simpa only [Category.assoc, Functor.mapIso_hom, asIso_hom, Iso.app_hom, D, U]
      using (he P₀).trans (hd P₀).symm
  have hpiso : IsIso (DerivedCategory.Q.map p) := inferInstance
  apply (Iso.cancel_iso_hom_left (@asIso _ _ _ _ (DerivedCategory.Q.map p) hpiso) _ _).1
  have hn := e.unit.naturality (DerivedCategory.Q.map p)
  have hn' := d.unit.naturality (DerivedCategory.Q.map p)
  simp only [Functor.id_map, hLunit] at hn hn'
  exact hn.trans hn'.symm

/-- Scalar adjunction for the prescribed whole-system derived extension.
Source: Stacks 07A6 (blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def systemScalarAdjunction :=
  (systemScalarAdjunction_existsUnique l E L ι W).exists.choose

end WeilConjectures

end SystemScalarCoordinates

@[expose] public noncomputable section WholeMixedCoordinates
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
attribute [local irreducible] WeilConjectures.FrobeniusExchange.models
  Functor.mapDerivedCategory WeilConjectures.CoefficientReductionPresentation
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived
  WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u})

/-- Ordinary scalar extension of a cochain representative, before completion.
Source: lem-fix-operation-reduction
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
abbrev mixedScalarComplex (P : CochainComplex (scalarReductionSource l E W) ℤ) :=
  ((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P

/-- The strict-chain square, before finite evaluation. Source: lem-fix-operation-reduction
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def MixedReductionChainSections
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (D : CochainComplex (coefficientSequenceModules l L W) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
    (κL : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).obj D ≅
        ((scalarReductionExtension l L W n).mapHomologicalComplex (.up ℤ)).obj
          (mixedScalarComplex l E L ι W P))
    (a : C ⟶ ((systemScalarRestriction l E L ι W).mapHomologicalComplex (.up ℤ)).obj D) :
    Prop :=
  ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ),
    HEq
      (fun x : (C.X i).val.obj (op (n, U.unop)) ↦
        ((κL n).hom.f i).val.app U
          (cast (congrArg (fun A : AddCommGrpCat ↦ ↥A)
            (coefficientSequenceEvaluationAb_eq l L W (D.X i) n U)).symm
              ((a.f i).val.app (op (n, U.unop)) x)))
      (fun x : ((coefficientSequenceEvaluation l E W n).obj (C.X i)).val.obj U ↦
        ((sfMixedReductionUnit l E L ι W n).app (P.X i)).val.app U
          (((κ n).hom.f i).val.app U x))

/-- The simultaneous whole-system counit square for a fixed strict-chain map.
Source: lem-fix-operation-reduction
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def MixedReductionWholeSquare
    (η : FrobeniusExchange.reduction l E W ⟶
      integralOrdinaryDerivedScalar l E L ι W ⋙ FrobeniusExchange.reduction l L W ⋙
        (systemScalarRestriction l E L ι W).mapDerivedCategory)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (D : CochainComplex (coefficientSequenceModules l L W) ℤ)
    (e : (FrobeniusExchange.reduction l E W).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj C)
    (d : (FrobeniusExchange.reduction l L W).obj
      (DerivedCategory.Q.obj (mixedScalarComplex l E L ι W P)) ≅ DerivedCategory.Q.obj D)
    (a : C ⟶ ((systemScalarRestriction l E L ι W).mapHomologicalComplex (.up ℤ)).obj D) :
    Prop :=
  η.app (DerivedCategory.Q.obj P) ≫
      (systemScalarRestriction l E L ι W).mapDerivedCategory.map
        ((FrobeniusExchange.reduction l L W).map
          ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P)) ≫
      (systemScalarRestriction l E L ι W).mapDerivedCategory.map d.hom ≫
      (systemScalarRestriction l E L ι W).mapDerivedCategoryFactors.hom.app D =
    e.hom ≫ DerivedCategory.Q.map a

/-- The ordinary mixed map is fixed on every flat-term K-flat presentation by one
strict-system chain map with the tensor formula of the recorded finite unit.
Source: lem-fix-operation-reduction
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def WholeMixedReductionNormalized
    (η : FrobeniusExchange.reduction l E W ⟶
      integralOrdinaryDerivedScalar l E L ι W ⋙ FrobeniusExchange.reduction l L W ⋙
        (systemScalarRestriction l E L ι W).mapDerivedCategory) : Prop :=
  ∀ (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) P),
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i)) →
    ∃ (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (D : CochainComplex (coefficientSequenceModules l L W) ℤ)
      (e : (FrobeniusExchange.reduction l E W).obj (DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj C)
      (d : (FrobeniusExchange.reduction l L W).obj
        (DerivedCategory.Q.obj (mixedScalarComplex l E L ι W P)) ≅ DerivedCategory.Q.obj D)
      (κ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)
      (κL : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ)).obj D ≅
          ((scalarReductionExtension l L W n).mapHomologicalComplex (.up ℤ)).obj
            (mixedScalarComplex l E L ι W P))
      (a : C ⟶ ((systemScalarRestriction l E L ι W).mapHomologicalComplex (.up ℤ)).obj D),
      CoefficientReductionPresentation l E W
        ((FrobeniusExchange.models l E).system W).toCoefficientDerivedSystemReduction
          P hP C e κ ∧
      (∃ hQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W)
        (R := completedIntegralCommRingSheafUnrestricted l L W) (mixedScalarComplex l E L ι W P),
        CoefficientReductionPresentation l L W
          ((FrobeniusExchange.models l L).system W).toCoefficientDerivedSystemReduction
            (mixedScalarComplex l E L ι W P) hQ D d κL) ∧
      MixedReductionChainSections l E L ι W P C D κ κL a ∧
      MixedReductionWholeSquare l E L ι W η P C D e d a

/-- Unique localization of the actual simultaneous mixed tensor unit.
Source: lem-fix-operation-reduction, tensor reassociation paragraph
(blueprint: lem-weil-compact-support-system-transpose-normalization).
Proof: on a flat-term K-flat P, use its strict quotient complexes and the strict
quotient complexes of ordinary scalar extension of P. The maps
s tensor x maps to ι_n(s) tensor (1 tensor x) commute with all quotient transitions,
vertical restrictions and differentials, hence give one chainMap. Finite free
ordinary extension preserves flat terms and K-flatness. The universal reduction
counits identify these complexes with the two reductions. Their naturality gives
the displayed whole_square. Localize using the canonical K-flat resolution
comparisons. The section formula determines each strict-chain map, and the
universal derived counit square determines its localization on every roof. This
gives existence and uniqueness of the natural transformation, without assuming
that finite evaluations are faithful on arbitrary derived morphisms. -/
theorem wholeMixedReductionUnit_existsUnique :
    ∃! η : FrobeniusExchange.reduction l E W ⟶
      integralOrdinaryDerivedScalar l E L ι W ⋙ FrobeniusExchange.reduction l L W ⋙
        (systemScalarRestriction l E L ι W).mapDerivedCategory,
      WholeMixedReductionNormalized l E L ι W η := by
  sorry

/-- The ordinary whole-system mixed unit, determined by its strict-chain construction.
Source: lem-fix-operation-reduction
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def wholeMixedReductionUnit :=
  (wholeMixedReductionUnit_existsUnique l E L ι W).exists.choose

/-- Apply reduction and exact restriction to the prescribed diagonal Roos completion.
This is the entire-system mixed completed unit, with both Roos coordinates retained.
Source: lem-fix-operation-reduction, completed comparison paragraph
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def wholeMixedCompletedReductionUnit :
    FrobeniusExchange.reduction l E W ⟶
      integralScalarExtension l E L ι W ⋙ FrobeniusExchange.reduction l L W ⋙
        (systemScalarRestriction l E L ι W).mapDerivedCategory :=
  wholeMixedReductionUnit l E L ι W ≫
    Functor.whiskerRight (Functor.whiskerRight (scalarCompletion l E L ι W)
      (FrobeniusExchange.reduction l L W))
      (systemScalarRestriction l E L ι W).mapDerivedCategory

end WeilConjectures

end WholeMixedCoordinates

@[expose] public noncomputable section RestrictionCoordinates
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures
open FrobeniusExchange
variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The identity of section carriers fixes the ordinary pushforward/restriction square.
Source: Stacks 03CZ (blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def RealizedSystemPushSections {Z W : Scheme.{u}} (g : Z ⟶ W)
    (d : systemScalarRestriction l E L ι Z ⋙ integralComparisonSequenceDirectImage l E g ≅
      integralComparisonSequenceDirectImage l L g ⋙ systemScalarRestriction l E L ι W) :
    Prop :=
  ∀ (M : coefficientSequenceModules l L Z) (U : (ℕ × W.ProEt)ᵒᵖ)
    (x : M.val.obj ((integralComparisonSequenceBaseChange g).op.obj U)),
    (d.hom.app M).val.app U x = x

/-- The ordinary section identity determines the comparison uniquely.
Source: Stacks 03CZ (blueprint: lem-weil-compact-support-system-transpose-normalization).
Proof: pushforward is precomposition with the same base-change functor, and
restriction retains the underlying additive sections. The constant coefficient
square commutes, so identity functions are linear; the inverse is the same
identity. Sectionwise faithfulness determines the natural isomorphism uniquely. -/
theorem realizedSystemPush_existsUnique {Z W : Scheme.{u}} (g : Z ⟶ W) :
    ∃! d : systemScalarRestriction l E L ι Z ⋙ integralComparisonSequenceDirectImage l E g ≅
      integralComparisonSequenceDirectImage l L g ⋙ systemScalarRestriction l E L ι W,
      RealizedSystemPushSections l E L ι g d := by
  classical
  let d := sequenceScalarPullbackRight l E L ι g
  have hd : RealizedSystemPushSections l E L ι g d := by
    intro M U x
    rfl
  refine ⟨d, hd, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  ext U x
  exact (he M U x).trans (hd M U x).symm

/-- The actual section-normalized ordinary comparison.
Source: Stacks 03CZ (blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def realizedSystemPush {Z W : Scheme.{u}} (g : Z ⟶ W) :=
  (realizedSystemPush_existsUnique l E L ι g).exists.choose

attribute [local irreducible] realizedSystemPush

/-- Restriction commutes with ordinary inverse image, by the mate of the section identity.
Source: Stacks 03D7 (blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def realizedSystemPullInv {Z W : Scheme.{u}} (g : Z ⟶ W) :
    systemScalarRestriction l E L ι W ⋙ integralComparisonSequencePullback l E g ⟶
      integralComparisonSequencePullback l L g ⋙ systemScalarRestriction l E L ι Z :=
  ((mateEquiv
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l L g))
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E g))).symm
      (TwoSquare.mk _ _ _ _ (realizedSystemPush l E L ι g).inv)).natTrans

attribute [local irreducible] realizedSystemPullInv

/-- The constant coefficient inverse-image square is invertible before localization.
Source: Stacks 03D7 (blueprint: lem-weil-compact-support-system-transpose-normalization).
Proof: both inverse images are the same exact inverse image of additive sheaves;
their scalar action is the constant coefficient map. The mate on pure tensor
sections is the identity balancing map, whose inverse has the same formula. -/
theorem realizedSystemPullInv_isIso {Z W : Scheme.{u}} (g : Z ⟶ W) :
    IsIso (realizedSystemPullInv l E L ι g) := by
  sorry

/-- Exact localization of the normalized inverse-image square.
Source: Stacks 05RU (blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def realizedSystemPull {Z W : Scheme.{u}} (g : Z ⟶ W) :=
  letI := realizedSystemPullInv_isIso l E L ι g
  Functor.mapDerivedCategorySquareIso (asIso (realizedSystemPullInv l E L ι g))

attribute [local irreducible] realizedSystemPull

/-- Proper restriction is normalized on arbitrary K-injective system resolutions.
Restriction is not required to preserve K-injectives.
Source: Stacks 070Y, 0D6E
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def RealizedSystemProperNormalized {Z W : Scheme.{u}} (g : Z ⟶ W)
    (d : (systemScalarRestriction l E L ι Z).mapDerivedCategory ⋙ systemDirect l E g ≅
      systemDirect l L g ⋙ (systemScalarRestriction l E L ι W).mapDerivedCategory) : Prop :=
  ∀ (H : CochainComplex (coefficientSequenceModules l L Z) ℤ) [H.IsKInjective]
    (I : CochainComplex (coefficientSequenceModules l E Z) ℤ) [I.IsKInjective]
    (v : ((systemScalarRestriction l E L ι Z).mapHomologicalComplex (.up ℤ)).obj H ⟶ I)
    [QuasiIso v],
    QuasiIso (((integralComparisonSequenceDirectImage l E g).mapHomologicalComplex
      (.up ℤ)).map v) ∧
    d.hom.app (DerivedCategory.Q.obj H) ≫
      (systemScalarRestriction l E L ι W).mapDerivedCategory.map
        ((integralComparisonSequenceDirectImage l L g).rightDerivedFunctorObjQIso H).hom ≫
      (systemScalarRestriction l E L ι W).mapDerivedCategoryFactors.hom.app
        (((integralComparisonSequenceDirectImage l L g).mapHomologicalComplex (.up ℤ)).obj H) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (realizedSystemPush l E L ι g) (.up ℤ)).inv.app H) ≫
      DerivedCategory.Q.map
        (((integralComparisonSequenceDirectImage l E g).mapHomologicalComplex (.up ℤ)).map v) =
    (systemDirect l E g).map
        ((systemScalarRestriction l E L ι Z).mapDerivedCategoryFactors.hom.app H) ≫
      (systemDirect l E g).map (DerivedCategory.Q.map v) ≫
      ((integralComparisonSequenceDirectImage l E g).rightDerivedFunctorObjQIso I).hom

/-- The fixed operation-coordinate proper and open comparisons with their normalizations.
Source: Stacks 03DI, 03DJ, 0D6E
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
structure RealizedSystemRestriction {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) where
  properIso : (systemScalarRestriction l E L ι Z).mapDerivedCategory ⋙ systemDirect l E p ≅
    systemDirect l L p ⋙ (systemScalarRestriction l E L ι Y).mapDerivedCategory
  proper_normalized : RealizedSystemProperNormalized l E L ι p properIso
  openIso : (systemScalarRestriction l E L ι X).mapDerivedCategory ⋙ systemDerivedOpen l E j ≅
    systemDerivedOpen l L j ⋙ (systemScalarRestriction l E L ι Z).mapDerivedCategory
  open_normalized : ∀ M : coefficientSequenceDerived l L X,
    (systemDerivedOpenAdjunction l E j).unit.app
        ((systemScalarRestriction l E L ι X).mapDerivedCategory.obj M) ≫
      (integralComparisonDerivedSequencePullback l E j).map (openIso.hom.app M) ≫
      (realizedSystemPull l E L ι j).hom.app ((systemDerivedOpen l L j).obj M) =
    (systemScalarRestriction l E L ι X).mapDerivedCategory.map
      ((systemDerivedOpenAdjunction l L j).unit.app M)

/-- The normalized restriction comparison exists uniquely in the fixed realization.
Source: Stacks 03CZ, 03DI, 03DJ, 070Y, 0D6E
(blueprint: lem-weil-compact-support-system-transpose-normalization).
Proof: identify the fixed sequence-site coefficient ring with the uncurried actual
quotient ring diagram. Identity-on-sections equivalences identify restriction and
ordinary geometric pushforward. Transfer the normalized varying-ring comparison
of compactSupportRestrictionCocycle through these equivalences and their unique
adjunction-compatible left-adjoint comparisons. Its K-injective resolution equation
is exactly proper_normalized, and its original open-unit square is open_normalized.
Alternatively the proper comparison is the inverse of the localized p_*v after
the displayed section identity, while the open comparison is identity on the open
and zero outside it. Resolution comparison and open-adjunction uniqueness give
uniqueness in both cases. No evaluation-faithfulness assertion is needed. -/
theorem realizedSystemRestriction_existsUnique {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p] :
    ∃! d : RealizedSystemRestriction l E L ι j p, True := by
  sorry

attribute [local irreducible] RealizedSystemProperNormalized

/-- The restriction data determined by the proper and open normalizations.
Source: Stacks 03DI, 0D6E
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def realizedSystemRestriction {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p] :=
  (realizedSystemRestriction_existsUnique l E L ι j p).exists.choose

attribute [local irreducible] realizedSystemRestriction

/-- Paste the section-normalized open comparison with the K-injective-normalized proper one.
Source: Stacks 03DI, 0D6E
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def realizedSystemCompactRestriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    (systemScalarRestriction l E L ι X).mapDerivedCategory ⋙
        (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ≅
      (systemDerivedOpen l L c.i ⋙ systemDirect l L c.g) ⋙
        (systemScalarRestriction l E L ι Y).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (realizedSystemRestriction l E L ι c.i c.g).openIso
      (systemDirect l E c.g) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (systemDerivedOpen l L c.i)
      (realizedSystemRestriction l E L ι c.i c.g).properIso ≪≫
    (Functor.associator _ _ _).symm

end WeilConjectures

end RestrictionCoordinates

@[expose] public noncomputable section TransposeNormalization
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] WeilConjectures.systemScalarOrdinaryAdjunction
  WeilConjectures.systemScalarAdjunction
  WeilConjectures.integralComparisonSequenceScalarModel Functor.mapDerivedCategory
namespace WeilConjectures
open FrobeniusExchange

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The canonical whole-system scalar transpose of the normalized restriction square.
Its Hom equivalence is on the ordinary unbounded derived category of the sequence site.
Source: compact-support finite-field independence, single-inclusion normalization
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def compactSupportSystemTranspose {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : coefficientSequenceDerived l E X) :
    (integralComparisonDerivedSequenceScalar l E L ι Y).obj
        ((systemDerivedOpen l E c.i ⋙ systemDirect l E c.g).obj M) ⟶
      (systemDerivedOpen l L c.i ⋙ systemDirect l L c.g).obj
        ((integralComparisonDerivedSequenceScalar l E L ι X).obj M) :=
  ((systemScalarAdjunction l E L ι Y).homEquiv _ _).symm
    ((systemDerivedOpen l E c.i ⋙ systemDirect l E c.g).map
        ((systemScalarAdjunction l E L ι X).unit.app M) ≫
      (realizedSystemCompactRestriction l E L ι c).hom.app
        ((integralComparisonDerivedSequenceScalar l E L ι X).obj M))

/-- The coherent scalar reduction comparison, the actual realization counit.
Source: lem-fix-operation-reduction, scalar paragraph
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def compactSupportSystemScalarReduction (W : Scheme.{u}) :=
  integralComparisonScalarCounit l E L ι W ((models l E).system W)
    ((models l L).system W) ((models l L).roos W) ((scalarModels l E L ι).model W)

variable (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The fixed operation realization with invertibility transported from the base field.
Source: compact-support finite-field independence, coefficient convention
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def compactSupportTransposeRealization :=
  letI : ∀ x : X, Invertible (l : X.residueField x) :=
    sfCompactSupportScalarResidueUnit l K₀ hl X
  letI : ∀ y : Y, Invertible (l : Y.residueField y) :=
    sfCompactSupportScalarResidueUnit l K₀ hl Y
  compactRealization l E K₀ hl f c

/-- The fixed whole-system operation counit, with no additional invertibility hypothesis.
Source: compact-support finite-field independence, operation counit
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def compactSupportTransposeReduction :=
  letI : ∀ x : X, Invertible (l : X.residueField x) :=
    sfCompactSupportScalarResidueUnit l K₀ hl X
  letI : ∀ y : Y, Invertible (l : Y.residueField y) :=
    sfCompactSupportScalarResidueUnit l K₀ hl Y
  compactOperationReduction l E K₀ hl f c

/-- The fixed source coordinate uses scalar realization and scalar change of r_A.
Source: compact-support finite-field independence, system normalization
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def compactSupportTransposeSource (K : sfIntegralConstructibleCategory l E X) :=
  ((scalarModels l E L ι).model Y).realization.hom.app
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj ≫
    (coefficientSequenceLimit l L Y).map
      ((integralComparisonDerivedSequenceScalar l E L ι Y).map
        ((compactSupportTransposeReduction l E K₀ hl c).app K))

/-- The fixed target coordinate uses operation realization and proper/open image of s_X.
Source: compact-support finite-field independence, system normalization
(blueprint: lem-weil-compact-support-system-transpose-normalization). -/
def compactSupportTransposeTarget (K : sfIntegralConstructibleCategory l E X) :=
  (compactSupportTransposeRealization l L K₀ hl c).hom.app
      ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K) ≫
    (coefficientSequenceLimit l L Y).map
      ((systemDerivedOpen l L c.i ⋙ systemDirect l L c.g).map
        ((compactSupportSystemScalarReduction l E L ι X).app K.obj))

/-- The prescribed scalar comparison is the scalar-adjunction transpose on entire systems,
and its integral realization is the limit of that same transpose. There is no Tor,
quotient-flatness or finite-ground-field hypothesis and no evaluation-faithfulness claim.

Source: compact-support finite-field independence, first sentence; the agent-written
whole-system single-inclusion identification and lem-fix-operation-reduction
(blueprint: lem-weil-compact-support-system-transpose-normalization).

Proof (the eight DAG steps):
1. Identify F_D with reduction, system proper/open image, then total restricted limit,
using the fixed realization and its prescribed Roos projections. Its operation reduction
is the entire-system counit. Evaluations are isomorphisms, so joint conservativity
makes this counit invertible on constructible inputs. Scalar extension and compact
support preserve constructibility, so the same applies at C_X K and F_A K.
2. On one flat-term K-flat P, scalar association sends (x tensor b) tensor c to
(x tensor 1) tensor bc on the actual quotient diagrams. The quotient augmentation
has zero shifted Roos coordinate. QuotientScalarComparisonDescent and StrictRoosComparison
identify its completion chi with the reduction/limit adjunct of this association.
Countable products are exact on the pro-etale site. Hence epsilon R(chi) is association.
3. Reduction of the ordinary tensor unit followed by that association sends x tensor r
to (x tensor r) tensor 1. The normalized cochain counit square of the scalar adjunction
identifies this with zeta before evaluation. This is the first displayed equation.
4. Transpose d composed with H_A(zeta) using the whole-system scalar Hom equivalence.
It is a bijection for every target, so defines q uniquely for every unbounded input.
5. The open scalar mate has that transpose: restriction to the open is identity and
the original open unit is invertible. For the proper mate, iterated mate interchange
identifies its scalar transpose with the conjugate of the pullback/scalar comparison.
On a K-injective B-system and a K-injective resolution v of its restriction the triangle
identity reduces the conjugate to inverse p_*v, exactly the normalization of d.
Naturality pastes these two equations, proving systemCompactScalar = q.
6. The prescribed integral b is realized from precisely this proper/open word.
Its fixed source and target coordinates therefore give b followed by xi_t equal to
xi_s followed by total limit of q. This uses the construction, not finite evaluations.
7. Naturality of the whole-system counit gives epsilon R(xi_s) = S(r_A) s_Y and
epsilon R(xi_t) = H_B(s_X) r_B. Apply reduction to step 6 and compose with epsilon;
its naturality on q gives the asserted reduced equation in the entire-system category.
8. The strict Roos functor sends maps to cone maps on both products and shifted products.
Its augmentation is (quotient projections, zero shifted coordinate). The normalized
Roos bridge and augmented scalar resolution retain these coordinates in every square.
Thus the cochain counit squares and both Roos coordinates used above are the fixed ones. -/
theorem compactSupportSystemTransposeNormalization :
    (∀ (W : Scheme.{u}), W = X ∨ W = c.Z ∨ W = Y →
      ∀ H : DerivedCategory (scalarReductionSource l E W),
      (wholeMixedCompletedReductionUnit l E L ι W).app H ≫
          (systemScalarRestriction l E L ι W).mapDerivedCategory.map
            ((compactSupportSystemScalarReduction l E L ι W).app H) =
        (systemScalarAdjunction l E L ι W).unit.app ((reduction l E W).obj H)) ∧
    (∀ (W : Scheme.{u}), W = X ∨ W = c.Z ∨ W = Y →
      ∀ H : DerivedCategory (scalarReductionSource l E W),
        IsIso ((compactSupportSystemScalarReduction l E L ι W).app H)) ∧
    (∀ (M : coefficientSequenceDerived l E X) (Z : coefficientSequenceDerived l L Y),
      Function.Bijective (fun a :
        (integralComparisonDerivedSequenceScalar l E L ι Y).obj
            ((systemDerivedOpen l E c.i ⋙ systemDirect l E c.g).obj M) ⟶ Z ↦
        (systemScalarAdjunction l E L ι Y).unit.app
            ((systemDerivedOpen l E c.i ⋙ systemDirect l E c.g).obj M) ≫
          (systemScalarRestriction l E L ι Y).mapDerivedCategory.map a)) ∧
    (∀ M : coefficientSequenceDerived l E X,
      (systemScalarAdjunction l E L ι Y).unit.app
          ((systemDerivedOpen l E c.i ⋙ systemDirect l E c.g).obj M) ≫
        (systemScalarRestriction l E L ι Y).mapDerivedCategory.map
          (compactSupportSystemTranspose l E L ι c M) =
      (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g).map
          ((systemScalarAdjunction l E L ι X).unit.app M) ≫
        (realizedSystemCompactRestriction l E L ι c).hom.app
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj M)) ∧
    (∀ N : sfIntegralConstructibleCategory l L X,
      IsIso ((compactSupportTransposeReduction l L K₀ hl c).app N)) ∧
    (∀ K : sfIntegralConstructibleCategory l E X,
      IsIso ((compactSupportTransposeReduction l E K₀ hl c).app K) ∧
      IsIso ((compactSupportTransposeReduction l L K₀ hl c).app
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K)) ∧
      (reduction l L Y).map (sfCompactSupportScalarSystemMap l K₀ hl c E L ι K) ≫
          (compactSupportTransposeReduction l L K₀ hl c).app
            ((sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K) ≫
          (systemDerivedOpen l L c.i ⋙ systemDirect l L c.g).map
            ((compactSupportSystemScalarReduction l E L ι X).app K.obj) =
        (compactSupportSystemScalarReduction l E L ι Y).app
            ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj ≫
          (integralComparisonDerivedSequenceScalar l E L ι Y).map
            ((compactSupportTransposeReduction l E K₀ hl c).app K) ≫
          compactSupportSystemTranspose l E L ι c ((reduction l E X).obj K.obj)) ∧
    (∀ K : sfIntegralConstructibleCategory l E X,
      IsIso (compactSupportTransposeSource l E L ι K₀ hl c K) ∧
      IsIso (compactSupportTransposeTarget l E L ι K₀ hl c K) ∧
      (reduction l L Y).map (compactSupportTransposeSource l E L ι K₀ hl c K) ≫
          ((models l L).system Y).adjunction.counit.app
            ((integralComparisonDerivedSequenceScalar l E L ι Y).obj
              ((systemDerivedOpen l E c.i ⋙ systemDirect l E c.g).obj
                ((reduction l E X).obj K.obj))) =
        (compactSupportSystemScalarReduction l E L ι Y).app
            ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj ≫
          (integralComparisonDerivedSequenceScalar l E L ι Y).map
            ((compactSupportTransposeReduction l E K₀ hl c).app K) ∧
      (reduction l L Y).map (compactSupportTransposeTarget l E L ι K₀ hl c K) ≫
          ((models l L).system Y).adjunction.counit.app
            ((systemDerivedOpen l L c.i ⋙ systemDirect l L c.g).obj
              ((integralComparisonDerivedSequenceScalar l E L ι X).obj
                ((reduction l E X).obj K.obj))) =
        (compactSupportTransposeReduction l L K₀ hl c).app
            ((sfConstructibleIntegralScalarExtension 0 l
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).obj K) ≫
          (systemDerivedOpen l L c.i ⋙ systemDirect l L c.g).map
            ((compactSupportSystemScalarReduction l E L ι X).app K.obj) ∧
      sfCompactSupportScalarSystemMap l K₀ hl c E L ι K ≫
          compactSupportTransposeTarget l E L ι K₀ hl c K =
        compactSupportTransposeSource l E L ι K₀ hl c K ≫
          (coefficientSequenceLimit l L Y).map
            (compactSupportSystemTranspose l E L ι c ((reduction l E X).obj K.obj))) := by
  sorry

end WeilConjectures

end TransposeNormalization
