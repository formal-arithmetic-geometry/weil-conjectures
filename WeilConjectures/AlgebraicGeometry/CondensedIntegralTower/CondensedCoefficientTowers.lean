/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.CoefficientQuotientTowerLimit
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Integral reduction and total inverse limit in condensed coefficients

Source: latest blueprint sk-def-sp-coefficient-towers; canonical reduction coordinates
from sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers).
The ordinary category is the existing strict semilinear system category.  Its rings
are the section rings of the pulled-back continuous ell-power quotients.  Every
natural index n represents the positive exponent n+1, including ramified extensions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual ell-power ideal, as distinct from a uniformizer-power index.
Source: sk-def-sp-coefficient-towers (blueprint: sk-lem-sp-tower). -/
abbrev ellIdeal : Ideal (Padic.coefficientExtensionIntegers l E) :=
  Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} :
    Set (Padic.coefficientExtensionIntegers l E))

/-- Continuous finite ell-power coefficients on the point.
Source: sk-def-sp-coefficient-towers (blueprint: sk-lem-sp-tower). -/
abbrev finiteRingSheaf (n : ℕ) : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.continuousCoefficientRingSheaf
    (Padic.coefficientExtensionIntegers l E ⧸ ellIdeal l E ^ (n + 1))

/-- The underlying internal finite coefficient ring.
Source: sk-def-sp-coefficient-towers (blueprint: sk-lem-sp-tower). -/
abbrev finiteRing (n : ℕ) : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (finiteRingSheaf l E n)

/-- The quotient coefficient sheaf has its actual internal multiplication.
Source: sk-def-sp-coefficient-towers (blueprint: sk-def-sp-coefficient-towers). -/
instance finiteMon (n : ℕ) : MonObj (finiteRing l E n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  inferInstance

/-- That quotient multiplication is commutative.
Source: sk-def-sp-coefficient-towers (blueprint: sk-def-sp-coefficient-towers). -/
instance finiteComm (n : ℕ) : IsCommMonObj (finiteRing l E n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Profinite.isCommMonObj_continuousCoefficientRingObj _

/-- Actual continuous postcomposition with the ell-power quotient map.
Source: sk-def-sp-coefficient-towers (blueprint: sk-lem-sp-tower). -/
def quotient (n : ℕ) : DerivedNakayama.integerRing l E ⟶ finiteRing l E n :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let q : DerivedNakayama.integerRingSheaf l E ⟶ finiteRingSheaf l E n :=
    ⟨{ app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            (((Ideal.Quotient.mk (ellIdeal l E ^ (n + 1))).compLeftContinuous _
              continuous_quot_mk).comp ULift.ringEquiv.toRingHom))
       naturality := fun _ _ _ ↦ rfl }⟩
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map q

/-- The actual consecutive quotient of the finite coefficient rings.
Source: sk-def-sp-coefficient-towers (blueprint: sk-lem-sp-tower). -/
def step (n : ℕ) : finiteRing l E (n + 1) ⟶ finiteRing l E n :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let q : finiteRingSheaf l E (n + 1) ⟶ finiteRingSheaf l E n :=
    ⟨{ app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            (((Ideal.Quotient.factorPowSucc (ellIdeal l E) (n + 1)).compLeftContinuous _
              (continuous_quot_lift _ continuous_quot_mk)).comp
                ULift.ringEquiv.toRingHom))
       naturality := fun _ _ _ ↦ rfl }⟩
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map q

/-- The actual ell-power quotient preserves the coefficient multiplication.
Source: sk-def-sp-coefficient-towers (blueprint: sk-def-sp-coefficient-towers). -/
instance quotientMon (n : ℕ) : IsMonHom (quotient l E n) := by
  unfold quotient
  infer_instance

/-- The consecutive quotient map preserves the coefficient multiplication.
Source: sk-def-sp-coefficient-towers (blueprint: sk-def-sp-coefficient-towers). -/
instance stepMon (n : ℕ) : IsMonHom (step l E n) := by
  unfold step
  infer_instance

variable (T : Scheme.{u})

/-- Current integral derived category over p_T^* O_E.
Source: sk-def-sfb-pulled-back-coefficients (blueprint: sk-lem-sp-tower). -/
abbrev Integral := DerivedCategory (AdicCompletion.Modules l E T)

/-- Current bounded constructible category; completeness is not part of its definition.
Source: sk-def-sfb-constructible (blueprint: sk-lem-sp-tower). -/
abbrev Dbc := ConstantModelBoundedConstructible (DerivedNakayama.integerRing l E) T

/-- The section-ring coefficient diagram of the actual pulled-back finite rings.
Source: sk-def-sp-coefficient-towers (blueprint: sk-lem-sp-tower). -/
def rings : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
  Functor.ofOpSequence
    (X := fun n ↦ sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
      (condensedRingObj (finiteRing l E n) T))
    (fun n ↦ sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
      ((upperStarFromPoint T).map (step l E n)))

/-- Strict varying-coefficient towers, with all semilinear transitions, without bounds.
Source: sk-def-sp-coefficient-towers (blueprint: sk-lem-sp-tower). -/
abbrev Towers := SheafOfModules.StrictRingSystem.{u + 1, u, u + 1} (rings l E T)

/-- The ordinary unbounded derived category of strict towers.
Source: sk-def-sp-normalized-towers (blueprint: sk-lem-sp-tower). -/
abbrev DerivedTowers := DerivedCategory (Towers l E T)

/-- Evaluation in the current internal-module model, through the exact section equivalence.
Source: det-sp-coefficient-towers-abelian (blueprint: sk-lem-sp-tower). -/
def evaluation (n : ℕ) : DerivedTowers l E T ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (finiteRing l E n) T)) :=
  let e := sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (condensedRingObj (finiteRing l E n) T)
  letI := Functor.additive_of_preserves_binary_products e.inverse
  SheafOfModules.derivedSystemEvaluation.{u + 1, u, u + 1} (rings l E T) n ⋙
    e.inverse.mapDerivedCategory

/-- The section equivalence on integral derived categories.
Source: coefficient convention (blueprint: sk-lem-sp-tower). -/
def sectionEquivalence : Integral l E T ≌
    DerivedCategory (ringedSiteModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
          (AdicCompletion.ring l E T)))) :=
  let e := sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (AdicCompletion.ring l E T)
  letI := Functor.additive_of_preserves_binary_products e.functor
  e.mapDerivedCategory



/-- Derived scalar reduction along the actual pulled-back ell-power quotient.
Source: sk-lem-sp-tower, displayed red (blueprint: sk-lem-sp-tower). -/
abbrev finiteReduction (n : ℕ) : Integral l E T ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (finiteRing l E n) T)) :=
  (Mod.extendScalars ((upperStarFromPoint T).map (quotient l E n))).leftDerivedFunctor

/-- The actual finite tensor identifications of ordinary reduction.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
def ReductionLevels (ordinaryRed : AdicCompletion.Modules l E T ⥤ Towers l E T) :=
  ∀ n : ℕ,
    ordinaryRed ⋙ SheafOfModules.systemEvaluation.{u + 1, u, u + 1} (rings l E T) n ≅
      Mod.extendScalars ((upperStarFromPoint T).map (quotient l E n)) ⋙
        (sectionModuleEquivalence (Scheme.ProEt.topology T)
          (condensedRingObj (finiteRing l E n) T)).functor

/-- The tensor-unit generator 1 tensor x, in the exact section coordinates.
Source: ordinary scalar adjunction (blueprint: sk-def-sp-coefficient-towers). -/
def reductionGenerator (n : ℕ) (P : AdicCompletion.Modules l E T) (U : T.ProEtᵒᵖ)
    (x : P.X.obj.obj U) :
    (((sectionModuleEquivalence (Scheme.ProEt.topology T)
      (condensedRingObj (finiteRing l E n) T)).functor.obj
        ((Mod.extendScalars ((upperStarFromPoint T).map (quotient l E n))).obj P)).val.obj U) :=
  (((Mod.extendRestrictAdjunction ((upperStarFromPoint T).map (quotient l E n))).unit.app
    P).hom.hom.app U) x

set_option maxHeartbeats 1600000 in
-- Compare the section and internal tensor coordinates of the quotient unit.
/-- The quotient-induced semilinear transition sends 1 tensor x to 1 tensor x.
Linearity then determines it on every local tensor generator c tensor x.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
def ReductionTransitions (ordinaryRed : AdicCompletion.Modules l E T ⥤ Towers l E T)
    (ordinaryLevels : ReductionLevels l E T ordinaryRed) : Prop :=
  ∀ (P : AdicCompletion.Modules l E T) (n : ℕ) (U : T.ProEtᵒᵖ) (x : P.X.obj.obj U)
    (a : ((ordinaryRed.obj P).level (n + 1)).val.obj U)
    (b : ((ordinaryRed.obj P).level n).val.obj U),
    HEq (((ordinaryLevels (n + 1)).hom.app P).val.app U a)
      (reductionGenerator l E T (n + 1) P U x) →
    HEq b ((((ordinaryRed.obj P).transition (Nat.le_succ n)).val.app U) a) →
    HEq (((ordinaryLevels n).hom.app P).val.app U b)
      (reductionGenerator l E T n P U x)

set_option maxHeartbeats 1600000 in
-- Checking these dependent construction coordinates needs the larger kernel budget.
/-- Canonical reduction/limit coordinates. Ordinary tensor reduction has the specified
quotient transitions on unit generators; the derived functors are the universal
left and right derived functors of those specified ordinary functors. The structure
contains no constructibility, equivalence or derived adjunction assertion.
Source: sk-lem-sp-tower, construction of red and Rlim (blueprint: sk-lem-sp-tower). -/
structure OrdinaryReduction where
  ordinaryRed : AdicCompletion.Modules l E T ⥤ Towers l E T
  ordinaryLimit : Towers l E T ⥤ AdicCompletion.Modules l E T
  [redAdditive : ordinaryRed.Additive]
  [limitAdditive : ordinaryLimit.Additive]
  ordinaryAdjunction : ordinaryRed ⊣ ordinaryLimit
  ordinaryLevels : ReductionLevels l E T ordinaryRed
  ordinaryTransition : ReductionTransitions l E T ordinaryRed ordinaryLevels
attribute [instance] OrdinaryReduction.redAdditive OrdinaryReduction.limitAdditive

/-- The ordinary finite reduction in internal coordinates, using the actual
section-equivalence unit. Source: sk-lem-sp-tower
(blueprint: sk-def-sp-coefficient-towers). -/
def ordinaryInternalLevels (O : OrdinaryReduction l E T) (n : ℕ) :
    O.ordinaryRed ⋙ SheafOfModules.systemEvaluation.{u + 1, u, u + 1} (rings l E T) n ⋙
      (sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
        (condensedRingObj (finiteRing l E n) T)).inverse ≅
    Mod.extendScalars ((upperStarFromPoint T).map (quotient l E n)) :=
  Functor.isoWhiskerRight (O.ordinaryLevels n)
      (sectionModuleEquivalence (Scheme.ProEt.topology T)
        (condensedRingObj (finiteRing l E n) T)).inverse ≪≫
    Functor.isoWhiskerLeft (Mod.extendScalars ((upperStarFromPoint T).map (quotient l E n)))
      (sectionModuleEquivalence (Scheme.ProEt.topology T)
        (condensedRingObj (finiteRing l E n) T)).unitIso.symm

/-- Exact evaluation on representatives, followed by the specified ordinary tensor
identification. Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
def representativeLevels (O : OrdinaryReduction l E T) (n : ℕ)
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    (evaluation l E T n).obj
        (DerivedCategory.Q.obj ((O.ordinaryRed.mapHomologicalComplex (.up ℤ)).obj P)) ≅
    DerivedCategory.Q.obj
      (((Mod.extendScalars ((upperStarFromPoint T).map (quotient l E n))).mapHomologicalComplex
        (.up ℤ)).obj P) :=
  let e := sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
    (condensedRingObj (finiteRing l E n) T)
  letI := Functor.additive_of_preserves_binary_products e.inverse
  e.inverse.mapDerivedCategory.mapIso
      ((SheafOfModules.systemEvaluation.{u + 1, u, u + 1}
        (rings l E T) n).mapDerivedCategoryFactors.app
          ((O.ordinaryRed.mapHomologicalComplex (.up ℤ)).obj P)) ≪≫
    e.inverse.mapDerivedCategoryFactors.app
      (((SheafOfModules.systemEvaluation.{u + 1, u, u + 1}
        (rings l E T) n).mapHomologicalComplex (.up ℤ)).obj
          ((O.ordinaryRed.mapHomologicalComplex (.up ℤ)).obj P)) ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (ordinaryInternalLevels l E T O n) (.up ℤ)).app P)

/-- The generic left-derived tensor counit, transported from homotopy to cochain
coordinates by the standard localization factors. Source: sk-lem-sp-tower
(blueprint: sk-def-sp-coefficient-towers). -/
def finiteCounit (n : ℕ) (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    (finiteReduction l E T n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((Mod.extendScalars ((upperStarFromPoint T).map (quotient l E n))).mapHomologicalComplex
          (.up ℤ)).obj P) :=
  let F := Mod.extendScalars ((upperStarFromPoint T).map (quotient l E n))
  F.leftDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso (AdicCompletion.Modules l E T)).inv.app P) ≫
    F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P)

set_option maxHeartbeats 1600000 in
-- Checking these dependent construction coordinates needs the larger kernel budget.
/-- Universal total derived functors of the specified tensor/limit pair.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
structure DerivedReduction (O : OrdinaryReduction l E T) where
  red : Integral l E T ⥤ DerivedTowers l E T
  redCounit : DerivedCategory.Q ⋙ red ⟶
    O.ordinaryRed.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  redUniversal : red.IsLeftDerivedFunctor redCounit
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ))
  rlim : DerivedTowers l E T ⥤ Integral l E T
  limitUnit : O.ordinaryLimit.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ rlim
  limitUniversal : rlim.IsRightDerivedFunctor limitUnit
    (HomologicalComplex.quasiIso (Towers l E T) (.up ℤ))
  levels : ∀ n : ℕ, red ⋙ evaluation l E T n ≅ finiteReduction l E T n
  /-- The Levels are the derived ordinary identifications, including their counits. -/
  levels_counit : ∀ (n : ℕ) (P : CochainComplex (AdicCompletion.Modules l E T) ℤ),
    (levels n).hom.app (DerivedCategory.Q.obj P) ≫ finiteCounit l E T n P =
      (evaluation l E T n).map (redCounit.app P) ≫
        (representativeLevels l E T O n P).hom
/-- Canonical coefficient reduction, its total limit, and its actual scalar maps.
The three fields only group the construction and universal-property data above.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
structure Model where
  ordinary : OrdinaryReduction l E T
  derived : DerivedReduction l E T ordinary
  reductions : SheafOfModules.SystemLevelLeftExtensionTheory.{u + 1, u, u + 1}
    (J := Scheme.ProEt.topology T)

namespace Model
variable {l E T} (D : Model l E T)

/-- Projection of the canonical construction data.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
abbrev ordinaryRed := D.ordinary.ordinaryRed

/-- Projection of the canonical construction data.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
abbrev ordinaryLimit := D.ordinary.ordinaryLimit

/-- Projection of the canonical construction data.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
abbrev ordinaryAdjunction := D.ordinary.ordinaryAdjunction

/-- Projection of the canonical construction data.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
abbrev ordinaryLevels := D.ordinary.ordinaryLevels

/-- Projection of the canonical construction data.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
abbrev ordinaryTransition := D.ordinary.ordinaryTransition

/-- Projection of the canonical construction data.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
abbrev red := D.derived.red

/-- Projection of the canonical construction data.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
abbrev redCounit := D.derived.redCounit

/-- Projection of the canonical construction data.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
abbrev redUniversal := D.derived.redUniversal

/-- Projection of the canonical construction data.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
abbrev rlim := D.derived.rlim

/-- Projection of the canonical construction data.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
abbrev limitUnit := D.derived.limitUnit

/-- Projection of the canonical construction data.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
abbrev limitUniversal := D.derived.limitUniversal

/-- Projection of the canonical construction data.
Source: sk-lem-sp-tower (blueprint: sk-def-sp-coefficient-towers). -/
abbrev levels := D.derived.levels

/-- The already existing normalized scalar data; no second scalar model is defined.
Source: det-sp-coefficient-towers-abelian(3) (blueprint: sk-def-sp-coefficient-towers). -/
abbrev scalar : SheafOfModules.SystemScalarAssignment.{u + 1, u, u + 1}
    (J := Scheme.ProEt.topology T) :=
  D.reductions.scalar

/-- The adjoint of the localized actual strict transition. The existing theory fixes
its transition on every representative and its identity normalization.
Source: det-sp-coefficient-towers-abelian(3) (blueprint: sk-def-sp-coefficient-towers). -/
def reduction {m n : ℕ} (h : m ≤ n) :
    SheafOfModules.derivedSystemEvaluation.{u + 1, u, u + 1} (rings l E T) n ⋙
      SheafOfModules.systemDerivedTensor D.scalar (rings l E T) h ⟶
        SheafOfModules.derivedSystemEvaluation.{u + 1, u, u + 1} (rings l E T) m :=
  (((SheafOfModules.systemDerivedTensorAdj D.scalar (rings l E T) h).whiskerRight
      (DerivedTowers l E T)).homEquiv _ _).symm (D.reductions.transition (rings l E T) h)

end Model

/-- Section-ring maps of a factored internal ring map factor accordingly. -/
private theorem sectionScalarMap_eq_comp {R S Q : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj Q] [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj Q]
    {a : R ⟶ Q} {b : R ⟶ S} {c : S ⟶ Q} [IsMonHom a] [IsMonHom b] [IsMonHom c]
    (h : a = b ≫ c) :
    sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) a =
      sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) b ≫
        sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) c := by
  subst h
  ext U x
  rfl

/-- On sections, a section-ring map is the underlying internal ring map. -/
private theorem sectionScalarMap_hom_app_apply
    {R S : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (a : R ⟶ S) [IsMonHom a]
    (U : T.ProEtᵒᵖ) (x : R.obj.obj U) :
    (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T) a).hom.app U x =
      a.hom.app U x :=
  rfl

/-- The ell-power quotient maps are compatible with the consecutive quotients. -/
private theorem quotient_comp_step (n : ℕ) :
    quotient l E (n + 1) ≫ step l E n = quotient l E n :=
  CoefficientQuotientTower.pointQuotientMap_comp_pointFactorMap l E _

/-- The cone of section-ring quotient maps. -/
private def quotientCone : Cone (rings l E T) :=
  ⟨sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (AdicCompletion.ring l E T),
    NatTrans.ofOpSequence (fun n ↦ sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
      ((upperStarFromPoint T).map (quotient l E n))) (fun n ↦ by
        simp only [Functor.const_obj_map, rings, Functor.ofOpSequence_map_homOfLE_succ]
        refine (Category.id_comp _).trans (sectionScalarMap_eq_comp T ?_)
        rw [← Functor.map_comp, quotient_comp_step])⟩

/-- On sections, the section-ring tower is the pulled-back quotient tower. -/
private def sectionsIso (U : T.ProEtᵒᵖ) :
    CoefficientQuotientTower.pullbackSequence l E (fun n ↦ ellIdeal l E ^ (n + 1)) T
        (fun n ↦ Ideal.pow_le_pow_right (n + 1).le_succ) ⋙
      sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1} ⋙
        (CategoryTheory.evaluation _ _).obj U ⋙ forget Ab.{u + 1} ≅
    ((rings l E T ⋙ sheafToPresheaf _ _) ⋙ (CategoryTheory.evaluation _ _).obj U) ⋙
      forget CommRingCat.{u + 1} where
  hom := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
    simp only [Functor.comp_map, rings, CoefficientQuotientTower.pullbackSequence,
      Functor.ofOpSequence_map_homOfLE_succ]
    ext x
    exact (sectionScalarMap_hom_app_apply T
      ((upperStarFromPoint T).map (step l E n)) U x).symm)
  inv := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
    simp only [Functor.comp_map, rings, CoefficientQuotientTower.pullbackSequence,
      Functor.ofOpSequence_map_homOfLE_succ]
    ext x
    exact sectionScalarMap_hom_app_apply T ((upperStarFromPoint T).map (step l E n)) U x)

/-- The pulled-back continuous integer ring is the inverse limit of its positive
ell-power quotients, with the actual quotient projections. The point equality transports
only the cone vertex, never its legs. Source: sk-def-sp-coefficient-towers, displayed
inverse limit (blueprint: sk-def-sp-coefficient-towers).
Proof: continuous maps into the complete integer ring are exactly compatible families
of continuous maps into all finite quotients. The ell- and uniformizer-power ideals are
cofinal, also for ramified E. Pullback to the replete small pro-etale topos preserves
this countable inverse limit; the local lifting calculation identifies every projection
with quotient. Taking section ring sheaves gives precisely this cone and its universal
property. -/
theorem coefficient_limit :
    ∃ c : Cone (rings l E T), ∃ e : c.pt ≅
      sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology T) (AdicCompletion.ring l E T),
      (∀ n : ℕ, c.π.app (op n) = e.hom ≫
        sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology T)
          ((upperStarFromPoint T).map (quotient l E n))) ∧ Nonempty (IsLimit c) := by
  obtain ⟨r, hr, hpow⟩ := CoefficientQuotientTower.ell_pow_eq_coefficientExtensionIdeal l E
  have hlim := (CoefficientQuotientTower.pullbackCone_isLimit l E
    (fun n ↦ ellIdeal l E ^ (n + 1)) T (fun n ↦ Ideal.pow_le_pow_right (n + 1).le_succ)
    (fun n ↦ ⟨r * (n + 1), Nat.le_mul_of_pos_left _ hr, hpow n⟩)).some
  refine ⟨quotientCone l E T, Iso.refl _, fun n ↦ (Category.id_comp _).symm, ⟨?_⟩⟩
  apply isLimitOfReflects (sheafToPresheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
  apply evaluationJointlyReflectsLimits
  intro U
  have : ReflectsLimitsOfShape ℕᵒᵖ (forget CommRingCat.{u + 1}) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply isLimitOfReflects (forget CommRingCat.{u + 1})
  refine (IsLimit.equivOfNatIsoOfIso (sectionsIso l E T U) _ _ ?_) (isLimitOfPreserves _ hlim)
  refine Cone.ext (Iso.refl _) (fun n ↦ ?_)
  ext x
  exact (sectionScalarMap_hom_app_apply T
    ((upperStarFromPoint T).map (quotient l E n.unop)) U x).symm

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
