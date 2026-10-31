/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.NativeSectionClosed.NativeSectionClosedForgetful
public import WeilConjectures.SixFunctors.Coef.CoefQbarVerdier

/-! # Evaluation-normalized native dual realization comparison data

Source: current blueprint, cor-coef-verdier-weil-equivariance, first-map and final
paragraphs (blueprint: def-sf-weil-dual-realization-comparison-data).
All Hom functors are the recorded native or common-stage constructions. The
native two-variable model carries its specified isomorphism to derivedHom.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open WeilConjectures WeilConjectures.AdicQbarRealization
open WeilConjectures.NativeExceptionalForgetful
open AlgebraicGeometry.ProEtaleWeilSheaf

namespace WeilConjectures.NativeDualRealization

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]
  (R : Family l D) (X : Space D)

/-- The actual structure map to the finite-field point, as an Over morphism.
Source: current blueprint, cor-coef-verdier-weil-equivariance, a_0
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
abbrev structureMap : X.base ⟶ (point D).base := Over.homMk X.base.hom

/-- The structural morphism retains separatedness from the bundled model.
Source: current blueprint, separated finite-type convention
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
instance structureMapSeparated : IsSeparated (structureMap D X).left := X.separated

/-- The structural morphism retains local finite type from the bundled model.
Source: current blueprint, separated finite-type convention
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
instance structureMapFiniteType : LocallyOfFiniteType (structureMap D X).left := X.finiteType

/-- The structural morphism retains quasi-compactness from the bundled model.
Source: current blueprint, separated finite-type convention
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
instance structureMapQuasiCompact : QuasiCompact (structureMap D X).left := X.quasiCompact

/-- The fixed exceptional adjoints, their counit-normalized comparison, and the
closed forgetful data. All choices are precisely the choices in the statement.
Source: current blueprint, cor-coef-verdier-weil-equivariance, final paragraph
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
structure Datum where
  exceptional : Package D l R
  system : StructuralSystem D l X
  compactification : Compactification (geometric D X).base.hom
  right : W D l (point D) ⥤ W D l X
  adjunction : nativeShriek D l (structureMap D X) ⊣ right
  closed : NativeSectionClosed.Comparison D l R X

variable (A : Datum D l R X)

/-- The native dualizing complex is the specified right adjoint at the constant.
Source: current blueprint, cor-coef-verdier-weil-equivariance, omega_X
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
abbrev nativeOmega : W D l X := A.right.obj (constant D l (point D))

/-- The common-stage dualizing object is the actual structural exceptional image.
Source: current blueprint, cor-coef-verdier-weil-equivariance, omega_Y
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
abbrev commonOmega : C D l X :=
  (A.system.ring.operation A.compactification .closed).G.obj (geometricPointOmega D l R)

/-- The inverse-realization model of native forgetting, with its fixed counit.
Source: current blueprint, cor-coef-verdier-weil-equivariance, M_K
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
abbrev model : W D l X ⥤ C D l X := (A.exceptional.model X).functor

/-- The specified inverse-equivalence counit j_K in ordinary module-derived objects.
Source: current blueprint, cor-coef-verdier-weil-equivariance, j_K
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
def counit (K : W D l X) :
    (rho D l R X).obj ((model D l R X A).obj K) ≅ (U D l R X).obj K :=
  (A.exceptional.model X).realization.app K

/-- The exceptional-adjunction-counit-normalized dualizing comparison h.
Source: current blueprint, cor-coef-verdier-weil-equivariance, final paragraph
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
def dualizingComparison :
    (U D l R X).obj (nativeOmega D l R X A) ≅ (rho D l R X).obj (commonOmega D l R X A) :=
  A.exceptional.actualSpecialization X (structureMap D X) A.system A.compactification
    A.right A.adjunction

/-- Native internal Hom into omega, in the recorded two-variable model.
Its nativeModel isomorphism identifies this very functor with derivedHom.
Source: current blueprint, cor-coef-verdier-weil-equivariance, native derived Hom
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
abbrev nativeHom :=
  Prod.sectL _ (nativeOmega D l R X A).obj ⋙ A.closed.native.homModels.weilHom

/-- The common-stage permitted-Hom condition, with no site-perfectness condition.
Source: current blueprint, cor-coef-verdier-weil-equivariance, D_Y M
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
def Permitted : Prop :=
  ∀ M : C D l X, commonStageHomPairs l (PadicAlgCl l) (geometric D X).base.left
    (op M, commonOmega D l R X A)

/-- Restriction of the existing common-stage internal Hom into omega_Y: the
full-subcategory lift of K ↦ (K, omega_Y) to the permitted pairs, followed by the
recorded common-stage derived internal Hom.
Source: current blueprint, cor-coef-verdier-weil-equivariance, D_Y
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
def commonDual (h : Permitted D l R X A) : (C D l X)ᵒᵖ ⥤ C D l X :=
  letI := (R.data (geometric D X)).units
  (commonStageHomPairs l (PadicAlgCl l) (geometric D X).base.left).lift
    ((𝟭 _).prod' ((Functor.const _).obj (commonOmega D l R X A))) (fun K ↦ h K.unop) ⋙
      commonStageDerivedInternalHom l (PadicAlgCl l) (geometric D X).base.left

/-- The permitted pair (M,omega_Y) in the existing full Hom-pair subcategory.
Source: current blueprint, cor-coef-verdier-weil-equivariance, internal-Hom pair
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
def pair (h : Permitted D l R X A) (M : C D l X) :
    (commonStageHomPairs l (PadicAlgCl l) (geometric D X).base.left).FullSubcategory :=
  ⟨(op M, commonOmega D l R X A), h M⟩

/-- The realization Hom comparison, defined by transposing realized evaluation.
Source: BS 6.8.15, current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
def realizationHom (h : Permitted D l R X A) (M : C D l X) :
    (rho D l R X).obj ((commonDual D l R X A h).obj (op M)) ⟶
      (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).obj
        (op ((rho D l R X).obj M), (rho D l R X).obj (commonOmega D l R X A)) :=
  letI := (R.data (geometric D X)).units
  homComparison l (geometric D X).base.left (R.data (geometric D X)).realization
    (R.data (geometric D X)).tensor (pair D l R X A h M)

/-- The invertible evaluation-transpose realization comparison.
Source: BS 6.8.15, current blueprint, cor-coef-verdier-weil-equivariance
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
def realizationHomIso (h : Permitted D l R X A) (M : C D l X) :
    (rho D l R X).obj ((commonDual D l R X A h).obj (op M)) ≅
      (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).obj
        (op ((rho D l R X).obj M), (rho D l R X).obj (commonOmega D l R X A)) :=
  letI := (R.data (geometric D X)).units
  letI : IsIso (realizationHom D l R X A h M) :=
    (R.data (geometric D X)).tensor.hom_isIso (pair D l R X A h M)
  asIso (realizationHom D l R X A h M)

/-- The actual composite c_K: native forgetting, precomposition by j_K,
postcomposition by h, and the inverse evaluation-transpose comparison.
Source: current blueprint, cor-coef-verdier-weil-equivariance, first-map paragraph
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
def comparison (h : Permitted D l R X A) (K : W D l X) :
    (NativeSectionClosed.ambientForget D l R X).obj
        ((nativeHom D l R X A).obj (op K.obj)) ≅
      (rho D l R X).obj
        ((commonDual D l R X A h).obj (op ((model D l R X A).obj K))) :=
  letI := A.closed.hom_isIso K.obj (nativeOmega D l R X A).obj
  asIso (NativeSectionClosed.sectionHomComparison A.closed.native.weilClosed
      (NativeSectionClosed.ordinaryClosed D l R X)
      (NativeSectionClosed.ambientForget D l R X) A.closed.tensor K.obj
      (nativeOmega D l R X A).obj) ≪≫
    (ambientHom l (geometric D X).base.left (R.data (geometric D X)).realization).mapIso
      (Iso.prod (counit D l R X A K).op (dualizingComparison D l R X A)) ≪≫
    (realizationHomIso D l R X A h ((model D l R X A).obj K)).symm

/-- Realized common-stage evaluation, with Hom in the first tensor factor.
Source: current blueprint, cor-coef-verdier-weil-equivariance, evaluation clause
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
def realizedEvaluation (h : Permitted D l R X A) (M : C D l X) :=
  letI := (R.data (geometric D X)).units
  (R.data (geometric D X)).tensor.tensor.hom.app
      ((commonDual D l R X A h).obj (op M), M) ≫
    (rho D l R X).map
      ((podCommonClosed l (PadicAlgCl l) (geometric D X).base.left).evaluation
        (pair D l R X A h M))

/-- The underlying native evaluation, using the inverse tensor comparison.
Source: current blueprint, cor-coef-verdier-weil-equivariance, evaluation clause
(blueprint: def-sf-weil-dual-realization-comparison-data). -/
def forgottenEvaluation (K : W D l X) :=
  (A.closed.tensor.app ((nativeHom D l R X A).obj (op K.obj), K.obj)).inv ≫
    (NativeSectionClosed.ambientForget D l R X).map
      (A.closed.native.weilClosed.evaluation K.obj (nativeOmega D l R X A).obj)

end WeilConjectures.NativeDualRealization
