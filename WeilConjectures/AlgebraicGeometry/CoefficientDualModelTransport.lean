/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.RationalSliceCompletedEvaluation
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralScalarData
public import WeilConjectures.AlgebraicGeometry.ConstantCoefficientScalarNormalization
public import WeilConjectures.SixFunctors.RingedFiniteFreeHomBaseChangeData
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.SixFunctors.RingedFiniteFreeHomBaseChange
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestrictionSupplement

import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.CategoryTheory.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Homology.KFlatSupplement
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.AlgebraicGeometry.IntegralOperationsScalarComparisons
import WeilConjectures.Algebra.Homology.RingedSliceEvaluationTranspose
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.Abelian.SplitSESBoundaryComparison
import WeilConjectures.CategoryTheory.ScalarLocalizationTriangulated
import WeilConjectures.AlgebraicGeometry.SfScalarExtensionComposition

/-! # Restriction and coefficient transport of local dual models

Source: main-20261015 blueprint, sec-six-functors/sk-prop-sf-dualizable-biduality,
local dual model sentence; Stacks Tags 08JB, 08J7, 08J9 and 0152
(blueprint: lem-sf-coefficient-dual-model-transport).

The declarations `coefficientDualModelTransport`, `dualFiniteFreeRetract`,
`scalarLocalModels`, `scalarTailTriangles`, `scalarRestrictionDualCompatibility`,
`finiteScalarDualCoherence` and `commonStageDualModelTransport` state the clauses.

The global site and actual slice sites are the recorded `IntegralOnSlice` sites.
The Hom is the ambient K-injective Hom and the rational categories are raw scalar
localizations. No integral splitting of a rational retraction is requested.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v t
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AlgebraicGeometry

namespace WeilConjectures.CoefficientDualModels

open IntegralOnSlice
attribute [local irreducible] HasDerivedCategory.standard IntegralOnSlice.duality

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{t})

/-- The raw rational image of the actual coefficient unit.
Source: Stacks 08J7 (blueprint: lem-sf-coefficient-dual-model-transport). -/
def unit (U : Option X.ProEt) : Rational l E X U :=
  (q l E X U).obj (coefficient l E X U)

/-- The actual finite sum of completed units in degree zero, then scalar-localized.
The empty sum is included. Source: Stacks 08J7
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def free (U : Option X.ProEt) (m : ℕ) : Rational l E X U :=
  (q l E X U).obj ((DerivedCategory.singleFunctor (Mod l E X U) 0).obj
    (SheafOfModules.free.{max u (t + 1), t, t + 1}
      (R := rings l E X U) (ULift.{max u (t + 1)} (Fin m))))

/-- Scalar extension of the contravariant ambient Hom into the coefficient unit is
uniquely specified on unchanged objects and pure fraction arrows.
Source: Stacks 08J7; node proof steps 1--3
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: precomposition in the ambient Hom is linear for the constant O_E action.
Extend its maps linearly to the localized Hom modules. The balancing relation
makes this well-defined. The identity and reversed-composition equations follow
on pure tensors and extend by additivity. These formulas uniquely determine
all maps, since pure tensors generate. This works on every actual slice. -/
theorem dual_existsUnique (U : Option X.ProEt) :
    ∃! H : (Rational l E X U)ᵒᵖ ⥤ Rational l E X U,
      H.Additive ∧
      (∀ K : Rational l E X U,
        H.obj (op K) = ⟨(hom l E X U).obj (op K.obj, coefficient l E X U)⟩) ∧
      (∀ (K M : D l E X U) (f : K ⟶ M)
        (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        HEq (H.map (Quiver.Hom.op
          (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
            (q l E X U).obj K ⟶ (q l E X U).obj M)))
          (a ⊗ₜ[Padic.coefficientExtensionIntegers l E]
            (hom l E X U).map (Prod.mkHom f.op (𝟙 (coefficient l E X U))))) := by
  sorry

/-- The scalar-localized ambient internal Hom into the recorded unit.
Source: Stacks 08J7 (blueprint: lem-sf-coefficient-dual-model-transport). -/
def dual (U : Option X.ProEt) : (Rational l E X U)ᵒᵖ ⥤ Rational l E X U :=
  (dual_existsUnique l E X U).exists.choose

/-- Rational restriction of the degree-zero coefficient comparison.
Source: Stacks 03DH (blueprint: lem-sf-coefficient-dual-model-transport). -/
def unitRestriction {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    (restrictionRational l E X a).obj (unit l E X U) ≅ unit l E X V :=
  (q l E X V).mapIso (restrictionCoefficientIso l E X a)

/-- The localized Hom comparison associated to the actual integral restriction datum.
The map of the second Hom input is the recorded coefficient-unit identification.
Source: Stacks 08JB (blueprint: lem-sf-coefficient-dual-model-transport). -/
def integralDualRestriction {U V : Option X.ProEt} {a : RestrictionArrow X U V}
    (d : CompletedRestrictionComparisons l E X a) (K : D l E X U) :
    (restrictionDerived l E X a).obj
        ((hom l E X U).obj (op K, coefficient l E X U)) ≅
      (hom l E X V).obj (op ((restrictionDerived l E X a).obj K), coefficient l E X V) :=
  d.homIso.app (op K, coefficient l E X U) ≪≫
    (hom l E X V).mapIso
      (Iso.prod (Iso.refl _) (restrictionCoefficientIso l E X a))

/-- Evaluation at one, expressed through the normalized ordinary tensor unitor.
The unitor is scalar multiplication on K-flat representatives, so this map is
literally evaluation at the section one, rather than an arbitrary unit automorphism.
Source: Stacks 08J7, node proof step 2
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def integralUnitEvaluation (U : Option X.ProEt) :
    (hom l E X U).obj (op (coefficient l E X U), coefficient l E X U) ⟶
      coefficient l E X U :=
  ((duality l E X U).closed.monoidal.rightUnitor _).inv ≫
    (duality l E X U).closed.tensor.map
      (Prod.mkHom (𝟙 _) (duality l E X U).unitIso.hom) ≫
    (duality l E X U).closed.evaluation (coefficient l E X U) (coefficient l E X U)

/-- The j-th actual standard generator, in degree zero and then rationalized.
Source: Stacks 08J7, node proof step 2
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def freeGenerator (U : Option X.ProEt) (m : ℕ) (j : Fin m) :
    unit l E X U ⟶ free l E X U m :=
  (q l E X U).map ((DerivedCategory.singleFunctor (Mod l E X U) 0).map
    (SheafOfModules.ιFree (R := rings l E X U) (ULift.up j)))

/-- The standard coordinate projection, using the coproduct universal property.
Source: Stacks 08J7, node proof step 2
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def freeProjection (U : Option X.ProEt) (m : ℕ) (j : Fin m) :
    free l E X U m ⟶ unit l E X U :=
  (q l E X U).map ((DerivedCategory.singleFunctor (Mod l E X U) 0).map
    ((SheafOfModules.isColimitFreeCofan (R := rings l E X U)
      (ULift.{max u (t + 1)} (Fin m))).desc
        (Cofan.mk (SheafOfModules.unit (rings l E X U))
          (fun k ↦ if k.down = j then 𝟙 _ else 0))))

/-- Natural dual restriction, successive-restriction coherence, and the unit square.
Source: Stacks 08JB; node proof steps 1--3
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: use the ambient ringed-site Hom restriction with second argument R_E.
Exact module restriction preserves the unit and representatives. Localize the
comparison and its inverse. Naturality on integral arrows extends to fraction
arrows by linearity, and the successive-restriction equations remain equalities.
Evaluation at 1 identifies Hom(R_E,I) with I for a K-injective unit resolution.
This evaluation commutes with restriction; hence the displayed unit square.
No constructibility is imposed on the restricted representatives. -/
theorem coefficientDualModelTransport
    (_hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x)) :
    ∃ (d : ∀ (U V : Option X.ProEt) (a : RestrictionArrow X U V),
        CompletedRestrictionComparisons l E X a),
      (∀ (U V : Option X.ProEt) (a : RestrictionArrow X U V), (d U V a).Normalized) ∧
      CompletedRestrictionComparisons.Coherent l E X d ∧
      ∃ (e : ∀ (U V : Option X.ProEt) (a : RestrictionArrow X U V),
          dual l E X U ⋙ restrictionRational l E X a ≅
            (restrictionRational l E X a).op ⋙ dual l E X V)
        (η : ∀ U : Option X.ProEt, (dual l E X U).obj (op (unit l E X U)) ≅ unit l E X U),
        (∀ U : Option X.ProEt, HEq (η U).hom
          ((q l E X U).map (integralUnitEvaluation l E X U))) ∧
        (∀ (U V : Option X.ProEt) (a : RestrictionArrow X U V)
          (K : Rational l E X U),
          HEq ((e U V a).hom.app (op K))
            ((q l E X V).map (integralDualRestriction l E X (d U V a) K.obj).hom)) ∧
        (∀ (U V : Option X.ProEt) (a : RestrictionArrow X U V),
          (restrictionRational l E X a).map (η U).hom ≫ (unitRestriction l E X a).hom =
            (e U V a).hom.app (op (unit l E X U)) ≫
              (dual l E X V).map (unitRestriction l E X a).inv.op ≫ (η V).hom) := by
  sorry

/-- Dualizing an actual localized finite-free retraction gives its dual retraction.
The displayed maps need not lift to integral retractions.
Source: node proof steps 2--3 (blueprint: lem-sf-coefficient-dual-model-transport).
Proof: evaluation on the m standard generators identifies the Hom of the rank-m
unit with m copies of a K-injective resolution of the unit. The finite direct sum
of the augmentations is a quasi-isomorphism, giving the first isomorphism.
Contravariance sends i followed by p to H(p) followed by H(i). Their composite
is the identity, so conjugating by the finite-free isomorphism gives the asserted
retraction. When m=0 both complexes and all maps are zero. -/
theorem dualFiniteFreeRetract (U : Option X.ProEt) (m : ℕ) :
    ∃ e : (dual l E X U).obj (op (free l E X U m)) ≅ free l E X U m,
      (∀ j : Fin m, HEq (e.hom ≫ freeProjection l E X U m j)
        ((q l E X U).map
          ((hom l E X U).map (Prod.mkHom
            ((DerivedCategory.singleFunctor (Mod l E X U) 0).map
              (SheafOfModules.ιFree (R := rings l E X U) (ULift.up j))).op (𝟙 _)) ≫
            integralUnitEvaluation l E X U))) ∧
      ∀ (F : Mod l E X U)
        (i : (q l E X U).obj ((DerivedCategory.singleFunctor (Mod l E X U) 0).obj F) ⟶
          free l E X U m)
        (p : free l E X U m ⟶
          (q l E X U).obj ((DerivedCategory.singleFunctor (Mod l E X U) 0).obj F)),
        i ≫ p = 𝟙 _ →
          ((dual l E X U).map p.op ≫ e.hom) ≫
            (e.inv ≫ (dual l E X U).map i.op) = 𝟙 _ := by
  sorry

/-- The canonical O_E action on module maps on the actual slice.
Source: constant-section action in raw scalar localization
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: multiply each component of a module map by the specified constant section.
Its restriction compatibility and commutativity of the completed coefficient ring
make this a module map. The ring identities hold sectionwise, and composition is
bilinear. The displayed section formula determines every Hom module structure,
so the resulting linear structure is unique. -/
theorem moduleLinear_existsUnique (U : Option X.ProEt) :
    ∃! s : Linear (Padic.coefficientExtensionIntegers l E) (Mod l E X U),
      (fun [linearInst : Linear (Padic.coefficientExtensionIntegers l E) (Mod l E X U)] ↦
        ∀ (a : Padic.coefficientExtensionIntegers l E) (M N : Mod l E X U)
          (f : M ⟶ N) (V : (Site X U)ᵒᵖ) (x : M.val.obj V),
          (a • f).val.app V x = scalarConstant l E X U V a • f.val.app V x)
        (linearInst := s) := by
  sorry

/-- Use that sectionwise action for module localization.
Source: node proof step 5 (blueprint: lem-sf-coefficient-dual-model-transport). -/
instance moduleLinear (U : Option X.ProEt) :
    Linear (Padic.coefficientExtensionIntegers l E) (Mod l E X U) :=
  (moduleLinear_existsUnique l E X U).exists.choose

/-- Raw localization of module sheaves, with no added objects or idempotents.
Source: node proof step 5 (blueprint: lem-sf-coefficient-dual-model-transport). -/
abbrev RationalModules (U : Option X.ProEt) :=
  ScalarLocalization (Padic.coefficientExtensionIntegers l E) (Mod l E X U)
    (Padic.coefficientExtensionUniformizer l E)

/-- The actual module-to-localized-module functor.
Source: node proof step 5 (blueprint: lem-sf-coefficient-dual-model-transport). -/
abbrev qModules (U : Option X.ProEt) : Mod l E X U ⥤ RationalModules l E X U :=
  ScalarLocalization.localization (Padic.coefficientExtensionIntegers l E) (Mod l E X U)
    (Padic.coefficientExtensionUniformizer l E)

/-- Rank-m free module in the raw module localization.
Source: node proof steps 2--3 (blueprint: lem-sf-coefficient-dual-model-transport). -/
def freeModule (U : Option X.ProEt) (m : ℕ) : RationalModules l E X U :=
  (qModules l E X U).obj
    (SheafOfModules.free.{max u (t + 1), t, t + 1} (R := rings l E X U)
      (ULift.{max u (t + 1)} (Fin m)))

/-- A bounded rational complex models an ambient rational derived object when an
actual bounded complex gives both its localized chain presentation and derived
presentation. This is a relation, not a choice of an object or a realization map.
The bounds are part of the displayed local model, and can vary with the slice.
Source: node proof steps 5--6, bounded-complex lifting
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def Models (U : Option X.ProEt)
    (P : CochainComplex (RationalModules l E X U) ℤ)
    (K : Rational l E X U) (a b : ℤ) : Prop :=
  ∃ T : Cx l E X U,
    (∀ r : ℤ, r < a ∨ b < r → IsZero (T.X r)) ∧
    Nonempty (((qModules l E X U).mapHomologicalComplex (.up ℤ)).obj T ≅ P) ∧
    Nonempty ((q l E X U).obj (DerivedCategory.Q.obj T) ≅ K)

/-- Actual localized finite-free retract terms, retaining the rational arrows.
Source: node proof steps 3,6 (blueprint: lem-sf-coefficient-dual-model-transport). -/
def RetractTerms (U : Option X.ProEt)
    (P : CochainComplex (RationalModules l E X U) ℤ) : Prop :=
  ∀ r : ℤ, ∃ (m : ℕ) (i : P.X r ⟶ freeModule l E X U m)
    (p : freeModule l E X U m ⟶ P.X r), i ≫ p = 𝟙 _

section Scalar
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Restrict the canonical completed coefficient map to the actual slice.
Source: finite-free completed scalar comparison, Stacks 06YY
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def scalarRing (U : Option X.ProEt) : ring l E X U ⟶ ring l L X U :=
  (restrict X U).map (completedIntegralScalarCoefficientMap l E L ι X)

set_option linter.defProp false in
/-- The published ordinary/derived scalar tensor witness for this very ring map.
Its ordinary functor is specified on objects and maps and the derived functor
has its universal K-flat computation. Source: Stacks 06YY
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def scalarData (U : Option X.ProEt) :=
  letI : EssentiallySmall.{max u (t + 1)} (Site X U) := essentiallySmallSelf _
  letI : HasDerivedCategory.{(max u (t + 1)) + 1} (Mod l E X U) :=
    IntegralOnSlice.hasDerived l E X U
  letI : HasDerivedCategory.{(max u (t + 1)) + 1} (Mod l L X U) :=
    IntegralOnSlice.hasDerived l L X U
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{(max u (t + 1)) + 1,
    max u (t + 1), t + 1, t}
    (C := Site X U) (J := topology X U) (O := ring l E X U) (O' := ring l L X U)
    (scalarRing l E X L ι U)

/-- Actual sheafified scalar tensor, with no flatness assumption on the input.
Source: Stacks 06YY (blueprint: lem-sf-coefficient-dual-model-transport). -/
def scalarModules (U : Option X.ProEt) : Mod l E X U ⥤ Mod l L X U :=
  (scalarData l E X L ι U).choose

/-- Additivity of ordinary scalar tensor, supplied by its normalized witness.
Source: Stacks 06YY (blueprint: lem-sf-coefficient-dual-model-transport). -/
instance scalarModulesAdditive (U : Option X.ProEt) :
    (scalarModules l E X L ι U).Additive :=
  (scalarData l E X L ι U).choose_spec.choose_spec.choose_spec.choose

/-- Termwise extension of the actual module complexes.
Source: Stacks 015F (blueprint: lem-sf-coefficient-dual-model-transport). -/
def scalarComplex (U : Option X.ProEt) : Cx l E X U ⥤ Cx l L X U :=
  (scalarModules l E X L ι U).mapHomologicalComplex (.up ℤ)

/-- Additivity of termwise ordinary scalar extension.
Source: Stacks 015F (blueprint: lem-sf-coefficient-dual-model-transport). -/
instance scalarComplexAdditive (U : Option X.ProEt) :
    (scalarComplex l E X L ι U).Additive :=
  inferInstanceAs ((scalarModules l E X L ι U).mapHomologicalComplex (.up ℤ)).Additive

/-- The ordinary derived change of completed coefficient rings on this slice.
Source: Stacks 06YY (blueprint: lem-sf-coefficient-dual-model-transport). -/
def scalarDerived (U : Option X.ProEt) : D l E X U ⥤ D l L X U :=
  (scalarData l E X L ι U).choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose

/-- Its universal computing map on every complex.
Source: Stacks 06YY (blueprint: lem-sf-coefficient-dual-model-transport). -/
def scalarCounit (U : Option X.ProEt) (P : Cx l E X U) :
    (scalarDerived l E X L ι U).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((scalarComplex l E X L ι U).obj P) :=
  let ε : DerivedCategory.Qh ⋙ scalarDerived l E X L ι U ⟶
      (scalarModules l E X L ι U).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    (scalarData l E X L ι U).choose_spec.choose_spec.choose_spec.choose_spec.2.2
      |>.choose_spec.choose
  ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)

/-- The actual sheafified pure scalar tensor in the prescribed ordinary extension.
Source: Stacks 03EK, 08J9 (blueprint: lem-sf-coefficient-dual-model-transport). -/
def scalarSection (U : Option X.ProEt) (M : Mod l E X U)
    (W : (Site X U)ᵒᵖ) (s : (ring l L X U).obj.obj W) (x : M.val.obj W) :
    ((scalarModules l E X L ι U).obj M).val.obj W :=
  ringedFiniteFreeScalarSection (topology X U) (scalarRing l E X L ι U)
    (scalarModules l E X L ι U) (scalarData l E X L ι U).choose_spec.choose M W s x

/-- Completed coefficient sections restrict by their literal section identity.
Source: Stacks 03DH (blueprint: lem-sf-coefficient-dual-model-transport). -/
def restrictionRingSection {U V : Option X.ProEt} (a : RestrictionArrow X U V)
    (W : (Site X V)ᵒᵖ) :
    (ring l E X U).obj.obj ((restrictionSite X a).op.obj W) ≃+*
      (ring l E X V).obj.obj W :=
  match U, V, a, W with
  | none, none, _, _ => RingEquiv.refl _
  | none, some _, _, _ => RingEquiv.refl _
  | some _, none, a, _ => PEmpty.elim a
  | some _, some _, _, _ => RingEquiv.refl _

/-- The ordinary scalar/restriction comparison is uniquely fixed on tensor generators.
Source: Stacks 03EK, node proof step 4
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: restriction commutes with tensor presheaves and with sheafification on an
over-site. Send the displayed restricted generator to the same scalar tensor.
The balancing relations and sheafification yield a natural module map. Reversing
the generator formula gives its inverse. Local generation by these pure tensors
proves uniqueness. This applies also to relocalization and identity restriction. -/
theorem scalarModuleRestriction_existsUnique {U V : Option X.ProEt}
    (a : RestrictionArrow X U V) :
    ∃! σ : restrictionModules l E X a ⋙ scalarModules l E X L ι V ≅
        scalarModules l E X L ι U ⋙ restrictionModules l L X a,
      ∀ (M : Mod l E X U) (W : (Site X V)ᵒᵖ)
        (s : (ring l L X U).obj.obj ((restrictionSite X a).op.obj W))
        (x : M.val.obj ((restrictionSite X a).op.obj W)),
        (σ.hom.app M).val.app W
          (scalarSection l E X L ι V ((restrictionModules l E X a).obj M) W
            (restrictionRingSection l L X a W s) (restrictionSection l E X a M W x)) =
        restrictionSection l L X a ((scalarModules l E X L ι U).obj M) W
          (scalarSection l E X L ι U M ((restrictionSite X a).op.obj W) s x) := by
  sorry

/-- The uniquely normalized module scalar/restriction comparison.
Source: Stacks 03EK (blueprint: lem-sf-coefficient-dual-model-transport). -/
def scalarModuleRestriction {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    restrictionModules l E X a ⋙ scalarModules l E X L ι V ≅
      scalarModules l E X L ι U ⋙ restrictionModules l L X a :=
  (scalarModuleRestriction_existsUnique l E X L ι a).exists.choose

/-- Derived scalar/restriction comparison with its computing square on all complexes.
Source: node proof steps 4--5, Stacks 015F
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: ordinary restriction and finite-free scalar tensor are exact, so derive
the normalized ordinary comparison termwise. Its naturality with the universal
scalar counit gives the displayed square. Every complex computes scalar tensor,
and quasi-isomorphism localization makes that square determine the natural
comparison uniquely. Its inverse is induced by the inverse ordinary comparison. -/
theorem scalarDerivedRestriction_existsUnique {U V : Option X.ProEt}
    (a : RestrictionArrow X U V) :
    ∃! σ : restrictionDerived l E X a ⋙ scalarDerived l E X L ι V ≅
        scalarDerived l E X L ι U ⋙ restrictionDerived l L X a,
      ∀ P : Cx l E X U,
        (scalarDerived l E X L ι V).map ((restrictionLocalization l E X a).hom.app P) ≫
          scalarCounit l E X L ι V ((restrictionComplex l E X a).obj P) ≫
          DerivedCategory.Q.map
            (((scalarModuleRestriction l E X L ι a).hom.mapHomologicalComplex (.up ℤ)).app P) =
        σ.hom.app (DerivedCategory.Q.obj P) ≫
          (restrictionDerived l L X a).map (scalarCounit l E X L ι U P) ≫
          (restrictionLocalization l L X a).hom.app ((scalarComplex l E X L ι U).obj P) := by
  sorry

/-- The comparison fixed by that universal computing square.
Source: Stacks 015F (blueprint: lem-sf-coefficient-dual-model-transport). -/
def scalarDerivedRestriction {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    restrictionDerived l E X a ⋙ scalarDerived l E X L ι V ≅
      scalarDerived l E X L ι U ⋙ restrictionDerived l L X a :=
  (scalarDerivedRestriction_existsUnique l E X L ι a).exists.choose

/-- Extension of the actual fraction fields, expressed in the published localization
coordinates. Source: blueprint scalar extension paragraph
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def scalarCoefficient :
    Localization.Away (Padic.coefficientExtensionUniformizer l E) →+*
      Localization.Away (Padic.coefficientExtensionUniformizer l L) :=
  (sfRationalCoefficientEquiv l L).symm.toRingHom.comp
    (ι.toRingHom.comp (sfRationalCoefficientEquiv l E).toRingHom)

/-- On every slice, finite-free extension is exact and computes its derived functor
termwise on every complex, not only on K-flat complexes.
Source: node proof steps 4--5; Stacks 015F
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: R_L is finite free over R_E. A basis restricts to each slice. After scalar
restriction tensor is a finite direct sum, so kernels and cokernels are computed
componentwise. Exact-functor derived factorization gives termwise computation.
On K-flat complexes its computing map is the universal derived counit. The
localization universal property identifies the factorization with the specified
derived tensor and makes this same counit invertible on all complexes. -/
theorem scalarExact (U : Option X.ProEt) :
    PreservesFiniteLimits (scalarModules l E X L ι U) ∧
    PreservesFiniteColimits (scalarModules l E X L ι U) ∧
    (scalarDerived l E X L ι U).Additive ∧
    ∀ P : Cx l E X U, IsIso (scalarCounit l E X L ι U P) := by
  sorry

/-- The rational ambient scalar functor is determined on every object and pure tensor.
Source: node proof steps 4--5, raw localization arrow formulas
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: ordinary derived tensor is semilinear for the canonical integral inclusion.
Extend its Hom maps using the specified map of fraction fields. Balancing gives
well-defined additive maps, and the integral functor laws give identities and
composition on pure tensors, hence on all sums. These formulas determine the
functor uniquely and include ramified and identity extensions. -/
theorem scalarRational_existsUnique (U : Option X.ProEt) :
    ∃! F : Rational l E X U ⥤ Rational l L X U,
      F.Additive ∧
      (∀ K : Rational l E X U, F.obj K = ⟨(scalarDerived l E X L ι U).obj K.obj⟩) ∧
      (∀ (K M : D l E X U) (f : K ⟶ M)
        (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        HEq (F.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
          (q l E X U).obj K ⟶ (q l E X U).obj M))
          (scalarCoefficient l E L ι a ⊗ₜ[Padic.coefficientExtensionIntegers l L]
            (scalarDerived l E X L ι U).map f)) := by
  sorry

/-- Raw rational extension on the slice, with unchanged integral objects and the
specified scalar map on arrows. Source: node proof steps 4--5
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def scalarRational (U : Option X.ProEt) : Rational l E X U ⥤ Rational l L X U :=
  (scalarRational_existsUnique l E X L ι U).exists.choose

/-- Rationalize the prescribed scalar/restriction map without changing its components.
Source: node proof step 4, raw localization
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: extend integral naturality to pure fraction arrows using semilinearity.
All objects are unchanged integral representatives, so the component formula
uniquely specifies the rational natural isomorphism and its inverse. -/
theorem scalarRationalRestriction_existsUnique {U V : Option X.ProEt}
    (a : RestrictionArrow X U V) :
    ∃! σ : restrictionRational l E X a ⋙ scalarRational l E X L ι V ≅
        scalarRational l E X L ι U ⋙ restrictionRational l L X a,
      ∀ K : Rational l E X U, HEq (σ.hom.app K)
        ((q l L X V).map ((scalarDerivedRestriction l E X L ι a).hom.app K.obj)) := by
  sorry

/-- The prescribed raw rational scalar/restriction comparison.
Source: node proof step 4 (blueprint: lem-sf-coefficient-dual-model-transport). -/
def scalarRationalRestriction {U V : Option X.ProEt} (a : RestrictionArrow X U V) :
    restrictionRational l E X a ⋙ scalarRational l E X L ι V ≅
      scalarRational l E X L ι U ⋙ restrictionRational l L X a :=
  (scalarRationalRestriction_existsUnique l E X L ι a).exists.choose

/-- Normalization of the scalar unit by ordinary multiplication and its universal
computing counit. The section formula includes evaluation on one and all scalars.
Source: Stacks 06YY, node proof step 4
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def IntegralScalarUnitNormalized (U : Option X.ProEt)
    (e : (scalarDerived l E X L ι U).obj (coefficient l E X U) ≅ coefficient l L X U) :
    Prop :=
  ∃ μ : (scalarModules l E X L ι U).obj (SheafOfModules.unit (rings l E X U)) ≅
      SheafOfModules.unit (rings l L X U),
    (∀ (W : (Site X U)ᵒᵖ) (s : (ring l L X U).obj.obj W)
      (x : (ring l E X U).obj.obj W),
      μ.hom.val.app W (scalarSection l E X L ι U
        (SheafOfModules.unit (rings l E X U)) W s x) =
          s * (scalarRing l E X L ι U).hom.app W x) ∧
    e.hom = scalarCounit l E X L ι U
        (ringedSiteDualityUnitComplex (topology X U) (ring l E X U)) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (scalarModules l E X L ι U) (.up ℤ) 0).hom.app
            (SheafOfModules.unit (rings l E X U))) ≫
      (DerivedCategory.singleFunctor (Mod l L X U) 0).map μ.hom

/-- The strong scalar tensor comparison is fixed on pure generators and on every
K-flat computing square. This is precisely the tensor normalization used by
finite-free Hom base change, for the already specified ordinary scalar functor.
Source: Stacks 07A4, 08J9, node proof step 4
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def ScalarTensorNormalized (U : Option X.ProEt)
    (κ : coefficientTotalTensor.{u, t + 1, t} (topology X U) (ring l E X U) ⋙
        scalarComplex l E X L ι U ≅
      (scalarComplex l E X L ι U).prod (scalarComplex l E X L ι U) ⋙
        coefficientTotalTensor.{u, t + 1, t} (topology X U) (ring l L X U))
    (μ : (duality l E X U).closed.tensor ⋙ scalarDerived l E X L ι U ≅
      (scalarDerived l E X L ι U).prod (scalarDerived l E X L ι U) ⋙
        (duality l L X U).closed.tensor) : Prop :=
  (∀ (P Q : Cx l E X U) (p q : ℤ) (W : (Site X U)ᵒᵖ)
    (x : (P.X p).val.obj W) (y : (Q.X q).val.obj W),
    ((κ.hom.app (P, Q)).f (p + q)).val.app W
      (scalarSection l E X L ι U
        (((coefficientTotalTensor.{u, t + 1, t} (topology X U)
          (ring l E X U)).obj (P, Q)).X (p + q)) W 1
        (coefficientTensorGenerator.{u, t + 1, t} (topology X U) (ring l E X U)
          P Q p q (p + q) rfl W x y)) =
      coefficientTensorGenerator.{u, t + 1, t} (topology X U) (ring l L X U)
        ((scalarComplex l E X L ι U).obj P) ((scalarComplex l E X L ι U).obj Q)
        p q (p + q) rfl W
        (scalarSection l E X L ι U (P.X p) W 1 x)
        (scalarSection l E X L ι U (Q.X q) W 1 y)) ∧
  (∀ (P Q : Cx l E X U)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := topology X U) (R := ring l E X U) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := topology X U) (R := ring l E X U) Q),
    ∃ (hEP : CochainComplex.IsKFlatIndependentCoefficients
        (J := topology X U) (R := ring l L X U) ((scalarComplex l E X L ι U).obj P))
      (hEQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := topology X U) (R := ring l L X U) ((scalarComplex l E X L ι U).obj Q)),
      (scalarDerived l E X L ι U).map
          (((duality l E X U).models.iso (topology X U) (ring l E X U)
            (duality l E X U).closed P Q hP hQ).hom) ≫
        μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (duality l L X U).closed.tensor.map
          (Prod.mkHom (scalarCounit l E X L ι U P) (scalarCounit l E X L ι U Q)) =
      scalarCounit l E X L ι U
          ((coefficientTotalTensor.{u, t + 1, t} (topology X U)
            (ring l E X U)).obj (P, Q)) ≫
        DerivedCategory.Q.map (κ.hom.app (P, Q)) ≫
        ((duality l L X U).models.iso (topology X U) (ring l L X U)
          (duality l L X U).closed _ _ hEP hEQ).hom)

/-- The scalar dual map is the rationalized finite-free Hom base-change transpose,
followed by Hom of multiplication on the coefficient unit. Every auxiliary
comparison is fixed by the same generator and K-flat computing equations.
Source: Stacks 08J9, node proof step 4
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def ScalarDualNormalized (U : Option X.ProEt)
    (β : dual l E X U ⋙ scalarRational l E X L ι U ≅
      (scalarRational l E X L ι U).op ⋙ dual l L X U)
    (ε : (scalarRational l E X L ι U).obj (unit l E X U) ≅ unit l L X U) : Prop :=
  ∃ e : (scalarDerived l E X L ι U).obj (coefficient l E X U) ≅ coefficient l L X U,
    IntegralScalarUnitNormalized l E X L ι U e ∧
    HEq ε.hom ((q l L X U).map e.hom) ∧
    ∃ (κ : coefficientTotalTensor.{u, t + 1, t} (topology X U) (ring l E X U) ⋙
          scalarComplex l E X L ι U ≅
        (scalarComplex l E X L ι U).prod (scalarComplex l E X L ι U) ⋙
          coefficientTotalTensor.{u, t + 1, t} (topology X U) (ring l L X U))
      (μ : (duality l E X U).closed.tensor ⋙ scalarDerived l E X L ι U ≅
        (scalarDerived l E X L ι U).prod (scalarDerived l E X L ι U) ⋙
          (duality l L X U).closed.tensor)
      (α : hom l E X U ⋙ scalarDerived l E X L ι U ≅
        (scalarDerived l E X L ι U).op.prod (scalarDerived l E X L ι U) ⋙ hom l L X U),
      ScalarTensorNormalized l E X L ι U κ μ ∧
      (∀ P Q : D l E X U, α.hom.app (op P, Q) =
        (duality l L X U).closed.transpose _
          ((scalarDerived l E X L ι U).obj P) ((scalarDerived l E X L ι U).obj Q)
          (μ.inv.app ((hom l E X U).obj (op P, Q), P) ≫
            (scalarDerived l E X L ι U).map ((duality l E X U).closed.evaluation P Q))) ∧
      (∀ K : Rational l E X U, HEq (β.hom.app (op K))
        ((q l L X U).map (α.hom.app (op K.obj, coefficient l E X U) ≫
          (hom l L X U).map (Prod.mkHom (𝟙 _) e.hom))))

/-- Natural scalar comparison for duals on the actual ambient slices, with finite
free sums and the degree-zero coefficient units identified by scalar tensor.
Source: Stacks 08J9; node proof step 4
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: apply finite-free ambient Hom base change to (K,R_E). The Hom comparison
is the closed transpose of extended evaluation; identify the extended unit by
multiplication. Scalar-localize this natural isomorphism and its inverse. A basis
is used only to prove invertibility, so the map is independent of that basis.
The unit and finite-sum identifications use the same multiplication. -/
theorem scalarDualComparison (U : Option X.ProEt) :
    ∃ (β : dual l E X U ⋙ scalarRational l E X L ι U ≅
        (scalarRational l E X L ι U).op ⋙ dual l L X U)
      (ε : (scalarRational l E X L ι U).obj (unit l E X U) ≅ unit l L X U),
      ScalarDualNormalized l E X L ι U β ε ∧
      ∀ m : ℕ, ∃ e : (scalarRational l E X L ι U).obj (free l E X U m) ≅
          free l L X U m,
        ∀ j : Fin m,
          (scalarRational l E X L ι U).map (freeGenerator l E X U m j) ≫ e.hom =
            ε.hom ≫ freeGenerator l L X U m j := by
  sorry

/-- The dual comparison commutes with the prescribed scalar/restriction map,
including its unit square. Both Hom restriction maps retain their integral normalization.
Source: node proof step 4, Stacks 08JB and 08J9
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: choose the normalized ambient finite-free Hom comparison by transposing
extended evaluation. Restriction preserves evaluation and transpose. The scalar
restriction map sends each tensor generator to itself, so the two transposed
pairings coincide. This proves the first square. On the coefficient unit the
same argument is scalar multiplication, proving the second square. Localize
the integral equalities; linearity proves them on arbitrary fraction morphisms. -/
theorem scalarRestrictionDualCompatibility {U V : Option X.ProEt}
    (a : RestrictionArrow X U V)
    (dE : CompletedRestrictionComparisons l E X a) (_hE : dE.Normalized)
    (dL : CompletedRestrictionComparisons l L X a) (_hL : dL.Normalized) :
    ∃ (eE : dual l E X U ⋙ restrictionRational l E X a ≅
        (restrictionRational l E X a).op ⋙ dual l E X V)
      (eL : dual l L X U ⋙ restrictionRational l L X a ≅
        (restrictionRational l L X a).op ⋙ dual l L X V)
      (βU : dual l E X U ⋙ scalarRational l E X L ι U ≅
        (scalarRational l E X L ι U).op ⋙ dual l L X U)
      (βV : dual l E X V ⋙ scalarRational l E X L ι V ≅
        (scalarRational l E X L ι V).op ⋙ dual l L X V)
      (εU : (scalarRational l E X L ι U).obj (unit l E X U) ≅ unit l L X U)
      (εV : (scalarRational l E X L ι V).obj (unit l E X V) ≅ unit l L X V),
      ScalarDualNormalized l E X L ι U βU εU ∧
      ScalarDualNormalized l E X L ι V βV εV ∧
      (∀ K : Rational l E X U, HEq (eE.hom.app (op K))
        ((q l E X V).map (integralDualRestriction l E X dE K.obj).hom)) ∧
      (∀ K : Rational l L X U, HEq (eL.hom.app (op K))
        ((q l L X V).map (integralDualRestriction l L X dL K.obj).hom)) ∧
      (∀ K : Rational l E X U,
        (scalarRational l E X L ι V).map (eE.hom.app (op K)) ≫
          βV.hom.app (op ((restrictionRational l E X a).obj K)) ≫
          (dual l L X V).map ((scalarRationalRestriction l E X L ι a).inv.app K).op =
        (scalarRationalRestriction l E X L ι a).hom.app ((dual l E X U).obj (op K)) ≫
          (restrictionRational l L X a).map (βU.hom.app (op K)) ≫
          eL.hom.app (op ((scalarRational l E X L ι U).obj K))) ∧
      (scalarRational l E X L ι V).map (unitRestriction l E X a).hom ≫ εV.hom =
        (scalarRationalRestriction l E X L ι a).hom.app (unit l E X U) ≫
          (restrictionRational l L X a).map εU.hom ≫ (unitRestriction l L X a).hom := by
  sorry

/-- Ordinary scalar tensor also has its prescribed extension on raw module Homs.
Source: node proof steps 5--6
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: termwise tensor is semilinear for the integral coefficient inclusion.
Extend the maps on Hom modules along scalarCoefficient. Balancing, identities
and composition are checked on pure tensors and extended by addition. The object
formula and these maps determine a unique additive functor. -/
theorem scalarRationalModules_existsUnique (U : Option X.ProEt) :
    ∃! F : RationalModules l E X U ⥤ RationalModules l L X U,
      F.Additive ∧
      (∀ K : RationalModules l E X U, F.obj K = ⟨(scalarModules l E X L ι U).obj K.obj⟩) ∧
      (∀ (K M : Mod l E X U) (f : K ⟶ M)
        (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        HEq (F.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
          (qModules l E X U).obj K ⟶ (qModules l E X U).obj M))
          (scalarCoefficient l E L ι a ⊗ₜ[Padic.coefficientExtensionIntegers l L]
            (scalarModules l E X L ι U).map f)) := by
  sorry

/-- The actual raw module scalar functor, characterized on every fraction arrow.
Source: node proof step 5 (blueprint: lem-sf-coefficient-dual-model-transport). -/
def scalarRationalModules (U : Option X.ProEt) :
    RationalModules l E X U ⥤ RationalModules l L X U :=
  (scalarRationalModules_existsUnique l E X L ι U).exists.choose

/-- Additivity of the specified raw module scalar functor.
Source: node proof step 5 (blueprint: lem-sf-coefficient-dual-model-transport). -/
instance scalarRationalModulesAdditive (U : Option X.ProEt) :
    (scalarRationalModules l E X L ι U).Additive :=
  (scalarRationalModules_existsUnique l E X L ι U).exists.choose_spec.1

/-- Apply that functor termwise, including to localized differentials.
Source: node proof step 5 (blueprint: lem-sf-coefficient-dual-model-transport). -/
def scalarRationalComplex (U : Option X.ProEt) :
    CochainComplex (RationalModules l E X U) ℤ ⥤
      CochainComplex (RationalModules l L X U) ℤ :=
  (scalarRationalModules l E X L ι U).mapHomologicalComplex (.up ℤ)

/-- Coefficient extension preserves each supplied local model, its exact bounds,
and its actual rational finite-free retractions. It suffices to state this on
one arbitrary slice: applying it to each member gives every coefficient-site
cover, with unrelated bounds and ranks on different members.
Source: node proof steps 5--6 (blueprint: lem-sf-coefficient-dual-model-transport).
Proof: lift the bounded fraction complex to an actual complex with the same
support. Exact scalar tensor computes the derived scalar functor termwise by
scalarExact. Apply it to the supplied derived-model isomorphism and then use
scalarDualComparison. Tensor sends zero to zero, so the same interval works.
For every displayed term retraction, functoriality preserves i followed by p.
Multiplication and the finite-sum comparison identify its middle object with
the corresponding free L-module. The rational chain isomorphism transports the
model calculation back to the supplied complex, without lifting its retractions. -/
theorem scalarLocalModels (U : Option X.ProEt)
    (K : Rational l E X U) (P : CochainComplex (RationalModules l E X U) ℤ)
    (a b : ℤ)
    (_hbounded : ∀ r : ℤ, r < a ∨ b < r → IsZero (P.X r))
    (_hmodel : Models l E X U P ((dual l E X U).obj (op K)) a b)
    (_hretract : RetractTerms l E X U P) :
    (∀ r : ℤ, r < a ∨ b < r →
      IsZero (((scalarRationalComplex l E X L ι U).obj P).X r)) ∧
    Models l L X U ((scalarRationalComplex l E X L ι U).obj P)
      ((dual l L X U).obj (op ((scalarRational l E X L ι U).obj K))) a b ∧
    RetractTerms l L X U ((scalarRationalComplex l E X L ι U).obj P) ∧
    ∃ e : ∀ m : ℕ,
        (scalarRationalModules l E X L ι U).obj (freeModule l E X U m) ≅
          freeModule l L X U m,
      (∀ m : ℕ, ∃ μ :
          (scalarModules l E X L ι U).obj
            (SheafOfModules.free (R := rings l E X U) (ULift.{max u (t + 1)} (Fin m))) ≅
          SheafOfModules.free (R := rings l L X U) (ULift.{max u (t + 1)} (Fin m)),
        (∀ (j : Fin m) (W : (Site X U)ᵒᵖ) (s : (ring l L X U).obj.obj W)
          (x : (ring l E X U).obj.obj W),
          μ.hom.val.app W (scalarSection l E X L ι U _ W s
            ((SheafOfModules.ιFree (R := rings l E X U) (ULift.up j)).val.app W x)) =
          (SheafOfModules.ιFree (R := rings l L X U) (ULift.up j)).val.app W
            (s * (scalarRing l E X L ι U).hom.app W x)) ∧
        HEq (e m).hom ((qModules l L X U).map μ.hom)) ∧
      ∀ (r : ℤ) (m : ℕ) (i : P.X r ⟶ freeModule l E X U m)
        (p : freeModule l E X U m ⟶ P.X r), i ≫ p = 𝟙 _ →
          ((scalarRationalModules l E X L ι U).map i ≫ (e m).hom) ≫
            ((e m).inv ≫ (scalarRationalModules l E X L ι U).map p) = 𝟙 _ := by
  sorry

/-- The canonical computing comparison carries the whole short-exact-sequence
triangle, including its connecting morphism, to termwise scalar extension.
In particular this applies to every finite stupid-tail sequence of a bounded
model and to its actual inclusion, projection and boundary comparison maps.
Source: node proof step 7; Stacks 0152 and 015F
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: finite-free ordinary tensor is exact. Use the exact-functor factorization
with its canonical shift comparison and the same scalarCounit. Applied to a
complex short exact sequence, its naturality gives the squares for inclusion
and projection. In a degreewise split tail sequence the boundary is Q(b), where
b in the cutoff degree is the model differential. Tensor preserves its displayed
identity/zero splitting, so the extended boundary is Q(F(b)). The split-boundary
comparison and the factorization's shift compatibility give the third square.
Equivalently use naturality of the canonical cone construction for a general
short exact sequence. The components of the triangle isomorphism are precisely
the computing counits, as recorded below. Scalar localization preserves all
three equalities, hence also the localized tail comparison maps. -/
theorem scalarTailTriangles (U : Option X.ProEt) :
    ∃ s : (scalarDerived l E X L ι U).CommShift ℤ,
      (fun [commInst : (scalarDerived l E X L ι U).CommShift ℤ] ↦
        ∀ (S : ShortComplex (Cx l E X U)) (hS : S.ShortExact),
          ∃ hFS : (S.map (scalarComplex l E X L ι U)).ShortExact,
            ∃ e : (scalarDerived l E X L ι U).mapTriangle.obj
                (DerivedCategory.triangleOfSES hS) ≅ DerivedCategory.triangleOfSES hFS,
              e.hom.hom₁ = scalarCounit l E X L ι U S.X₁ ∧
              e.hom.hom₂ = scalarCounit l E X L ι U S.X₂ ∧
              e.hom.hom₃ = scalarCounit l E X L ι U S.X₃ ∧
              (q l L X U).map
                  ((scalarDerived l E X L ι U).map (DerivedCategory.triangleOfSESδ hS) ≫
                    ((scalarDerived l E X L ι U).commShiftIso (1 : ℤ)).hom.app
                      (DerivedCategory.Q.obj S.X₁) ≫
                    (scalarCounit l E X L ι U S.X₁)⟦(1 : ℤ)⟧') =
                (q l L X U).map
                  (scalarCounit l E X L ι U S.X₃ ≫ DerivedCategory.triangleOfSESδ hFS))
        (commInst := s) := by
  sorry

end Scalar

section Global
variable (X : Scheme.{u}) (hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x))

include hInv in
/-- The actual completed unit belongs to the recorded integral constructible domain.
Source: rank-one model, blueprint local dual model sentence
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: its reductions are the constant rank-one finite coefficient sheaves,
concentrated in degree zero, so the same interval [0,0] works at every level.
The quotient transitions are surjective. The derived inverse limit is their
ordinary limit, namely the completed coefficient sheaf, and its augmentation
is the actual reduction unit. This gives derived completeness and the
constructibility predicate without any finiteness or separatedness on X. -/
theorem unit_constructible : sfIntegralConstructible l E X (coefficient l E X none) := by
  sorry

/-- The intrinsic integral unit, retaining its actual completed underlying object.
Source: blueprint local dual model sentence
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def integralStageUnit : sfIntegralConstructibleCategory l E X :=
  ⟨coefficient l E X none, unit_constructible l E X hInv⟩

/-- The unit of the raw rational constructible category, not a Karoubi object.
Source: blueprint rational coefficient paragraph
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def stageUnit : sfRationalConstructibleCategory l E X :=
  (sfRationalConstructibleLocalization l E X).obj (integralStageUnit l E X hInv)

/-- The permitted pair defining the specified constructible dual.
Source: def-weil-derived-pullback-tensor-hom, rational paragraph
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def stageDualPair (K : sfRationalConstructibleCategory l E X)
    (h : constructibleRationalHomPairs l E X (op K, stageUnit l E X hInv)) :
    (constructibleRationalHomPairs l E X).FullSubcategory :=
  ⟨(op K, stageUnit l E X hInv), h⟩

/-- The specified rational constructible dual, on precisely its recorded Hom domain.
Source: def-weil-derived-pullback-tensor-hom, rational paragraph
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def stageDual (K : sfRationalConstructibleCategory l E X)
    (h : constructibleRationalHomPairs l E X (op K, stageUnit l E X hInv)) :
    sfRationalConstructibleCategory l E X :=
  (rationalDerivedInternalHom l E X).obj (stageDualPair l E X hInv K h)

/-- Contravariant action of the specified constructible internal Hom into the unit.
Source: rational Hom arrow formula
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def stageDualMap (K K' : sfRationalConstructibleCategory l E X)
    (h : constructibleRationalHomPairs l E X (op K, stageUnit l E X hInv))
    (h' : constructibleRationalHomPairs l E X (op K', stageUnit l E X hInv))
    (f : K ⟶ K') : stageDual l E X hInv K' h' ⟶ stageDual l E X hInv K h :=
  (rationalDerivedInternalHom l E X).map
    (ObjectProperty.homMk (Prod.mkHom f.op (𝟙 (stageUnit l E X hInv))))

/-- The constructible-to-ambient rational inclusion preserves the actual fraction
arrows and unchanged underlying integral objects.
Source: raw rationalization in def-weil-rationalization-karoubi
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: the integral inclusion is fully faithful and linear for the same constant
section action. Extend its Hom maps linearly to raw localization. The pure-tensor
formula preserves identities and composition, and determines the additive map
on every Hom group. Thus it determines a unique additive functor. -/
theorem stageInclusion_existsUnique :
    ∃! J : sfRationalConstructibleCategory l E X ⥤ Rational l E X none,
      J.Additive ∧
      (∀ K : sfRationalConstructibleCategory l E X, J.obj K = ⟨K.obj.obj⟩) ∧
      (∀ (K M : sfIntegralConstructibleCategory l E X) (f : K ⟶ M)
        (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
        HEq (J.map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f :
          (sfRationalConstructibleLocalization l E X).obj K ⟶
            (sfRationalConstructibleLocalization l E X).obj M))
          (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f.hom)) := by
  sorry

/-- Actual inclusion, specified on every pure fraction arrow.
Source: raw rationalization (blueprint: lem-sf-coefficient-dual-model-transport). -/
def stageInclusion : sfRationalConstructibleCategory l E X ⥤ Rational l E X none :=
  (stageInclusion_existsUnique l E X).exists.choose

/-- The ambient dual and the specified constructible dual agree on exactly the
permitted domain, including their contravariant rational morphism action.
Source: def-weil-derived-pullback-tensor-hom, rational arrow formulas
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: both underlying objects are the same ambient integral Hom into R_E.
Their maps on an integral pure fraction are precomposition with that integral
map times its scalar, by the two recorded formulas. Additivity gives equality
for every fraction arrow. The resulting identity-on-representatives comparison
is natural and invertible. -/
theorem stageDual_ambient
    (K : sfRationalConstructibleCategory l E X)
    (h : constructibleRationalHomPairs l E X (op K, stageUnit l E X hInv)) :
    ∃ e : (stageInclusion l E X).obj (stageDual l E X hInv K h) ≅
        (dual l E X none).obj (op ((stageInclusion l E X).obj K)),
      HEq e.hom (𝟙 ((q l E X none).obj
        ((hom l E X none).obj (op K.obj.obj, coefficient l E X none)))) := by
  sorry

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Finite coefficient extension carries the specified constructible dual to the
specified dual of the extended input, naturally on its permitted Hom domain.
Source: node proof step 4, integral operation scalar comparison
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: rationalHomScalarComparison is the rationalization of the specified
integral Hom comparison. Its second input is scalar extension of the completed
unit. Multiplication identifies that extension with the new completed unit.
Postcomposition on Hom with this identification gives the displayed comparison.
Constructibility is invariant under the underlying integral unit isomorphism,
so the target pair is permitted. Naturality follows from the recorded Hom scalar
comparison and multiplication. No assumption on an intermediate resolution is used. -/
theorem stageScalarDual (K : sfRationalConstructibleCategory l E X)
    (h : constructibleRationalHomPairs l E X (op K, stageUnit l E X hInv)) :
    ∃ (hL : constructibleRationalHomPairs l L X
        (op ((sfRationalScalarExtension l E X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K), stageUnit l L X hInv))
      (ε : (sfRationalScalarExtension l E X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj (stageUnit l E X hInv) ≅
        stageUnit l L X hInv)
      (β : (sfRationalScalarExtension l E X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj (stageDual l E X hInv K h) ≅
        stageDual l L X hInv ((sfRationalScalarExtension l E X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K) hL),
      HEq ((stageInclusion l L X).map ε.hom)
        ((q l L X none).map (constantCoefficientIntegralScalarIso l E L ι X).hom) ∧
      β.hom = (rationalHomScalarComparison l E L ι X
        (stageDualPair l E X hInv K h)).hom ≫
        (rationalDerivedInternalHom l L X).map
          (ObjectProperty.homMk
            (X := rationalHomScalarPair l E L ι X (stageDualPair l E X hInv K h))
            (Y := stageDualPair l L X hInv _ hL)
            (Prod.mkHom (𝟙 _) ε.hom)) := by
  sorry

end Global

section CommonStage
open AlgebraicallyClosedCoefficients (Coefficient)
open GeneralAlgebraicallyClosedCoefficients
variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (X : Scheme.{u}) (hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x))

/-- The coefficient unit represented at any chosen finite coefficient stage.
Source: common-stage coefficient definition
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def commonUnit (E : Padic.FiniteCoefficientFields l Ω) :
    generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  ⟨E, stageUnit l (Coefficient.{u} l Ω E) X hInv⟩

/-- The original finite-stage permitted pair is permitted in the common-stage Hom domain.
Source: common-stage operation definition, node proof step 8
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: the compositum of E with E is E. Transport the permitted finite-stage
pair through the recorded scalar identity comparison; constructibility is
invariant under its underlying integral isomorphism. -/
theorem commonDual_permitted (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X)
    (h : constructibleRationalHomPairs l (Coefficient.{u} l Ω E) X
      (op K, stageUnit l (Coefficient.{u} l Ω E) X hInv)) :
    commonStageHomPairs l Ω X
      (op ((inclusion (l := l) (Ω := Ω) (Y := X) E).obj K), commonUnit l Ω X hInv E) := by
  sorry

/-- The literal permitted pair used by common-stage internal Hom.
Source: common-stage operation definition
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def commonDualPair (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X)
    (h : constructibleRationalHomPairs l (Coefficient.{u} l Ω E) X
      (op K, stageUnit l (Coefficient.{u} l Ω E) X hInv)) :
    (commonStageHomPairs l Ω X).FullSubcategory :=
  ⟨(op ((inclusion (l := l) (Ω := Ω) (Y := X) E).obj K), commonUnit l Ω X hInv E),
    commonDual_permitted l Ω X hInv E K h⟩

/-- The recorded common-stage Hom object on that permitted pair.
Source: common-stage operation definition
(blueprint: lem-sf-coefficient-dual-model-transport). -/
def commonDual (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X)
    (h : constructibleRationalHomPairs l (Coefficient.{u} l Ω E) X
      (op K, stageUnit l (Coefficient.{u} l Ω E) X hInv)) :
    generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  commonStageHomObject l Ω X (commonDualPair l Ω X hInv E K h)

/-- The permitted dual domain is preserved by the specified finite-stage transition.
Source: scalar comparison specialized to the unit, node proof step 4
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: the transition is the recorded scalar extension. Apply stageScalarDual
and use the scalar unit identification in its second Hom input. -/
theorem finiteScalarDualDomain
    (E L : Padic.FiniteCoefficientFields l Ω) (hEL : E ≤ L)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X)
    (_h : constructibleRationalHomPairs l (Coefficient.{u} l Ω E) X
      (op K, stageUnit l (Coefficient.{u} l Ω E) X hInv)) :
    constructibleRationalHomPairs l (Coefficient.{u} l Ω L) X
      (op ((transition l Ω X E L hEL).obj K),
        stageUnit l (Coefficient.{u} l Ω L) X hInv) := by
  sorry

/-- The coefficient dual comparisons form one natural family, normalized by the
specified Hom scalar comparison, the tensor unit and the scalar associators.
The displayed tower identity includes the inverse first-variable comparison.
Source: node proof steps 4 and 8; integral scalar identity/tower equations
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: take the scalar unit maps given by multiplication on completed coefficient
sheaves. Their ordinary tensor generator formulas commute with two successive
scalar extensions, and the completed comparisons preserve those equalities.
Compose rationalHomScalarComparison with Hom of this unit map. Its naturality
and contravariant first argument give the naturality equation below. For a tower,
apply the recorded integral Hom tower equation and the unit tower equation,
then scalar-localize; the inverse source associator is forced by contravariance.
For the identity field extension, the same formula is the tensor unitor. These
equalities hold on all integral representatives and pure fraction arrows, hence
on the entire permitted raw rational Hom domain. -/
theorem finiteScalarDualCoherence :
    ∃ (ε : ∀ (E L : Padic.FiniteCoefficientFields l Ω) (hEL : E ≤ L),
        (transition l Ω X E L hEL).obj
          (stageUnit l (Coefficient.{u} l Ω E) X hInv) ≅
            stageUnit l (Coefficient.{u} l Ω L) X hInv)
      (β : ∀ (E L : Padic.FiniteCoefficientFields l Ω) (hEL : E ≤ L)
        (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X)
        (hK : constructibleRationalHomPairs l (Coefficient.{u} l Ω E) X
          (op K, stageUnit l (Coefficient.{u} l Ω E) X hInv)),
        (transition l Ω X E L hEL).obj
          (stageDual l (Coefficient.{u} l Ω E) X hInv K hK) ≅
        stageDual l (Coefficient.{u} l Ω L) X hInv
          ((transition l Ω X E L hEL).obj K)
          (finiteScalarDualDomain l Ω X hInv E L hEL K hK)),
      (∀ (E L : Padic.FiniteCoefficientFields l Ω) (hEL : E ≤ L)
        (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X)
        (hK : constructibleRationalHomPairs l (Coefficient.{u} l Ω E) X
          (op K, stageUnit l (Coefficient.{u} l Ω E) X hInv)),
        (β E L hEL K hK).hom =
          (rationalHomScalarComparison l (Coefficient.{u} l Ω E)
            (Coefficient.{u} l Ω L)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL) X
            (stageDualPair l (Coefficient.{u} l Ω E) X hInv K hK)).hom ≫
          (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) X).map
            (ObjectProperty.homMk
              (X := rationalHomScalarPair l (Coefficient.{u} l Ω E)
                (Coefficient.{u} l Ω L)
                (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL) X
                (stageDualPair l (Coefficient.{u} l Ω E) X hInv K hK))
              (Y := stageDualPair l (Coefficient.{u} l Ω L) X hInv
                ((transition l Ω X E L hEL).obj K)
                (finiteScalarDualDomain l Ω X hInv E L hEL K hK))
              (Prod.mkHom (𝟙 _) (ε E L hEL).hom))) ∧
      (∀ (E L : Padic.FiniteCoefficientFields l Ω) (hEL : E ≤ L),
        HEq ((stageInclusion l (Coefficient.{u} l Ω L) X).map (ε E L hEL).hom)
          ((q l (Coefficient.{u} l Ω L) X none).map
            (constantCoefficientIntegralScalarIso l (Coefficient.{u} l Ω E)
              (Coefficient.{u} l Ω L)
              (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL) X).hom)) ∧
      (∀ E : Padic.FiniteCoefficientFields l Ω,
        (ε E E le_rfl).hom = (unitor l Ω X E).hom.app
          (stageUnit l (Coefficient.{u} l Ω E) X hInv)) ∧
      (∀ (E L M : Padic.FiniteCoefficientFields l Ω) (hEL : E ≤ L) (hLM : L ≤ M),
        (transition l Ω X L M hLM).map (ε E L hEL).hom ≫ (ε L M hLM).hom =
          (associator l Ω X E L M hEL hLM).hom.app
            (stageUnit l (Coefficient.{u} l Ω E) X hInv) ≫ (ε E M (hEL.trans hLM)).hom) ∧
      (∀ (E L M : Padic.FiniteCoefficientFields l Ω) (hEL : E ≤ L) (hLM : L ≤ M)
        (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X)
        (hK : constructibleRationalHomPairs l (Coefficient.{u} l Ω E) X
          (op K, stageUnit l (Coefficient.{u} l Ω E) X hInv)),
        (transition l Ω X L M hLM).map (β E L hEL K hK).hom ≫
          (β L M hLM ((transition l Ω X E L hEL).obj K)
            (finiteScalarDualDomain l Ω X hInv E L hEL K hK)).hom ≫
          stageDualMap l (Coefficient.{u} l Ω M) X hInv _ _
            (finiteScalarDualDomain l Ω X hInv E M (hEL.trans hLM) K hK)
            (finiteScalarDualDomain l Ω X hInv L M hLM _
              (finiteScalarDualDomain l Ω X hInv E L hEL K hK))
            ((associator l Ω X E L M hEL hLM).inv.app K) =
          (associator l Ω X E L M hEL hLM).hom.app
            (stageDual l (Coefficient.{u} l Ω E) X hInv K hK) ≫
          (β E M (hEL.trans hLM) K hK).hom) ∧
      (∀ (E L : Padic.FiniteCoefficientFields l Ω) (hEL : E ≤ L)
        (K K' : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X)
        (hK : constructibleRationalHomPairs l (Coefficient.{u} l Ω E) X
          (op K, stageUnit l (Coefficient.{u} l Ω E) X hInv))
        (hK' : constructibleRationalHomPairs l (Coefficient.{u} l Ω E) X
          (op K', stageUnit l (Coefficient.{u} l Ω E) X hInv)) (f : K ⟶ K'),
        (transition l Ω X E L hEL).map
            (stageDualMap l (Coefficient.{u} l Ω E) X hInv K K' hK hK' f) ≫
          (β E L hEL K hK).hom =
        (β E L hEL K' hK').hom ≫
          stageDualMap l (Coefficient.{u} l Ω L) X hInv _ _
            (finiteScalarDualDomain l Ω X hInv E L hEL K hK)
            (finiteScalarDualDomain l Ω X hInv E L hEL K' hK')
            ((transition l Ω X E L hEL).map f)) := by
  sorry

/-- The common-stage dual is represented at the original finite coefficient field;
its extended local dual models represent that same object at every further field.
Source: node proof step 8
(blueprint: lem-sf-coefficient-dual-model-transport).
Proof: the common-stage Hom definition uses the finite compositum stage. When
both inputs have stage E, its scalar identity comparison identifies that Hom
with (E,H_E(K)). At a larger finite stage L, stageScalarDual identifies its
extension with H_L(F K); inclusion into the pair category identifies scalar
extension with the original representative. The tower equation for the
integral scalar comparison, rationalized on pure tensors, identifies these
isomorphisms after every further common finite extension. Thus the same local
models, their scalar extensions and their tail maps give the same common-stage
dual. No idempotents or integral splittings are introduced. -/
theorem commonStageDualModelTransport
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X)
    (h : constructibleRationalHomPairs l (Coefficient.{u} l Ω E) X
      (op K, stageUnit l (Coefficient.{u} l Ω E) X hInv)) :
    ∃ e : commonDual l Ω X hInv E K h ≅
        (inclusion (l := l) (Ω := Ω) (Y := X) E).obj
          (stageDual l (Coefficient.{u} l Ω E) X hInv K h),
      (∃ c : (rationalDerivedInternalHom l (Coefficient.{u} l Ω E) X).obj
            (commonStageHomPairAtStage l Ω X (commonDualPair l Ω X hInv E K h) E
              (show E.val ⊔ E.val ≤ E.val from sup_le le_rfl le_rfl)) ≅
            stageDual l (Coefficient.{u} l Ω E) X hInv K h,
        (∃ z : (commonStageHomPairAtStage l Ω X
              (commonDualPair l Ω X hInv E K h) E
              (show E.val ⊔ E.val ≤ E.val from sup_le le_rfl le_rfl)) ≅
            stageDualPair l (Coefficient.{u} l Ω E) X hInv K h,
          z.hom.hom = Prod.mkHom
            ((unitor l Ω X E).inv.app K ≫
              (operationStageTransitionIso l Ω X E E le_rfl).inv.app K).op
            ((operationStageTransitionIso l Ω X E E le_rfl).hom.app
                (stageUnit l (Coefficient.{u} l Ω E) X hInv) ≫
              (unitor l Ω X E).hom.app (stageUnit l (Coefficient.{u} l Ω E) X hInv)) ∧
          c.hom = (rationalDerivedInternalHom l (Coefficient.{u} l Ω E) X).map z.hom) ∧
        e.hom = ((stageSystem l Ω X).isoToStage
            (commonDual l Ω X hInv E K h)
            (show E.val ⊔ E.val ≤ E.val from sup_le le_rfl le_rfl)).hom ≫
          (inclusion (l := l) (Ω := Ω) (Y := X) E).map
            ((commonStageHomComparison l Ω X (commonDualPair l Ω X hInv E K h) E
              (show E.val ⊔ E.val ≤ E.val from sup_le le_rfl le_rfl)).hom ≫ c.hom)) ∧
      ∀ (L : Padic.FiniteCoefficientFields l Ω) (hEL : E ≤ L),
        ∃ (hL : constructibleRationalHomPairs l (Coefficient.{u} l Ω L) X
            (op ((transition l Ω X E L hEL).obj K),
              stageUnit l (Coefficient.{u} l Ω L) X hInv))
          (ε : (transition l Ω X E L hEL).obj
              (stageUnit l (Coefficient.{u} l Ω E) X hInv) ≅
            stageUnit l (Coefficient.{u} l Ω L) X hInv)
          (β : (transition l Ω X E L hEL).obj
              (stageDual l (Coefficient.{u} l Ω E) X hInv K h) ≅
            stageDual l (Coefficient.{u} l Ω L) X hInv
              ((transition l Ω X E L hEL).obj K) hL)
          (eL : (inclusion (l := l) (Ω := Ω) (Y := X) L).obj
              (stageDual l (Coefficient.{u} l Ω L) X hInv
                ((transition l Ω X E L hEL).obj K) hL) ≅
            commonDual l Ω X hInv E K h),
          HEq ((stageInclusion l (Coefficient.{u} l Ω L) X).map ε.hom)
            ((q l (Coefficient.{u} l Ω L) X none).map
              (constantCoefficientIntegralScalarIso l (Coefficient.{u} l Ω E)
                (Coefficient.{u} l Ω L)
                (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL) X).hom) ∧
          β.hom = (rationalHomScalarComparison l (Coefficient.{u} l Ω E)
              (Coefficient.{u} l Ω L)
              (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL) X
              (stageDualPair l (Coefficient.{u} l Ω E) X hInv K h)).hom ≫
            (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) X).map
              (ObjectProperty.homMk
                (X := rationalHomScalarPair l (Coefficient.{u} l Ω E)
                  (Coefficient.{u} l Ω L)
                  (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL) X
                  (stageDualPair l (Coefficient.{u} l Ω E) X hInv K h))
                (Y := stageDualPair l (Coefficient.{u} l Ω L) X hInv _ hL)
                (Prod.mkHom (𝟙 _) ε.hom)) ∧
          eL.hom = (inclusion (l := l) (Ω := Ω) (Y := X) L).map
              (β.inv ≫ (operationStageTransitionIso l Ω X E L hEL).inv.app
                (stageDual l (Coefficient.{u} l Ω E) X hInv K h)) ≫
            ((stageSystem l Ω X).transIso hEL).hom.app
              (stageDual l (Coefficient.{u} l Ω E) X hInv K h) ≫ e.inv := by
  sorry

end CommonStage

end WeilConjectures.CoefficientDualModels
