/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkPropSfRfShriekPreservation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompCompositionWitnesses
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Mathlib.CategoryTheory.HomCongr
public import WeilConjectures.SmoothPurity.FiniteRingTrace.FiniteRingTraceDualizingComplex
public import WeilConjectures.ZetaWeil.FiniteRingTrace.KunnethVerdierEvaluationFormula
public import WeilConjectures.TraceFormula.ConstructibleBrownHom.ConstructibleBrownInternalHomExchange
public import WeilConjectures.ZetaWeil.FiniteRingTrace.FiniteRingExceptionalComparisons
public import WeilConjectures.ZetaWeil.FiniteRingTrace.FiniteRingProductComparisons
public import WeilConjectures.DeligneLaumon.FiniteRingTrace.TraceFormulaDualizingComplexComposition
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedArbitraryPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CurrentCtfSixFunctorStability

/-! # External duality for the fixed-point trace, arbitrary finite coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/
thm-trf-verdier-duality.md, with the coefficient scope of Wei Yang #1412 item 3
(blueprint: thm-trf-verdier-duality).

The coefficient ring `A` is an arbitrary finite commutative ring killed by a positive
power of `ell`, with its unique (discrete) topology. The self-product `X ×_s X` is the
pullback of the structure map along itself, with projections `p₁ = pullback.fst` and
`p₂ = pullback.snd`; it is the codomain of the support map `toProduct` of the
correspondence. The external product is `K ⊠ D_X K = Lp₁^* K ⊗ Lp₂^* D_X K` in this
order, with the native derived pullback, tensor and internal Hom; `D_X` is the recorded
Verdier dual. The trace-class source and the exceptional inverse image `Rc^!` are those
of `def-trf-trace-class-source` and `def-trf-correspondence`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.FiniteRingTrace

open KVConstructible

/-- The topology of the discrete condensed coefficient: the discrete topology, which is the
only discrete topology on `A`. It is literally the topology used by `coefficient A`.
Source: coefficient convention, "regarded as a discrete condensed ring"
(blueprint: thm-trf-verdier-duality). -/
abbrev vdDiscreteTopology (A : Type) [Finite A] : TopologicalSpace A := ⊥

attribute [local instance] vdDiscreteTopology

/-- The topology `vdDiscreteTopology` is discrete.
Source: coefficient convention (blueprint: thm-trf-verdier-duality). -/
local instance vdDiscrete (A : Type) [Finite A] : DiscreteTopology A :=
  discreteTopology_bot A

/-- A discrete ring is a topological ring.
Source: coefficient convention (blueprint: thm-trf-verdier-duality). -/
local instance vdTopologicalRing (A : Type) [CommRing A] [Finite A] : IsTopologicalRing A :=
  DiscreteTopology.topologicalRing

section Geometry

variable {D : FiniteFieldDatum.{u}} (X : Over (Spec (.of D.k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The self-product `Z = X ×_s X`, the pullback of the structure map along itself, as a
`k`-scheme. Its underlying scheme is the codomain of the correspondence support map.
Source: the projections `p_i` from `X ×_s X` (blueprint: thm-trf-verdier-duality). -/
abbrev vdProduct : Over (Spec (.of D.k)) :=
  Over.mk (pullback.fst X.hom X.hom ≫ X.hom)

/-- `X ×_s X` is LocallyOfFiniteType over `k`, by base change and composition.
Source: standing setting sk-def-sfb-dc-setting (blueprint: thm-trf-verdier-duality). -/
instance vdProduct_locallyOfFiniteType : LocallyOfFiniteType (vdProduct X).hom := by
  change LocallyOfFiniteType (pullback.fst X.hom X.hom ≫ X.hom)
  infer_instance

/-- `X ×_s X` is QuasiCompact over `k`, by base change and composition.
Source: standing setting sk-def-sfb-dc-setting (blueprint: thm-trf-verdier-duality). -/
instance vdProduct_quasiCompact : QuasiCompact (vdProduct X).hom := by
  change QuasiCompact (pullback.fst X.hom X.hom ≫ X.hom)
  infer_instance

/-- `X ×_s X` is IsSeparated over `k`, by base change and composition.
Source: standing setting sk-def-sfb-dc-setting (blueprint: thm-trf-verdier-duality). -/
instance vdProduct_isSeparated : IsSeparated (vdProduct X).hom := by
  change IsSeparated (pullback.fst X.hom X.hom ≫ X.hom)
  infer_instance

/-- The first projection `p₁ : X ×_s X → X`.
Source: the projections `p_i` (blueprint: thm-trf-verdier-duality). -/
abbrev vdFst : vdProduct X ⟶ X :=
  Over.homMk (pullback.fst X.hom X.hom)

/-- The second projection `p₂ : X ×_s X → X`.
Source: the projections `p_i` (blueprint: thm-trf-verdier-duality). -/
abbrev vdSnd : vdProduct X ⟶ X :=
  Over.homMk (pullback.snd X.hom X.hom) (by
    change pullback.snd X.hom X.hom ≫ X.hom = pullback.fst X.hom X.hom ≫ X.hom
    exact pullback.condition.symm)

/-- `X` in the separated finite-type category used by the Künneth–Verdier maps.
Source: standing setting sk-def-sfb-dc-setting (blueprint: thm-trf-verdier-duality). -/
abbrev vdBase : SepFinType D.k := SepFinType.mk X

/-- `X ×_s X` in the separated finite-type category.
Source: standing setting (blueprint: thm-trf-verdier-duality). -/
abbrev vdTotal : SepFinType D.k := SepFinType.mk (vdProduct X)

/-- `p₁` in the separated finite-type category.
Source: the projections `p_i` (blueprint: thm-trf-verdier-duality). -/
abbrev vdFstSep : vdTotal X ⟶ vdBase X := SepFinType.homMk (vdFst X)

/-- `p₂` in the separated finite-type category.
Source: the projections `p_i` (blueprint: thm-trf-verdier-duality). -/
abbrev vdSndSep : vdTotal X ⟶ vdBase X := SepFinType.homMk (vdSnd X)

/-- The defining Cartesian square of `X ×_s X`.
Source: the projections `p_i` (blueprint: thm-trf-verdier-duality).
Proof: `IsPullback.of_hasPullback X.hom X.hom`. -/
theorem vdIsPullback :
    IsPullback (vdFstSep X).hom.left (vdSndSep X).hom.left (vdBase X).obj.hom
      (vdBase X).obj.hom := by
  exact IsPullback.of_hasPullback X.hom X.hom

end Geometry

variable (A : Type) [CommRing A] [Finite A]
  (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
  (X : Over (Spec (.of D.k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

include ell hell hA in
/-- Pullback, tensor and internal-Hom preservation over the algebraically closed base.
Source: the constructible-domain checks in Step 2
(blueprint: thm-trf-verdier-duality). -/
private theorem vdCtfOperations
    {Y Z : Over (Spec (.of D.k))}
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (f : Y ⟶ Z) :
    (∀ K : Ctf A Z.left,
      (constantModelBoundedConstructible (coefficient A) Y.left ⊓
        DerivedCategory.finiteTorAmplitude _)
        ((upperStar (coefficient A) f.left).leftDerivedFunctor.obj K.obj)) ∧
    (∀ K L : Ctf A Y.left,
      (constantModelBoundedConstructible (coefficient A) Y.left ⊓
        DerivedCategory.finiteTorAmplitude _) (K.obj ⊗ L.obj) ∧
      (constantModelBoundedConstructible (coefficient A) Y.left ⊓
        DerivedCategory.finiteTorAmplitude _) ((ihom K.obj).obj L.obj)) := by
  let : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  let : Fact (ringChar D.k ≠ ell) := ⟨geometricCharNe D ell hell⟩
  have h := ctfSixFunctorStabilityFiniteOrAlgClosed (coefficient A) ell D.k
    (Or.inr (IsAlgClosure.isAlgClosed D.k₀)) f (coefficientAdmissible A ell hA)
  exact ⟨h.1, h.2.2.1⟩

/-- The external product `K ⊠^L_A D_X K = Lp₁^* K ⊗^L_A Lp₂^* D_X K` on `X ×_s X`, with `K`
the first factor and its Verdier dual the second.
Source: first display, and def-trf-external-product (blueprint: thm-trf-verdier-duality). -/
abbrev vdExternalProduct (K : Ctf A X.left) : Ambient A (vdProduct X).left :=
  (upperStar (coefficient A) (vdFst X).left).leftDerivedFunctor.obj K.obj ⊗
    (upperStar (coefficient A) (vdSnd X).left).leftDerivedFunctor.obj
      ((verdierDual A D ell hell hA X).obj (op K))

/-- The ordinary inverse image `U = Lp₂^* K`.
Source: first display (blueprint: thm-trf-verdier-duality). -/
abbrev vdInput (K : Ctf A X.left) : Ambient A (vdProduct X).left :=
  (upperStar (coefficient A) (vdSnd X).left).leftDerivedFunctor.obj K.obj

/-- `K ⊠ D_X K` is bounded constructible of finite Tor amplitude.
Source: proof Step 2 (sk-thm-sf-ctf-stability) (blueprint: thm-trf-verdier-duality).
Proof: `D_X K = RHom(K, ω_X)` with `ω_X` in `D^b_ctf` by the constructible exceptional
adjunction; internal Hom, pullback and tensor preserve `D^b_ctf` by the general finite-`A`
stability theorem, since `cd_ℓ(k) = 0`. -/
theorem vdExternalProduct_mem (K : Ctf A X.left) :
    (constantModelBoundedConstructible (coefficient A) (vdProduct X).left ⊓
      DerivedCategory.finiteTorAmplitude _) (vdExternalProduct A D ell hell hA X K) := by
  have hω : (constantModelBoundedConstructible (coefficient A) X.left ⊓
      DerivedCategory.finiteTorAmplitude _) (dualizingComplex A D ell hell hA X) :=
    ((exceptional A D ell hell hA X).obj (kvCoefficientUnit A D)).property
  have hD := ((vdCtfOperations A D ell hell hA (𝟙 X)).2 K ⟨_, hω⟩).2
  exact ((vdCtfOperations A D ell hell hA (𝟙 (vdProduct X))).2
    ⟨_, (vdCtfOperations A D ell hell hA (vdFst X)).1 K⟩
    ⟨_, (vdCtfOperations A D ell hell hA (vdSnd X)).1 ⟨_, hD⟩⟩).1

/-- `K ⊠ D_X K` as an object of `D^b_ctf(X ×_s X, A)`, the domain of `Rc^!`.
Source: second display (blueprint: thm-trf-verdier-duality). -/
abbrev vdExternalProductCtf (K : Ctf A X.left) : Ctf A (vdProduct X).left :=
  ⟨vdExternalProduct A D ell hell hA X K, vdExternalProduct_mem A D ell hell hA X K⟩

/-- The exceptional inverse image `Rp₁^! K` in the presentation used by the Künneth–Verdier
maps (`kvExceptional`, the constructible Brown adjoint). The whole first display is stated
in this one presentation, so the asserted isomorphism is literally `κ⁻¹`.
Source: first display (blueprint: thm-trf-verdier-duality). -/
abbrev vdKVOutput (K : Ctf A X.left) : Ambient A (vdProduct X).left :=
  ((kvExceptional A D ell hell hA (vdBase X) (vdTotal X) (vdFstSep X)).obj K).obj

/-- `(K ⊠ D_X K) ⊗ Lp₂^* K` is bounded constructible of finite Tor amplitude.
Source: proof Step 2 (blueprint: thm-trf-verdier-duality).
Proof: as for `vdExternalProduct_mem`, with one more tensor product and pullback. -/
theorem vdEvaluationSource_mem (K : Ctf A X.left) :
    (constantModelBoundedConstructible (coefficient A) (vdProduct X).left ⊓
      DerivedCategory.finiteTorAmplitude _)
      (vdExternalProduct A D ell hell hA X K ⊗ vdInput A D X K) := by
  exact ((vdCtfOperations A D ell hell hA (𝟙 (vdProduct X))).2
    (vdExternalProductCtf A D ell hell hA X K)
    ⟨_, (vdCtfOperations A D ell hell hA (vdSnd X)).1 K⟩).1

/-- The source of evaluation, `(K ⊠ D_X K) ⊗ Lp₂^* K`, in `D^b_ctf(X ×_s X, A)`.
Source: compatibility with evaluation (blueprint: thm-trf-verdier-duality). -/
abbrev vdEvaluationSourceCtf (K : Ctf A X.left) : Ctf A (vdProduct X).left :=
  ⟨_, vdEvaluationSource_mem A D ell hell hA X K⟩

/-- `T = K ⊠ ω_X = Lp₁^* K ⊗ Lp₂^* ω_X` is bounded constructible of finite Tor amplitude.
Source: proof Step 2 (blueprint: thm-trf-verdier-duality).
Proof: `ω_X` is in `D^b_ctf`; pullback and tensor preserve `D^b_ctf`. -/
theorem vdEvaluationTarget_mem (K : Ctf A X.left) :
    (constantModelBoundedConstructible (coefficient A) (vdProduct X).left ⊓
      DerivedCategory.finiteTorAmplitude _)
      ((upperStar (coefficient A) (vdFst X).left).leftDerivedFunctor.obj K.obj ⊗
        (upperStar (coefficient A) (vdSnd X).left).leftDerivedFunctor.obj
          (dualizingComplex A D ell hell hA X)) := by
  exact ((vdCtfOperations A D ell hell hA (𝟙 (vdProduct X))).2
    ⟨_, (vdCtfOperations A D ell hell hA (vdFst X)).1 K⟩
    ⟨_, (vdCtfOperations A D ell hell hA (vdSnd X)).1
      ((exceptional A D ell hell hA X).obj (kvCoefficientUnit A D))⟩).1

/-- `T = K ⊠ ω_X` in `D^b_ctf(X ×_s X, A)`.
Source: exceptional tensor–Hom compatibility (blueprint: thm-trf-verdier-duality). -/
abbrev vdEvaluationTargetCtf (K : Ctf A X.left) : Ctf A (vdProduct X).left :=
  ⟨_, vdEvaluationTarget_mem A D ell hell hA X K⟩

/-- The constructible Brown adjunction `Rp₁! ⊣ Rp₁^!` whose right functor is `kvExceptional`.
Source: exceptional tensor–Hom adjunction (blueprint: thm-trf-verdier-duality). -/
abbrev vdExceptionalDatum :=
  exceptionalDatum A D ell hell hA ((𝟙 (vdTotal X)) ≫ vdFstSep X).hom

section Correspondence

variable {A D ell hell hA X}

end Correspondence

section Comparison

variable {A D ell hell hA X}

end Comparison

set_option linter.unusedSectionVars false in
/-- `U = Lp₂^* K` is bounded constructible of finite Tor amplitude.
Source: proof Step 6 (blueprint: thm-trf-verdier-duality).
Proof: pullback preserves `D^b_ctf` (sk-thm-sf-ctf-stability). -/
theorem vdInput_mem (K : Ctf A X.left) :
    (constantModelBoundedConstructible (coefficient A) (vdProduct X).left ⊓
      DerivedCategory.finiteTorAmplitude _) (vdInput A D X K) := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : CompactSpace (vdProduct X).left :=
    QuasiCompact.compactSpace_of_compactSpace (vdProduct X).hom
  have : QuasiSeparatedSpace (vdProduct X).left :=
    quasiSeparatedSpace_of_quasiSeparated (vdProduct X).hom
  obtain ⟨h⟩ := condensed_pullback_of_constructible (coefficient A) (vdSnd X).left
    (fun M hM ↦ condensed_pullback_constructible (coefficient A) (vdSnd X).left M hM)
  exact h.constructible K.obj K.property

/-- `U = Lp₂^* K` in `D^b_ctf(X ×_s X, A)`.
Source: proof Step 6 (blueprint: thm-trf-verdier-duality). -/
abbrev vdInputCtf (K : Ctf A X.left) : Ctf A (vdProduct X).left :=
  ⟨vdInput A D X K, vdInput_mem A D X K⟩

section Comparison

variable {A D ell hell hA X}

/-- `RHom(U, V)` is bounded constructible of finite Tor amplitude.
Source: proof Step 6 (blueprint: thm-trf-verdier-duality).
Proof: internal Hom preserves `D^b_ctf` (sk-thm-sf-ctf-stability). -/
theorem vdExchangeTarget_mem (K : Ctf A X.left) :
    ConstructibleBrownHom.ctf (coefficient A) (vdProduct X).left
      ((ConstructibleBrownHom.baseHom (coefficient A)).obj
        (op (vdInputCtf A D X K),
          (kvExceptional A D ell hell hA (vdBase X) (vdTotal X) (vdFstSep X)).obj K)) := by
  exact ((vdCtfOperations A D ell hell hA (𝟙 (vdProduct X))).2
    (vdInputCtf A D X K)
    ((kvExceptional A D ell hell hA (vdBase X) (vdTotal X) (vdFstSep X)).obj K)).2

variable (ell hell hA) in
/-- `RHom(U, V)` in `D^b_ctf(X ×_s X, A)`; `ell`, `hell`, `hA` are explicit since they
are not determined by the type.
Source: proof Step 6 (blueprint: thm-trf-verdier-duality). -/
abbrev vdExchangeTargetCtf (K : Ctf A X.left) :
    (ConstructibleBrownHom.ctf (coefficient A) (vdProduct X).left).FullSubcategory :=
  ⟨(ConstructibleBrownHom.baseHom (coefficient A)).obj
      (op (vdInputCtf A D X K),
        (kvExceptional A D ell hell hA (vdBase X) (vdTotal X) (vdFstSep X)).obj K),
    vdExchangeTarget_mem (ell := ell) (hell := hell) (hA := hA) K⟩

end Comparison

end WeilConjectures.FiniteRingTrace
