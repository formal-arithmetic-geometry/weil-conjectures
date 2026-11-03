/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.FiniteRingTrace.FiniteTraceVerdierDuality
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
public import WeilConjectures.AlgebraicGeometry.FixedScheme
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.DeligneLaumon.FiniteRingTrace.TraceFormulaDualizingComplexComposition
public import WeilConjectures.ZetaWeil.FiniteRingTrace.FiniteRingExceptionalComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCanonicalPullbackComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology

/-! # The trace morphism from external duality, arbitrary finite coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/
lem-trf-trace-map-from-external-duality.md and its proof
(blueprint: lem-trf-trace-map-from-external-duality).

The coefficient ring `A` is an arbitrary finite commutative ring killed by a positive power
of `ell`, with its discrete topology, exactly as in `thm-trf-verdier-duality`. Every arrow of
the composite defining `𝔱_{c,K}` is a specified construction of a dependency:
* `ξ`, the external-duality comparison of `thm-trf-verdier-duality`;
* `e_K`, the `LΔ^* ⊣ RΔ_*` transpose of `e'` = (inverse tensor comparison of `LΔ^*`, inverse
  pullback compositors for `p_i Δ = id`, the Koszul symmetry, Verdier evaluation);
* `Bc`, the right-adjoint fixed-square base change of `thm-trf-fixed-point-base-change`;
* `γ`, the dualizing comparison of `thm-trf-dualizing-complex-composition`, read on the
  recorded exceptional functor of `d` through the counit-compatible right-adjoint comparison;
* `λ`, the derived direct-image compositor for `i_F` followed by sections over `s`.
`RΓ(T, -)` is the recorded ordinary coefficient complex `Fib_s(Ra_{T*} -)` of
def-weil-ordinary-compact-cohomology.
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

attribute [local instance] vdDiscreteTopology

/-- The topology `vdDiscreteTopology` is discrete.
Source: coefficient convention (blueprint: lem-trf-trace-map-from-external-duality). -/
local instance tmDiscrete (A : Type) [Finite A] : DiscreteTopology A :=
  discreteTopology_bot A

/-- A discrete ring is a topological ring.
Source: coefficient convention (blueprint: lem-trf-trace-map-from-external-duality). -/
local instance tmTopologicalRing (A : Type) [CommRing A] [Finite A] : IsTopologicalRing A :=
  DiscreteTopology.topologicalRing

/-- The characteristic of `k` is the prime `p` of the global datum.
Source: global finite-field datum (blueprint: lem-trf-trace-map-from-external-duality). -/
local instance tmCharPrime (D : FiniteFieldDatum.{u}) : Fact (ringChar D.k).Prime :=
  ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩

/-- Morphisms between separated finite-type `k`-schemes are separated.
Source: standing setting sk-def-sfb-dc-setting
(blueprint: lem-trf-trace-map-from-external-duality). -/
local instance tmSeparated {k : Type u} [Field k] [Fact (ringChar k).Prime]
    {T U : SepFinType k} (f : T ⟶ U) :
    IsSeparated f.hom.left := sfComp_hom_isSeparated k f

/-- Morphisms between separated finite-type `k`-schemes are locally of finite type.
Source: standing setting sk-def-sfb-dc-setting
(blueprint: lem-trf-trace-map-from-external-duality). -/
local instance tmFiniteType {k : Type u} [Field k] [Fact (ringChar k).Prime]
    {T U : SepFinType k} (f : T ⟶ U) :
    LocallyOfFiniteType f.hom.left := sfComp_hom_locallyOfFiniteType k f

/-- Morphisms between separated finite-type `k`-schemes are quasi-compact.
Source: standing setting sk-def-sfb-dc-setting
(blueprint: lem-trf-trace-map-from-external-duality). -/
local instance tmQuasiCompact {k : Type u} [Field k] [Fact (ringChar k).Prime]
    {T U : SepFinType k} (f : T ⟶ U) :
    QuasiCompact f.hom.left := sfComp_hom_quasiCompact k f

/-- The point `s = Spec k`, as the terminal `k`-scheme, is of finite type.
Source: `a_X : X → s` (blueprint: lem-trf-trace-map-from-external-duality). -/
local instance tmBaseFiniteType (k : Type u) [Field k] :
    LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))

/-- The point `s = Spec k` is quasi-compact over itself.
Source: `a_X : X → s` (blueprint: lem-trf-trace-map-from-external-duality). -/
local instance tmBaseQuasiCompact (k : Type u) [Field k] :
    QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))

/-- The point `s = Spec k` is separated over itself.
Source: `a_X : X → s` (blueprint: lem-trf-trace-map-from-external-duality). -/
local instance tmBaseSeparated (k : Type u) [Field k] :
    IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))

variable (A : Type) [CommRing A] [Finite A]
  (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)
  (X : Over (Spec (.of D.k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

include hell in
/-- `ell` is different from the characteristic of `k`.
Source: `ℓ ≠ p` (blueprint: lem-trf-trace-map-from-external-duality).
Proof: `ringChar D.k = D.p` (`ringChar.eq`), and `D.p ≠ ell` is `hell.symm`. -/
theorem tmRingCharNe : ringChar D.k ≠ ell := by
  intro h
  apply hell
  rw [← ringChar.eq D.k D.p, h]

include hA in
/-- The power of `ell` killing `A`, in the form used by the restricted six operations.
Source: `A` annihilated by a power of `ℓ` (blueprint: lem-trf-trace-map-from-external-duality).
Proof: take the exponent of `hA` and forget its positivity. -/
theorem tmKilled : ∃ n : ℕ, ∀ a : A, (ell ^ n) • a = 0 := by
  obtain ⟨n, _hn, h⟩ := hA
  exact ⟨n, h⟩

section Geometry

variable {D}

/-- The structure morphism `a_X : X → s`.
Source: "`a_X : X → s` ... the structure morphisms"
(blueprint: lem-trf-trace-map-from-external-duality). -/
abbrev tmStructure : X ⟶ Over.mk (𝟙 (Spec (.of D.k))) :=
  Over.mkIdTerminal.from X

/-- The diagonal `Δ = Δ_X : X → Z = X ×_s X`.
Source: "put `Z = X ×_s X`, `Δ = Δ_X : X → Z`"
(blueprint: lem-trf-trace-map-from-external-duality). -/
abbrev tmDiagonal : X.left ⟶ (vdProduct X).left :=
  pullback.diagonal X.hom

/-- The ordinary derived pullback `LΔ^*` on the ordinary module-derived categories.
Source: def-weil-pbc-proetale-operations (blueprint: lem-trf-trace-map-from-external-duality). -/
abbrev tmDiagonalPullback : Ambient A (vdProduct X).left ⥤ Ambient A X.left :=
  (upperStar (coefficient A) (tmDiagonal X)).leftDerivedFunctor

/-- The ordinary derived direct image `RΔ_*`.
Source: def-weil-pbc-proetale-operations (blueprint: lem-trf-trace-map-from-external-duality). -/
abbrev tmDiagonalPushforward : Ambient A X.left ⥤ Ambient A (vdProduct X).left :=
  (lowerStar (coefficient A) (tmDiagonal X)).rightDerivedFunctor

/-- The ordinary adjunction `LΔ^* ⊣ RΔ_*`.
Source: "the ordinary adjunction `LΔ^* ⊣ RΔ_*` of [def-weil-pbc-proetale-operations]"
(blueprint: lem-trf-trace-map-from-external-duality). -/
abbrev tmDiagonalAdjunction : tmDiagonalPullback A X ⊣ tmDiagonalPushforward A X :=
  derivedUpperStarLowerStarAdjunction (coefficient A) (tmDiagonal X)

/-- The restriction isomorphism for the first factor, read as an arrow:
`LΔ^* Lp₁^* K → L(p₁Δ)^* K = L(id)^* K → K`, the inverse of the pullback compositor of
lem-weil-pbc-proetale-derived-pullback-composition, then `p₁ Δ = id_X`, then the identity
comparison of derived pullback.
Source: "the inverses of the pullback compositors ... for `p_iΔ = id_X`"
(blueprint: lem-trf-trace-map-from-external-duality). -/
def tmRestrictFst (M : Ambient A X.left) :
    (tmDiagonalPullback A X).obj
        ((upperStar (coefficient A) (vdFst X).left).leftDerivedFunctor.obj M) ⟶ M :=
  (condensedCanonicalPullbackComposition (coefficient A) (tmDiagonal X)
      (vdFst X).left).inv.app M ≫
    eqToHom (congrArg (fun g ↦ (upperStar (coefficient A) g).leftDerivedFunctor.obj M)
      (pullback.diagonal_fst X.hom)) ≫
    (leftDerivedUpperStarId (coefficient A) X.left).hom.app M

/-- The restriction isomorphism for the second factor, read as an arrow:
`LΔ^* Lp₂^* M → L(p₂Δ)^* M = L(id)^* M → M`.
Source: "the inverses of the pullback compositors ... for `p_iΔ = id_X`"
(blueprint: lem-trf-trace-map-from-external-duality). -/
def tmRestrictSnd (M : Ambient A X.left) :
    (tmDiagonalPullback A X).obj
        ((upperStar (coefficient A) (vdSnd X).left).leftDerivedFunctor.obj M) ⟶ M :=
  (condensedCanonicalPullbackComposition (coefficient A) (tmDiagonal X)
      (vdSnd X).left).inv.app M ≫
    eqToHom (congrArg (fun g ↦ (upperStar (coefficient A) g).leftDerivedFunctor.obj M)
      (pullback.diagonal_snd X.hom)) ≫
    (leftDerivedUpperStarId (coefficient A) X.left).hom.app M

end Geometry

/-- The arrow `e' : LΔ^* P → ω_X`, for `P = K ⊠ D_X K`: the restriction isomorphism
`LΔ^* P ≅ K ⊗ D` (the inverse of the native monoidal multiplication of `LΔ^*`, i.e. the
tensor comparison `μ_Δ`, followed by the two restriction isomorphisms), then the signed
symmetry `σ : K ⊗ D → D ⊗ K` (the Koszul braiding of the derived category), then the Verdier
evaluation `ev_K : D ⊗ K → ω_X` of def-trf-dualizing-complex.
Source: "Let `e' : LΔ^*P → ω_X` be the composite of ..."
(blueprint: lem-trf-trace-map-from-external-duality). -/
def tmRestrictedEvaluation (K : Ctf A X.left) :
    (tmDiagonalPullback A X).obj (vdExternalProduct A D ell hell hA X K) ⟶
      dualizingComplex A D ell hell hA X := by
  letI : BraidedCategory (Ambient A X.left) := DerivedCategory.braidedCategory' _
  let f : (tmDiagonalPullback A X).obj
      ((upperStar (coefficient A) (vdFst X).left).leftDerivedFunctor.obj K.obj) ⟶ K.obj :=
    tmRestrictFst A X K.obj
  let g : (tmDiagonalPullback A X).obj
      ((upperStar (coefficient A) (vdSnd X).left).leftDerivedFunctor.obj
        ((verdierDual A D ell hell hA X).obj (op K))) ⟶
      (verdierDual A D ell hell hA X).obj (op K) :=
    tmRestrictSnd A X ((verdierDual A D ell hell hA X).obj (op K))
  exact (Functor.Monoidal.μIso (tmDiagonalPullback A X)
      ((upperStar (coefficient A) (vdFst X).left).leftDerivedFunctor.obj K.obj)
      ((upperStar (coefficient A) (vdSnd X).left).leftDerivedFunctor.obj
        ((verdierDual A D ell hell hA X).obj (op K)))).inv ≫
    MonoidalCategoryStruct.tensorHom (C := Ambient A X.left) f g ≫
    (β_ K.obj ((verdierDual A D ell hell hA X).obj (op K))).hom ≫
    evaluation A D ell hell hA X K

/-- `ω_X` as an object of `D^b_ctf(X, A)` (the recorded constructible dualizing object).
Source: `ω_X = ω_{X,A}` (blueprint: lem-trf-trace-map-from-external-duality). -/
abbrev tmOmega : Ctf A X.left :=
  compositionOmega A D ell hell hA X

section Correspondence

variable {A D ell hell hA X}

end Correspondence

/-- Ordinary derived global sections `RΓ(T, -) = Fib_s(Ra_{T*} -)` of constant-coefficient
module sheaves on the small pro-étale site of a `k`-scheme `T`.
Source: "`RΓ` means ordinary derived global sections of constant-coefficient module sheaves
on the small pro-etale site" (blueprint: lem-trf-trace-map-from-external-duality). -/
abbrev tmSections (T : Over (Spec (.of D.k))) :
    Ambient A T.left ⥤ DerivedCategory (ModuleCat.{u + 1} (MonObj.Γ (coefficient A))) :=
  (lowerStar (coefficient A) T.hom).rightDerivedFunctor ⋙
    (condensedRingCoefficientSections (coefficient A) (Spec (.of D.k))).rightDerivedFunctor

section Correspondence

variable {A D ell hell hA X}

end Correspondence

end WeilConjectures.FiniteRingTrace
