/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.IntegralTraceFormula.IntegralTraceFormula
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralAcyclic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedGraphCorrespondence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCtfSixFunctorStabilityCurrent
public import WeilConjectures.AlgebraicGeometry.CondensedPoincare.FixedSetting.FixedSetting

/-! # Integral models for rational Frobenius correspondences

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-tf-coefficient-transport/sk-lem-tf-rational-model/_section.md
(blueprint: sk-lem-tf-rational-model).

Coefficients. `E ⊆ ℚ̄_ℓ` is a finite subextension of `ℚ_ℓ` (`PadicAlgCl.FiniteIntermediateField`,
the convention of det-def-sf-operations and sk-thm-sfb-rationalization-comparison); the condensed
rings are `𝒪̲_E = Profinite.padicIntegersRingObj ℓ E` and `E̲ = Profinite.continuousMapRingObj E`
with the inclusion `𝒪̲_E ⟶ E̲`; `π_E` is the chosen uniformizer
`Padic.coefficientExtensionUniformizer` of def-weil-l-adic-coefficient-extension.
* `change`: the derived coefficient change `- ⊗ᴸ_{𝒪_E} E` of det-def-sfb-coefficient-change;
* `smul`: multiplication of a morphism of `D(X,E)` by a scalar of `E`, acting through the
  constant global sections of `E_X` (`Mod.linearOfRingHom`);
* `IntegralTraceFormula.scalarCoefficient`: `θ ⊗ᴸ E`, read through the canonical pullback
  coefficient-change isomorphism (reused, not redefined);
* `stalkChange`: the canonical stalk (pullback) coefficient-change isomorphism;
* `condensedGraphOperator`: the graph operator `T_c(v)` of sk-d-operator for `c = (id_X, h)`,
  `h` proper, read with the condensed six operations of det-def-sf-operations: the pullback unit,
  the inverse proper comparison `P₂`, the compositors `μ₂`, `μ₁⁻¹`, the coefficient map
  `u = ι ∘ v` and the exceptional counit, all the recorded maps of
  lem-trf-condensed-graph-correspondence-base-change (`CondensedGraphCorrespondence`);
* `exists_integralModel`: the lemma, with Frobenius correspondences, iterates and stalk
  endomorphisms those of sk-d-weil (`TraceWeilComplex`); the compact-support identity is read
  through the canonical compact-support comparison `scalarCompactSupportMap`
  (det-prop-scalar-six-compact-support) for the chosen compactification of `a_X`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures.TraceWeilComplex WeilConjectures.TraceCoefficientMorphismFormula

namespace WeilConjectures.TraceRationalModel

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- The integral condensed coefficient ring `𝒪̲_E`.
Source: "the pulled-back condensed coefficients `Λ ∈ {𝒪_E, E}`"
(blueprint: sk-lem-tf-rational-model). -/
abbrev integral : CondensedRing.ScalarSixRing.{u} :=
  ⟨Profinite.padicIntegersRingObj.{u} ℓ E.1⟩

/-- The rational condensed coefficient ring `E̲`.
Source: "the pulled-back condensed coefficients `Λ ∈ {𝒪_E, E}`"
(blueprint: sk-lem-tf-rational-model). -/
abbrev rational : CondensedRing.ScalarSixRing.{u} :=
  ⟨Profinite.continuousMapRingObj.{u} E.1⟩

/-- `𝒪̲_E` as a condensed ring (monoid object), the form taken by the free-parameter scalar maps.
Source: "the pulled-back condensed coefficients `Λ ∈ {𝒪_E, E}`"
(blueprint: sk-lem-tf-rational-model). -/
abbrev integralMon : Profinite.CondensedRing.{u} :=
  Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E.1)

/-- `E̲` as a condensed ring (monoid object).
Source: "the pulled-back condensed coefficients `Λ ∈ {𝒪_E, E}`"
(blueprint: sk-lem-tf-rational-model). -/
abbrev rationalMon : Profinite.CondensedRing.{u} :=
  Mon.mk (Profinite.continuousMapRingObj.{u} E.1)

/-- The coefficient map `𝒪̲_E ⟶ E̲`.
Source: "the derived coefficient change `- ⊗ᴸ_{𝒪_E} E`" (blueprint: sk-lem-tf-rational-model). -/
abbrev inclusion : (integral.{u} ℓ E).X ⟶ (rational.{u} ℓ E).X :=
  padicIntegersRingObjToContinuousMapRingObj.{u} ℓ E

/-- The coefficient map `𝒪_E → E` as a morphism of commutative condensed rings.
Source: "the derived coefficient change `- ⊗ᴸ_{𝒪_E} E`" (blueprint: sk-lem-tf-rational-model). -/
abbrev coefficientInclusion : integral.{u} ℓ E ⟶ rational.{u} ℓ E :=
  CommMon.homMk (Mon.Hom.mk (inclusion.{u} ℓ E))

/-- The derived coefficient change `K ↦ K ⊗ᴸ_{𝒪_E} E = L(Ext_{a_X})K` on `X`
(det-def-sfb-coefficient-change).
Source: "the derived coefficient change `- ⊗ᴸ_{𝒪_E} E` of [det-def-sfb-coefficient-change]"
(blueprint: sk-lem-tf-rational-model). -/
abbrev change (X : Scheme.{u}) :
    TraceOperations.D (integral.{u} ℓ E).X X ⥤ TraceOperations.D (rational.{u} ℓ E).X X :=
  CondensedRing.scalarSixChange (coefficientInclusion.{u} ℓ E) X

/-- The chosen uniformizer `π_E ∈ E` of def-weil-l-adic-coefficient-extension.
Source: "a finite extension `E/ℚ_ℓ` with valuation ring `𝒪_E` and uniformizer `π_E`"
(blueprint: sk-lem-tf-rational-model). -/
abbrev uniformizer : E.1 :=
  (Padic.coefficientExtensionUniformizer ℓ E.1 : E.1)

/-- The constant scalars `E → Γ(X, E_X)`: constant global sections of `E̲`, pulled back along
`p_X`.
Source: "`ψ_E = π_E^{-N}(θ ⊗ᴸ E)`", scalar multiplication by `π_E^{-N} ∈ E`
(blueprint: sk-lem-tf-rational-model). -/
def scalarRingHom (X : Scheme.{u}) :
    E.1 →+* MonObj.Γ (condensedRingObj (rational.{u} ℓ E).X X) :=
  (MonObj.Γ.mapFunctor (upperStarFromPoint X)).comp
    (Profinite.continuousMapConstRingHom.{u} E.1)

/-- Multiplication of a morphism of `D(X,E)` by a scalar `a ∈ E`, for the `E`-linear structure
of `E_X`-modules given by the constant sections (`Mod.linearOfRingHom`) and its derived
category.
Source: "`ψ_E = π_E^{-N}(θ ⊗ᴸ E)`" and "`π_E^{-Nm}(…)`" in (13.2)
(blueprint: sk-lem-tf-rational-model). -/
def smul {X : Scheme.{u}} {K L : TraceOperations.D (rational.{u} ℓ E).X X} (a : E.1)
    (f : K ⟶ L) : K ⟶ L :=
  letI := Mod.linearOfRingHom (scalarRingHom ℓ E X)
  a • f

/-- The canonical pullback (stalk) coefficient-change isomorphism
`(f^*K₀) ⊗ᴸ E ≃ f^*(K₀ ⊗ᴸ E)`: the free-parameter scalar/pullback comparison, between the
total left derived pullbacks through their identifications with the termwise ones.
Source: "the rationalized arrows are read through `e` and the canonical pullback,
compact-support and stalk coefficient-change isomorphisms" (blueprint: sk-lem-tf-rational-model). -/
def stalkChange {Y X : Scheme.{u}} (f : Y ⟶ X)
    (K₀ : TraceOperations.D (integral.{u} ℓ E).X X) :
    (change ℓ E Y).obj ((TraceOperations.star (integral.{u} ℓ E).X f).obj K₀) ≅
      (TraceOperations.star (rational.{u} ℓ E).X f).obj ((change ℓ E X).obj K₀) :=
  letI := FreeParameterEvaluation.scalarPullComparison_isIso (integralMon.{u} ℓ E)
    (rationalMon.{u} ℓ E) (inclusion.{u} ℓ E) f K₀
  (change ℓ E Y).mapIso
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (integral.{u} ℓ E).X f).app K₀) ≪≫
    asIso (FreeParameterEvaluation.scalarPullComparison (integralMon.{u} ℓ E)
      (rationalMon.{u} ℓ E)
      (inclusion.{u} ℓ E) f K₀) ≪≫
    ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (rational.{u} ℓ E).X f).app
      ((change ℓ E X).obj K₀)).symm

section CondensedOperator

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (hk : Finite k ∨ IsAlgClosed k) (Λ : CondensedRing.ScalarSixRing.{u})
  (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ.X)
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- `Lh^*K` as a bounded constructible finite-Tor object (pullback stability of
sk-thm-sf-ctf-stability, `condensedCtfSixFunctorStabilityCurrent`).
Source: "the six operations for these coefficients of [det-def-sf-operations]"
(blueprint: sk-lem-tf-rational-model). -/
def pullbackCtf (h : X ⟶ X) (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    ConstantModelConstructibleFiniteTor Λ.X X.left :=
  ⟨(TraceOperations.star Λ.X h.left).obj K.obj,
    (CondensedRing.condensedCtfSixFunctorStabilityCurrent Λ.X ℓ k hk h hΛ).1 K⟩

/-- The graph operator `T_c(v) : RΓ_c(X,K) → RΓ_c(X,K)` of sk-d-operator for the graph
endocorrespondence `c = (id_X, h)` of a proper `k`-endomorphism `h` with coefficient map
`u = ι_{X,K} ∘ v` (`condensedGraphCoefficient`), read with the condensed six operations of
det-def-sf-operations: `Ra_{X!}` of the unit of `h^* ⊣ Rh_*`, `Ra_{X!}` of the inverse proper
comparison `P₂`, the compositor `μ₂`, `R(a_X h)_!` of `u`, the inverse compositor `μ₁`, and
`Ra_{X!}` of the exceptional counit of `R(id_X)_! ⊣ R(id_X)^!`. `RΓ_c` is the chosen
compactification functor of `a_X`.
Source: "graph operators `T_{c_m}` … are given by the formulas of [sk-d-weil, sk-d-operator]
read with the six operations for these coefficients of [det-def-sf-operations]"
(blueprint: sk-lem-tf-rational-model); displayed composite of sk-d-operator. -/
def condensedGraphOperator (h : X ⟶ X) [IsProper h.left]
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left)
    (v : (TraceOperations.star Λ.X h.left).obj K.obj ⟶ K.obj) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ.X
        (CondensedRing.condensedGraphStructureCompactification X)).obj K.obj ⟶
      (CondensedRing.rightDerivedLowerShriekOfCompactification Λ.X
        (CondensedRing.condensedGraphStructureCompactification X)).obj K.obj :=
  let L := pullbackCtf ℓ k hk Λ hΛ X h K
  let G := CondensedRing.rightDerivedLowerShriekOfCompactification Λ.X
    (CondensedRing.condensedGraphStructureCompactification X)
  let P := CondensedRing.condensedGraphProperComparison ℓ k hk Λ hΛ X h L
  haveI : IsIso P := by
    dsimp only [P, CondensedRing.condensedGraphProperComparison]
    infer_instance
  let J := CondensedRing.ctfExceptionalInverseImage Λ.X ℓ k
    (WeilConjectures.exceptionalCurrentFieldCD ℓ k hk) (𝟙 X) hΛ
  G.map ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ.X h.left).unit.app K.obj) ≫
    G.map (inv P) ≫
    (CondensedRing.condensedGraphCompositionComparison ℓ k hk Λ hΛ X h).hom.app
      (CondensedRing.condensedGraphLocalizing Λ L) ≫
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ.X
        (CondensedRing.condensedGraphCompositeCompactification X h)).map
      (CondensedRing.condensedGraphCoefficient ℓ k hk Λ hΛ X h K v) ≫
    (CondensedRing.condensedGraphCompositionComparison ℓ k hk Λ hΛ X (𝟙 X)).inv.app
      (CondensedRing.condensedGraphLocalizing Λ (J.obj K)) ≫
    G.map ((CondensedRing.ctfExceptionalAdjunction Λ.X ℓ k
      (WeilConjectures.exceptionalCurrentFieldCD ℓ k hk) (𝟙 X) hΛ).counit.app K).hom

end CondensedOperator

variable (D : FiniteFieldDatum.{u})

/-- The geometric fibre of a finite-type model is locally of finite type over `k`.
Source: "put `X=X_0×_{F_q}k`" (blueprint: sk-lem-tf-rational-model).
Proof: base change of a locally finite-type morphism. -/
theorem geometricFiber_locallyOfFiniteType (T : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] :
    LocallyOfFiniteType (D.geometricFiber T).hom := by
  dsimp [FiniteFieldDatum.geometricFiber]
  infer_instance

/-- The geometric fibre of a quasi-compact model is quasi-compact over `k`.
Source: "put `X=X_0×_{F_q}k`" (blueprint: sk-lem-tf-rational-model).
Proof: base change of a quasi-compact morphism. -/
theorem geometricFiber_quasiCompact (T : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] :
    QuasiCompact (D.geometricFiber T).hom := by
  dsimp [FiniteFieldDatum.geometricFiber]
  infer_instance

/-- The geometric fibre of a separated model is separated over `k`.
Source: "`X_0/F_q` separated and of finite type, `X=X_0×_{F_q}k`"
(blueprint: sk-lem-tf-rational-model).
Proof: base change of a separated morphism. -/
theorem geometricFiber_isSeparated (T : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom] :
    IsSeparated (D.geometricFiber T).hom := by
  dsimp [FiniteFieldDatum.geometricFiber]
  infer_instance

attribute [local instance] geometricFiber_locallyOfFiniteType geometricFiber_quasiCompact
  geometricFiber_isSeparated

end WeilConjectures.TraceRationalModel
