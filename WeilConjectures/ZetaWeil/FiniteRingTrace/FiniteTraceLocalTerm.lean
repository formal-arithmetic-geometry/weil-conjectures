/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.FiniteRingTrace.FiniteTraceClass
public import WeilConjectures.TraceFormula.TraceFormulaIntegrationNative
public import WeilConjectures.SmoothPurity.TraceFixedScheme
public import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.AlgebraicGeometry.ZeroDimIntegralPoint
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback

/-! # Local terms of a correspondence, arbitrary finite coefficients

Source: literature/blueprint/master/blueprint/sec-trace-formula/sk-d-pairing/
def-trf-local-term.md (blueprint: def-trf-local-term), with the refinements recorded in the
DAG node (the singleton `{x̄}` open and closed, `m ≥ 1`, `E_coeff` renamed).

The coefficient ring `A` is an arbitrary finite commutative ring killed by a positive power of
`ell`, with its discrete topology, exactly as in the trace class `verdierTraceClass` of
def-trf-trace-class below this module. Every arrow is a specified construction:
* `A_B → Lj_B^* A_E`: the inverse of the constant-coefficient pullback isomorphism
  `leftDerivedUpperStarUnitIso` (derived pullback of the coefficient unit);
* `Lj_B^* σ`: the ordinary derived pullback of the open immersion `j_B`;
* `Lj_B^* ω_E ≅ Rj_B^! ω_E`: purity for the open immersion `j_B` in relative dimension `0`,
  realized as the unique right-adjoint comparison (`Adjunction.rightAdjointUniq`) between the
  specified constructible exceptional adjunction of `j_B` and the extension-by-zero adjunction
  `Dj_! ⊣ Lj^*` restricted to the constructible finite-Tor subcategories; its left comparison is
  the normalized compact-support comparison to the open compactification `(j_B, id_E)`;
* `Rj_B^! ω_E ≅ ω_B`: `dualizingComposition` of thm-trf-dualizing-complex-composition at `j_B`;
* `∫_B`: the integration composite of def-trf-integration, read as a scalar of `A`.
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

attribute [local instance] vdDiscreteTopology tmDiscrete tmTopologicalRing tmCharPrime

section Geometry

variable {D : FiniteFieldDatum.{u}} (E : Over (Spec (.of D.k)))
  [LocallyOfFiniteType E.hom] [QuasiCompact E.hom] [IsSeparated E.hom]
  (U : E.left.Opens)

/-- The open-and-closed subscheme `B` of `E`: the open subscheme on the open subset `U`, as a
`k`-scheme through `E`. Clopenness of `U` is the instance `Fact (IsClopen (U : Set E.left))`.
Source: "`B` is the open subscheme on a subset of `E` that is both open and closed
[def-weil-open-immersion]" (blueprint: def-trf-local-term). -/
abbrev clopenPiece : Over (Spec (.of D.k)) :=
  Over.mk (U.ι ≫ E.hom)

/-- The inclusion `j_B : B ↪ E` of the open-and-closed subscheme, over `k`.
Source: "let `j_B : B ↪ E` be the inclusion of an open-and-closed subscheme"
(blueprint: def-trf-local-term). -/
abbrev clopenInclusion : clopenPiece E U ⟶ E :=
  Over.homMk U.ι rfl

/-- `j_B` is an open immersion.
Source: def-weil-open-immersion (blueprint: def-trf-local-term). -/
instance clopenInclusion_isOpenImmersion : IsOpenImmersion (clopenInclusion E U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

set_option linter.unusedSectionVars false in
-- Retain the published signature, including its existing instance assumptions.
/-- The inclusion of a closed open subset of the quasi-compact `E` is quasi-compact.
Source: def-weil-scheme-morphism-properties (blueprint: def-trf-local-term).
Proof: `U` is closed in `E`, and `E` is quasi-compact since `E → Spec k` is quasi-compact over
an affine; hence `U` is a compact space. A morphism from a compact scheme to the
quasi-separated scheme `E` (separated over a field) is quasi-compact. -/
theorem clopen_ι_quasiCompact [Fact (IsClopen (U : Set E.left))] : QuasiCompact U.ι := by
  let : IsClosedImmersion U.ι :=
    .of_isPreimmersion _ (U.range_ι ▸ (Fact.out : IsClopen (U : Set E.left)).isClosed)
  infer_instance

attribute [local instance] clopen_ι_quasiCompact

/-- The structure morphism of `B` is locally of finite type (open immersion followed by `a_E`).
Source: def-weil-scheme-morphism-properties (blueprint: def-trf-local-term). -/
instance clopenPiece_locallyOfFiniteType : LocallyOfFiniteType (clopenPiece E U).hom :=
  inferInstanceAs (LocallyOfFiniteType (U.ι ≫ E.hom))

/-- The structure morphism of `B` is separated (a monomorphism followed by `a_E`).
Source: def-weil-scheme-morphism-properties (blueprint: def-trf-local-term). -/
instance clopenPiece_isSeparated : IsSeparated (clopenPiece E U).hom :=
  inferInstanceAs (IsSeparated (U.ι ≫ E.hom))

/-- The structure morphism of `B` is quasi-compact, since `U` is closed.
Source: def-weil-scheme-morphism-properties (blueprint: def-trf-local-term). -/
instance clopenPiece_quasiCompact [Fact (IsClopen (U : Set E.left))] :
    QuasiCompact (clopenPiece E U).hom :=
  inferInstanceAs (QuasiCompact (U.ι ≫ E.hom))

end Geometry

variable (A : Type) [CommRing A] [Finite A]
  (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (hA : ∃ n : ℕ, 0 < n ∧ ∀ a : A, (ell ^ n) • a = 0)

section Restriction

variable {D} (E : Over (Spec (.of D.k)))
  [LocallyOfFiniteType E.hom] [QuasiCompact E.hom] [IsSeparated E.hom]
  (U : E.left.Opens) [Fact (IsClopen (U : Set E.left))]

/-- The ordinary derived pullback `Lj_B^*` of the open immersion `j_B`.
Source: def-weil-derived-pullback-tensor-hom (blueprint: def-trf-local-term). -/
abbrev clopenPullback : Ambient A E.left ⥤ Ambient A (clopenPiece E U).left :=
  (upperStar (coefficient A) (clopenInclusion E U).left).leftDerivedFunctor

set_option linter.unusedSectionVars false in
-- Retain the published signature, including its existing instance assumptions.
/-- `Lj_B^*` preserves bounded constructible complexes of finite Tor amplitude.
Source: prop-functor-package, pullback stability (blueprint: def-trf-local-term).
Proof: derived pullback is t-exact and monoidal, so it preserves boundedness and finite Tor
amplitude; it preserves constant-model constructibility by restricting a stratification
(`traceFormulaPullbackPreserves`, def-trf-admissibility, at `j_B`). -/
theorem clopenPullback_mem (K : Ctf A E.left) :
    (constantModelBoundedConstructible (coefficient A) (clopenPiece E U).left ⊓
      DerivedCategory.finiteTorAmplitude _) ((clopenPullback A E U).obj K.obj) := by
  let : CompactSpace E.left := QuasiCompact.compactSpace_of_compactSpace E.hom
  let : QuasiSeparatedSpace E.left := quasiSeparatedSpace_of_quasiSeparated E.hom
  let : CompactSpace (clopenPiece E U).left :=
    QuasiCompact.compactSpace_of_compactSpace (clopenPiece E U).hom
  let : QuasiSeparatedSpace (clopenPiece E U).left :=
    quasiSeparatedSpace_of_quasiSeparated (clopenPiece E U).hom
  exact ⟨pullback_bounded_constructible (coefficient A) (clopenInclusion E U).left
    (fun M hM ↦ pullback_constructible (coefficient A) (clopenInclusion E U).left M hM)
    K.obj K.property.1,
    pullback_tor (coefficient A) (clopenInclusion E U).left K.obj K.property.2⟩

/-- `Lj_B^*` on the constructible finite-Tor subcategories.
Source: prop-functor-package, item (6), the functor `Lj^*` (blueprint: def-trf-local-term). -/
def clopenCtfPullback : Ctf A E.left ⥤ Ctf A (clopenPiece E U).left :=
  ObjectProperty.lift _
    ((constantModelBoundedConstructible (coefficient A) E.left ⊓
      DerivedCategory.finiteTorAmplitude _).ι ⋙ clopenPullback A E U)
    (clopenPullback_mem A E U)

/-- The extension-by-zero adjunction `Dj_! ⊣ Lj^*` of the open immersion `j_B`, with the derived
pullback as right adjoint (the same transport as in `CompactSupportComposition.openExchange`).
Source: prop-functor-package, item (6); def-sfb-dc-open-lower-shriek-adjunction
(blueprint: def-trf-local-term). -/
def clopenOpenAdjunction :
    D(((clopenInclusion E U).left)_!open⟦coefficient A⟧) ⊣ clopenPullback A E U :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction (coefficient A)
      (clopenInclusion E U).left).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory (coefficient A) (clopenInclusion E U).left).symm

/-- The compact-support functor of the open compactification `(j_B, id_E)` is extension by zero:
`R(id_E)_* ∘ Dj_! ≅ Dj_!`, using the identity normalization of `R(id)_*` (the conjugate of the
identity comparison of derived pullback, as in `CompactSupportComposition.identity`).
Source: sk-thm-sf-comp-composition, identity normalization (blueprint: def-trf-local-term). -/
def clopenOpenCompactSupport :
    rightDerivedLowerShriekOfCompactification (coefficient A)
        (Compactification.ofIsOpenImmersion (clopenInclusion E U).left) ≅
      D(((clopenInclusion E U).left)_!open⟦coefficient A⟧) :=
  Functor.isoWhiskerLeft _
      (conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction (coefficient A) (𝟙 E.left))
        Adjunction.id (leftDerivedUpperStarId (coefficient A) E.left).symm) ≪≫
    Functor.rightUnitor _

/-- The left comparison: the specified constructible compact-support functor of `j_B`
(`compositionData`, at the chosen compactification over the field) agrees on constructible
finite-Tor objects with extension by zero, through the normalized compact-support comparison
to the open compactification `(j_B, id_E)`.
Source: sk-thm-sf-comp-composition (1), canonicity of the comparisons
(blueprint: def-trf-local-term). -/
def clopenSupportComparison :
    (constantModelBoundedConstructible (coefficient A) (clopenPiece E U).left ⊓
        DerivedCategory.finiteTorAmplitude _).ι ⋙
      D(((clopenInclusion E U).left)_!open⟦coefficient A⟧) ≅
    (compositionData A D ell hell hA (clopenInclusion E U)).lower ⋙
      (constantModelBoundedConstructible (coefficient A) E.left ⊓
        DerivedCategory.finiteTorAmplitude _).ι := by
  let h := compositionCoherence A D ell hell hA
  let i : Ctf A (clopenPiece E U).left ⥤
      (localizingClosureProEtale (coefficient A) (clopenPiece E U).left).FullSubcategory :=
    ObjectProperty.ιOfLE (fun K hK P _ hP ↦ hP K hK)
  exact (eqToIso (compositionData A D ell hell hA (clopenInclusion E U)).lower_eq ≪≫
    Functor.isoWhiskerLeft i
      (h.comparison (SepFinType.homMk (clopenInclusion E U))
        (compactificationOverField (clopenInclusion E U))
        (Compactification.ofIsOpenImmersion (clopenInclusion E U).left)) ≪≫
    Functor.isoWhiskerLeft
      (constantModelBoundedConstructible (coefficient A) (clopenPiece E U).left ⊓
        DerivedCategory.finiteTorAmplitude _).ι
      (clopenOpenCompactSupport A E U)).symm

/-- The adjunction `Rj_! ⊣ Lj^*` on the constructible finite-Tor subcategories, restricted from
`Dj_! ⊣ Lj^*` through the full inclusions; its left functor is the specified constructible
compact-support functor of `j_B`.
Source: prop-functor-package, item (6) (blueprint: def-trf-local-term). -/
def clopenCtfAdjunction :
    (compositionData A D ell hell hA (clopenInclusion E U)).lower ⊣ clopenCtfPullback A E U :=
  (clopenOpenAdjunction A E U).restrictFullyFaithful
    (constantModelBoundedConstructible (coefficient A) (clopenPiece E U).left ⊓
      DerivedCategory.finiteTorAmplitude _).fullyFaithfulι
    (constantModelBoundedConstructible (coefficient A) E.left ⊓
      DerivedCategory.finiteTorAmplitude _).fullyFaithfulι
    (clopenSupportComparison A ell hell hA E U) (Iso.refl _)

/-- Purity for the open immersion `j_B` in relative dimension `0`: `Rj_B^! ≅ Lj_B^*` on
constructible finite-Tor objects, the unique comparison of the two right adjoints of the same
compact-support functor (so it is compatible with both counits; no choice is made).
Source: "the equality `Rj_B^! ≅ Lj_B^*` for the open immersion `j_B` (the purity clause of the
six-operations package [prop-functor-package], item (6), in relative dimension `0`)"
(blueprint: def-trf-local-term). -/
def clopenPurity :
    (compositionData A D ell hell hA (clopenInclusion E U)).right ≅ clopenCtfPullback A E U :=
  (compositionData A D ell hell hA (clopenInclusion E U)).adjunction.rightAdjointUniq
    (clopenCtfAdjunction A ell hell hA E U)

/-- The canonical identification `Lj_B^* ω_{E,A} ≅ Rj_B^! ω_{E,A} ≅ ω_{B,A}`: the inverse of
purity at `ω_E`, followed by the composition isomorphism of
thm-trf-dualizing-complex-composition (`dualizingComposition`) applied to `j_B`.
Source: "the last arrow being the canonical identification
`Lj_B^*ω_{E,A} ≅ Rj_B^!ω_{E,A} ≅ ω_{B,A}`" (blueprint: def-trf-local-term). -/
def clopenDualizingRestriction :
    (clopenPullback A E U).obj (dualizingComplex A D ell hell hA E) ≅
      dualizingComplex A D ell hell hA (clopenPiece E U) :=
  (constantModelBoundedConstructible (coefficient A) (clopenPiece E U).left ⊓
      DerivedCategory.finiteTorAmplitude _).ι.mapIso
    ((clopenPurity A ell hell hA E U).symm.app (compositionOmega A D ell hell hA E) ≪≫
      dualizingComposition A D ell hell hA (clopenInclusion E U))

/-- The restriction `j_B^* σ : A_B ≅ Lj_B^* A_E → Lj_B^* ω_{E,A} → ω_{B,A}` of a section
`σ : A_E → ω_{E,A}`: the inverse of the constant-coefficient pullback isomorphism, the derived
pullback of `σ`, and the canonical identification `clopenDualizingRestriction`.
It is defined for every open-and-closed `B`, whether or not `B` or `E` is proper.
Source: "The *restriction* of `σ` to `B` is `j_B^*σ`", first display
(blueprint: def-trf-local-term). -/
def restrictSection (σ : 𝟙_ (Ambient A E.left) ⟶ dualizingComplex A D ell hell hA E) :
    𝟙_ (Ambient A (clopenPiece E U).left) ⟶ dualizingComplex A D ell hell hA (clopenPiece E U) :=
  (leftDerivedUpperStarUnitIso (coefficient A) (clopenInclusion E U).left).inv ≫
    (clopenPullback A E U).map σ ≫ (clopenDualizingRestriction A ell hell hA E U).hom

/-- The integral `∫_Y τ ∈ A` of def-trf-integration of a section `τ : A_Y → ω_{Y,A}` over a
proper `Y`: the scalar of the specified unit/proper-comparison/`Ra_!τ`/counit composite. At
`A = A_{E,n}` this is literally `traceFormulaIntegration` (see
`localTermOfSection_coefficientExtensionRing`).
Source: "the integral of [def-trf-integration]" (blueprint: def-trf-local-term). -/
abbrev sectionIntegral (Y : Over (Spec (.of D.k))) [IsProper Y.hom]
    (τ : 𝟙_ (Ambient A Y.left) ⟶ dualizingComplex A D ell hell hA Y) : A :=
  traceFormulaIntegrationScalar A D (traceFormulaIntegrationEndomorphism A D ell hell hA Y τ)

/-- The local term `LT_B(σ) := ∫_B j_B^* σ ∈ A` of a section on an open-and-closed `B` proper
over `s`; the ambient `E` need not be proper.
Source: "If moreover `B` is proper over `s`, the *local term* of `σ` on `B` is
`LT_B(σ) := ∫_B j_B^*σ ∈ A`" (blueprint: def-trf-local-term). -/
def localTermOfSection [IsProper (clopenPiece E U).hom]
    (σ : 𝟙_ (Ambient A E.left) ⟶ dualizingComplex A D ell hell hA E) : A :=
  sectionIntegral A ell hell hA (clopenPiece E U) (restrictSection A ell hell hA E U σ)

end Restriction

/-- At the coefficient ring `A = A_{E_coeff,n}` of def-trf-coefficient-conventions the local term
is the integral `traceFormulaIntegration` of def-trf-integration applied to the restriction.
Source: def-trf-local-term with `A = A_{E_coeff,n}` (blueprint: def-trf-local-term).
Proof: `traceFormulaIntegration` at `A_{E,n}` unfolds to `traceFormulaIntegrationScalar` of
`traceFormulaIntegrationEndomorphism` with the same primary witness; both sides agree by
definitional unfolding (`rfl`). -/
theorem localTermOfSection_coefficientExtensionRing
    (Ec : IntermediateField (Padic ell) (PadicAlgCl ell)) [FiniteDimensional (Padic ell) Ec]
    (n : ℕ) (hn : 1 ≤ n) [Finite (Padic.coefficientExtensionRing ell Ec n)]
    (E : Over (Spec (.of D.k)))
    [LocallyOfFiniteType E.hom] [QuasiCompact E.hom] [IsSeparated E.hom]
    (U : E.left.Opens) [Fact (IsClopen (U : Set E.left))] [IsProper (clopenPiece E U).hom]
    (σ : 𝟙_ (Ambient (Padic.coefficientExtensionRing ell Ec n) E.left) ⟶
      dualizingComplex (Padic.coefficientExtensionRing ell Ec n) D ell hell
        (coefficientExtensionRing_primary ell Ec n hn) E) :
    localTermOfSection (Padic.coefficientExtensionRing ell Ec n) ell hell
        (coefficientExtensionRing_primary ell Ec n hn) E U σ =
      traceFormulaIntegration D ell hell Ec n hn (clopenPiece E U)
        (restrictSection (Padic.coefficientExtensionRing ell Ec n) ell hell
          (coefficientExtensionRing_primary ell Ec n hn) E U σ) := by
  rfl

section Correspondence

variable {A D ell hell hA} {X : Over (Spec (.of D.k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- A connected component `β ∈ π₀(F)` of a fixed scheme with finitely many clopen components
(the convention `HasFiniteClopenConnectedComponents` of def-trf-fixed-scheme) is open and closed.
Source: "each `β` is open-and-closed in `F`" (blueprint: def-trf-local-term). -/
instance componentOpen_clopen {F : Scheme.{u}} (hF : F.HasFiniteClopenConnectedComponents)
    (β : _root_.ConnectedComponents F) :
    Fact (IsClopen (F.clopenConnectedComponentOpen hF β : Set F)) :=
  ⟨hF.2 β⟩

set_option linter.overlappingInstances false in
-- Retain the published signature, including its existing instance assumptions.
/-- Each component of a proper `F` is proper over `s`: a clopen immersion is a closed
immersion, hence proper, and a composite of proper morphisms is proper.
Source: "each `β` is open-and-closed in `F` and proper over `s`
[lem-weil-pbc-closed-immersion-proper]" (blueprint: def-trf-local-term).
Proof: the open immersion of the closed subset `β` is a closed immersion
(lem-weil-pbc-closed-immersion-proper (a)); closed immersions are proper and properness is
stable under composition with `a_F` (lem-weil-pbc-closed-immersion-proper (c)). -/
theorem componentPiece_isProper (F : Over (Spec (.of D.k)))
    [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom] [IsProper F.hom]
    (hF : F.left.HasFiniteClopenConnectedComponents) (β : _root_.ConnectedComponents F.left) :
    IsProper (clopenPiece F (F.left.clopenConnectedComponentOpen hF β)).hom := by
  let U := F.left.clopenConnectedComponentOpen hF β
  let : IsClosedImmersion U.ι := .of_isPreimmersion _ (U.range_ι ▸ (hF.2 β).isClosed)
  exact inferInstanceAs (IsProper (U.ι ≫ F.hom))

attribute [local instance] componentPiece_isProper

end Correspondence

section Point

variable {D}

/-- The open subset `{x̄}` of a scheme in which the singleton is open and closed.
Source: "If `x̄` is a point of `F` such that `{x̄}` is open and closed in `F`"
(blueprint: def-trf-local-term). -/
def pointOpen {F : Scheme.{u}} (x : F) (hx : IsClopen ({x} : Set F)) : F.Opens :=
  ⟨{x}, hx.isOpen⟩

/-- The point open is open and closed.
Source: "`{x̄}` is open and closed in `F`" (blueprint: def-trf-local-term). -/
instance pointOpen_clopen {F : Scheme.{u}} (x : F) (hx : IsClopen ({x} : Set F)) :
    Fact (IsClopen (pointOpen x hx : Set F)) :=
  ⟨hx⟩

/-- A reduced open-and-closed point component `B_x̄` is proper over `s`: it is nonempty,
reduced and irreducible, hence integral [def-pc-integral-scheme], of dimension `0`
[def-kun-topological-krull-dimension], and of finite type over the algebraically closed `k`, so
its structure morphism is an isomorphism `B_x̄ ≅ Spec k`.
Source: "Thus its structure morphism is an isomorphism `B_x̄ ≃ Spec k` by
[lem-weil-pbc-zero-dim-integral-point] ... so `B_x̄` is proper over `s`"
(blueprint: def-trf-local-term).
Proof: `B_x̄` has one point, so it is irreducible; with `IsReduced` it is integral. Its
topological Krull dimension is `0`. `isIso_structure_of_integral_zero_dim`
(lem-weil-pbc-zero-dim-integral-point) gives `IsIso`, and isomorphisms are proper. -/
theorem pointPiece_isProper (F : Over (Spec (.of D.k)))
    [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
    (x : F.left) (hx : IsClopen ({x} : Set F.left)) [IsReduced (pointOpen x hx).toScheme] :
    IsProper (clopenPiece F (pointOpen x hx)).hom := by
  let U := pointOpen x hx
  let : Subsingleton U.toScheme := ⟨fun a b ↦ Subtype.ext (a.property.trans b.property.symm)⟩
  let : Nonempty U.toScheme := ⟨⟨x, rfl⟩⟩
  let : IrreducibleSpace U.toScheme := { toNonempty := inferInstance }
  let : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  let : U.toScheme.Over (Spec (.of D.k)) := ⟨U.ι ≫ F.hom⟩
  let : LocallyOfFiniteType (U.toScheme ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ F.hom))
  let : QuasiCompact (U.toScheme ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (U.ι ≫ F.hom))
  have hi : IsIso (U.ι ≫ F.hom) :=
    isIso_structure_of_integral_zero_dim U.toScheme (by
      apply le_antisymm (topologicalKrullDim_zero_of_discreteTopology _)
      let : Nonempty (TopologicalSpace.IrreducibleCloseds U.toScheme) :=
        ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩⟩
      exact Order.krullDim_nonneg)
  exact inferInstanceAs (IsProper (U.ι ≫ F.hom))

attribute [local instance] pointPiece_isProper

variable {A ell hell hA} {X : Over (Spec (.of D.k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

end Point

end WeilConjectures.FiniteRingTrace
