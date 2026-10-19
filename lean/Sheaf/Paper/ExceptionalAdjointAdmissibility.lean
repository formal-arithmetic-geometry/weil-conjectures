/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.Paper.ConstructibleIntervalsUnordered
public import Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import Sheaf.Paper.IntegralScalarExtensionWellDefined
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.LinearAlgebra.Dimension.Free

import Sheaf.Paper.BoundedConstructibleTower
import Sheaf.Paper.SupportCoefficientByProjection

/-!
# Exceptional-adjoint admissibility as optional ambient data

Source: Weil blueprint, order 1474 (blueprint: def-weil-exceptional-adjoint-admissibility).
Coefficient extension and the support comparison are constructed from scalar restriction.
Ambient exceptional adjoints, refinement coherence, preservation bounds, and invertibility
of the resulting right-adjoint coefficient mates are conditions of the datum.
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- The two preservation clauses for one actual ambient right adjoint, at fixed signed
bounds. Reversed output endpoints denote the zero subcategory through Set.Icc.
Source: Weil blueprint, order 1474, clauses (2) and (3)
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable def ExceptionalAdjointPreserves (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}}
    (G : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n) ⥤
      proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)) (cMinus cPlus : ℤ) :
    Prop :=
  (∀ (a b : ℤ), a ≤ b → ∀ L,
    constructibleInterval l E n hn Y a b L →
      constructibleInterval l E n hn X (a + cMinus) (b + cPlus) (G.obj L)) ∧
  ∀ L, finiteTorConstructible l E n hn Y L → finiteTorConstructible l E n hn X (G.obj L)

/-- Exceptional-adjoint admissibility at A_(E,n), relative to the chosen compactification.
FullCD is on all pro-etale module sheaves. The natural Hom bijections are adj; all
refinement coherence is datum, and the amplitude endpoints are independent signed integers.
Source: Weil blueprint, order 1474 (blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable def IsExceptionalAdjointAdmissibleAtFiniteStage
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (_hS : ∀ s : S, IsUnit (l : S.presheaf.stalk s))
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Prop :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  ∃ (D : SfAmbientExceptionalRightAdjointDatum (Padic.coefficientExtensionRing l E n) f c)
    (cMinus cPlus : ℤ), ExceptionalAdjointPreserves l E n hn (D.rightAdjoint c) cMinus cPlus

/-- Ambient adjunctions at every positive finite coefficient stage, with the full
refinement datum and the full-CD existence statement at the fixed compactification.
Index n denotes exponent n+1 and therefore covers every positive exponent.
Source: Weil blueprint, order 1474, coefficient paragraph
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable def FiniteExceptionalAdjunctionFamily
    {I : Type w} (l : ℕ) [Fact l.Prime] (E : I → Type u)
    [∀ i, Field (E i)] [∀ i, Algebra (Padic l) (E i)]
    [∀ i, FiniteDimensional (Padic l) (E i)] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : Compactification f) : Type _ :=
  ∀ (i : I) (n : ℕ),
    letI := Padic.finite_coefficientExtensionRing l (E i) (n + 1) (Nat.le_add_left 1 n)
    SfAmbientExceptionalRightAdjointDatum (Padic.coefficientExtensionRing l (E i) (n + 1)) f c

/-- The three finite-stage conditions with one choice of bounds for the entire system.
There is no sign restriction on the two cohomological-amplitude bounds. The full-CD
bound is also uniform, independently of the coefficient field and positive exponent.
Source: Weil blueprint, order 1474, coefficient paragraph
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable def HasUniformFiniteExceptionalAdjoints
    {I : Type w} (l : ℕ) [Fact l.Prime] (E : I → Type u)
    [∀ i, Field (E i)] [∀ i, Algebra (Padic l) (E i)]
    [∀ i, FiniteDimensional (Padic l) (E i)] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : Compactification f) (D : FiniteExceptionalAdjunctionFamily l E f c) : Prop :=
  ∃ (cCD : ℕ) (cMinus cPlus : ℤ), ∀ (i : I) (n : ℕ),
    letI := Padic.finite_coefficientExtensionRing l (E i) (n + 1) (Nat.le_add_left 1 n)
    sfFullCohomologicalDimension c.g (Padic.coefficientExtensionRing l (E i) (n + 1)) cCD ∧
      ExceptionalAdjointPreserves l (E i) (n + 1) (Nat.le_add_left 1 n)
        ((D i n).rightAdjoint c) cMinus cPlus

/-- Derived tensor with a finite coefficient-ring map exists as the left adjoint
of the actual, exact restriction of scalars. This universal property fixes its
object, morphisms and tensor unit up to unique compatible isomorphism.
Source: Stacks Tags 06YY and 07A6
(blueprint: def-weil-exceptional-adjoint-admissibility).
Proof: take K-flat resolutions in all module sheaves, tensor termwise along the
map of constant ring sheaves, and descend the tensor/restriction adjunction.
The unit sends a local section x to x tensor 1. Independence of the resolution
and the tensor universal property give the derived adjunction on the whole
unbounded categories, including nonflat quotient maps. -/
theorem exceptionalCoefficientRestriction_isRightAdjoint
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    ((proEtaleCoefficientRestrictScalars T φ).mapDerivedCategory).IsRightAdjoint := by
  exact (pbcDerivedScalarAdjunction
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom φ.ulift))).isRightAdjoint

/-- Actual derived coefficient extension; no arbitrary coefficient functor is input.
Source: Stacks Tags 06YY and 07A6
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable def exceptionalCoefficientExtension
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    proEtaleDerivedCategory T A ⥤ proEtaleDerivedCategory T B :=
  letI := exceptionalCoefficientRestriction_isRightAdjoint φ T
  ((proEtaleCoefficientRestrictScalars T φ).mapDerivedCategory).leftAdjoint

/-- The actual tensor/restriction adjunction, with its tensor-with-one unit.
Source: Stacks Tags 06YY and 07A6
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable def exceptionalCoefficientAdjunction
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    exceptionalCoefficientExtension φ T ⊣
      (proEtaleCoefficientRestrictScalars T φ).mapDerivedCategory :=
  letI := exceptionalCoefficientRestriction_isRightAdjoint φ T
  Adjunction.ofIsRightAdjoint _

/-- The canonical support coefficient map, obtained by transposing the explicitly
normalized restriction comparison. That comparison is the open unit mate followed
by the proper comparison fixed on K-injective resolutions. Thus neither the map
nor its normalization can be supplied independently of the actual ring map.
Source: Stacks Tags 0GL6, 0D6E and 07A6
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable def exceptionalFiniteSupportExtensionMap
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    sfAmbientCompactSupportCandidate A c ⋙ exceptionalCoefficientExtension φ Y ⟶
      exceptionalCoefficientExtension φ X ⋙ sfAmbientCompactSupportCandidate B c :=
  ((mateEquiv (exceptionalCoefficientAdjunction φ X)
    (exceptionalCoefficientAdjunction φ Y)).symm
      (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom)).natTrans

/-- An ambient right adjoint makes the canonical support coefficient map invertible.
This concerns the LEFT support comparison, not the optional right-adjoint mate.
Source: Stacks, Cohomology on Sites, projection formula; blueprint coefficient comparisons
(blueprint: def-weil-exceptional-adjoint-admissibility).
Proof: transport the support adjunction to fixed coefficients. The open projection
isomorphism makes the proper projection target a left adjoint. After precomposition
with the exact constant-sheaf functor, both projection functors preserve coproducts
and triangles; generation of D(A) by A[0] reduces invertibility to the monoidal unit.
The normalized restriction square identifies the scalar mate, after conservative
restriction and realization, with this projection at the constant target ring.
Hence every component is invertible, including unbounded inputs and nonflat quotients. -/
theorem exceptionalFiniteSupportExtensionMap_isIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {G : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory X A}
    (_a : sfAmbientCompactSupportCandidate A c ⊣ G) :
    IsIso (exceptionalFiniteSupportExtensionMap φ c) := by
  have (K : proEtaleDerivedCategory X A) :
      IsIso ((exceptionalFiniteSupportExtensionMap φ c).app K) :=
    supportCoefficient_isIso_of_projection φ c
      (exceptionalCoefficientExtension φ X) (exceptionalCoefficientExtension φ Y)
      (exceptionalCoefficientAdjunction φ X) (exceptionalCoefficientAdjunction φ Y) _a K
  exact NatIso.isIso_of_isIso_app _

/-- The right coefficient comparison is the actual mate, using the SAME chosen
ambient adjunctions and the published canonical support restriction comparison.
Source: blueprint order 1474, coefficient paragraph; Stacks Tag 07A7
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable def exceptionalFiniteRightCoefficientMap
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (DA : SfAmbientExceptionalRightAdjointDatum A f c)
    (DB : SfAmbientExceptionalRightAdjointDatum B f c) :
    DA.rightAdjoint c ⋙ exceptionalCoefficientExtension φ X ⟶
      exceptionalCoefficientExtension φ Y ⋙ DB.rightAdjoint c :=
  letI := exceptionalFiniteSupportExtensionMap_isIso φ c (DA.adjunction c)
  (mateEquiv (DA.adjunction c) (DB.adjunction c)
    (TwoSquare.mk _ _ _ _ (asIso (exceptionalFiniteSupportExtensionMap φ c)).inv)).natTrans

/-- Invertibility of the canonical right coefficient mate for the specified DA, DB.
Source: blueprint order 1474 (blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable def ExceptionalFiniteCoefficientCompatible
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (DA : SfAmbientExceptionalRightAdjointDatum A f c)
    (DB : SfAmbientExceptionalRightAdjointDatum B f c) : Prop :=
  IsIso (exceptionalFiniteRightCoefficientMap φ c DA DB)

/-- All positive finite exponents for one fixed finite coefficient field.
Source: blueprint order 1474 (blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable abbrev ExceptionalFiniteFieldFamily
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : Compactification f) :=
  FiniteExceptionalAdjunctionFamily l (fun _ : PUnit.{1} ↦ E) f c

/-- Every positive quotient map A_(E,n+1) → A_(E,m+1), INCLUDING equality of
exponents. These are derived tensor maps even when the quotient is not flat.
Source: blueprint order 1474; sk-def-sf-operations (vi)
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable def ExceptionalFiniteReductionsCompatible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (c : Compactification f) (D : ExceptionalFiniteFieldFamily l E f c) : Prop :=
  ∀ (m n : ℕ) (h : m ≤ n),
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
    letI := Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.le_add_left 1 m)
    ExceptionalFiniteCoefficientCompatible
      (Ideal.Quotient.factor (S := Padic.coefficientExtensionIdeal l E (n + 1))
        (T := Padic.coefficientExtensionIdeal l E (m + 1))
        (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))) c (D PUnit.unit n) (D PUnit.unit m)

/-- Every finite scalar-extension map at each positive exponent, INCLUDING the
identity embedding. Its ring map is the actual valuation-ring inclusion descended
to the quotient, not a freely chosen map or square.
Source: blueprint order 1474; completed scalar extension finite projections
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable def ExceptionalFiniteScalarsCompatible
    (l : ℕ) [Fact l.Prime] (E L : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (DE : ExceptionalFiniteFieldFamily l E f c)
    (DL : ExceptionalFiniteFieldFamily l L f c) : Prop :=
  ∀ n : ℕ,
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.le_add_left 1 n)
    ExceptionalFiniteCoefficientCompatible (integralScalarQuotientMap l E L ι n) c
      (DE PUnit.unit n) (DL PUnit.unit n)

/-- The finite-system criterion at an integral coefficient field. The exponent
index is always ℕ, representing n+1. Scalar extensions range over ALL finite
extensions and algebra embeddings of E, including the identity. Target finite
adjoints are chosen with their own uniform bounds; the source bounds do not vary
with the exponent. All coefficient maps are the actual maps defined above.
Source: blueprint order 1474, original final defining paragraph, and
sk-def-sf-operations (vi) (blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable def IsExceptionalAdjointAdmissibleAtIntegral
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (_hS : ∀ s : S, IsUnit (l : S.presheaf.stalk s))
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Prop :=
  ∃ DE : ExceptionalFiniteFieldFamily l E f c,
    HasUniformFiniteExceptionalAdjoints l (fun _ : PUnit.{1} ↦ E) f c DE ∧
      ExceptionalFiniteReductionsCompatible l E f c DE ∧
      ∀ (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
        (ι : E →ₐ[Padic l] L),
        ∃ DL : ExceptionalFiniteFieldFamily l L f c,
          HasUniformFiniteExceptionalAdjoints l (fun _ : PUnit.{1} ↦ L) f c DL ∧
            ExceptionalFiniteReductionsCompatible l L f c DL ∧
            ExceptionalFiniteScalarsCompatible l E L ι f c DE DL

/-- The same finite-system criterion at the raw rationalization of the integral
category. The blueprint imposes the finite-stage obligations before rationalizing;
there is no idempotent completion and no arbitrary rational comparison square.
Source: blueprint order 1474, original final defining paragraph
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable abbrev IsExceptionalAdjointAdmissibleAtRational
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (hS : ∀ s : S, IsUnit (l : S.presheaf.stalk s))
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Prop :=
  IsExceptionalAdjointAdmissibleAtIntegral l E S X Y hS f c

/-- Admissibility at common-stage algebraically closed coefficients. Every finite
intermediate field of the FIXED algebraic closure is included; its bottom field
witnesses nonemptiness. Bounds are outside both the field and exponent quantifiers.
Every quotient and every field inclusion (including identity inclusions) is tested
using the very same chosen ambient adjoints. The common-stage category uses these
finite subfields and their inclusions, not an optional input diagram.
Source: blueprint order 1474, final defining paragraph; sk-def-sf-operations (vi)
(blueprint: def-weil-exceptional-adjoint-admissibility). -/
noncomputable def IsExceptionalAdjointAdmissibleAtAlgebraicallyClosed
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (_hS : ∀ s : S, IsUnit (l : S.presheaf.stalk s))
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Prop :=
  letI : ∀ E : Padic.FiniteCoefficientFields l Ω, Small.{u} E.val :=
    fun E ↦ small_map (Module.finBasis (Padic l) E.val).equivFun.toEquiv
  letI : ∀ E : Padic.FiniteCoefficientFields l Ω,
      FiniteDimensional (Padic l) (Shrink.{u} E.val) :=
    fun E ↦ Module.Finite.equiv (Shrink.algEquiv (Padic l) E.val).symm.toLinearEquiv
  ∃ D : FiniteExceptionalAdjunctionFamily l
      (fun E : Padic.FiniteCoefficientFields l Ω ↦ Shrink.{u} E.val) f c,
    HasUniformFiniteExceptionalAdjoints l
        (fun E : Padic.FiniteCoefficientFields l Ω ↦ Shrink.{u} E.val) f c D ∧
      (∀ E : Padic.FiniteCoefficientFields l Ω,
        ExceptionalFiniteReductionsCompatible l (Shrink.{u} E.val) f c (fun _ n ↦ D E n)) ∧
      ∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L),
        ExceptionalFiniteScalarsCompatible l (Shrink.{u} E.val) (Shrink.{u} L.val)
          ((Shrink.algEquiv (Padic l) L.val).symm.toAlgHom.comp
            ((IntermediateField.inclusion h).comp
              (Shrink.algEquiv (Padic l) E.val).toAlgHom))
          f c (fun _ n ↦ D E n) (fun _ n ↦ D L n)

end WeilConjectures
