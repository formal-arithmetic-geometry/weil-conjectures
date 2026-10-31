/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.IntegralQuotientCoefficients
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimensionSupplement
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction

/-! # Closed-support localization with condensed coefficients

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sf-localization/
prop-sf-localization-all-stages.md and its proof
(blueprint: prop-sf-localization-all-stages).

All operations act on the ordinary derived category of modules over the pulled-back
condensed ring. The structure below records restrictions of the prescribed functors and
their right adjunction, so it does not choose an unrelated counit or exceptional map.

## Main statements

* `condensedClosedLocalization`: support adjunction, triangle and finite-Tor restrictions.
* `condensedClosedLocalization_finiteBounds`: explicit finite-coefficient Tor bounds.
* `condensedClosedLocalization_finiteExceptional`: finite etale exceptional identification.
* `condensedClosedLocalization_nativeExceptional`: native Brown exceptional identification.
* `condensedClosedLocalization_integralReduction`: reduction comparison and uniform bounds.
* `condensedClosedLocalization_weil`: canonical Frobenius exchanges and equivariant triangle.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Restrictions and the exceptional adjunction for a closed/open pair. Every functor
except the right adjoint is fixed by the ambient module operations. The right adjoint is
specified by its adjunction, hence up to unique counit-compatible isomorphism.
Source: clauses (1)--(2) (blueprint: prop-sf-localization-all-stages). -/
structure ClosedLocalization {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) where
  /-- Closed direct image preserves bounded constructibility. -/
  closed_mem : ∀ K : ConstantModelBoundedConstructible Λ Z,
    constantModelBoundedConstructible Λ X ((moduleObjectDerivedPushforward Λ i).obj K.obj)
  /-- Open direct image preserves bounded constructibility, clause (1). -/
  open_mem : ∀ K : ConstantModelBoundedConstructible Λ U,
    constantModelBoundedConstructible Λ X ((moduleObjectDerivedPushforward Λ j).obj K.obj)
  /-- Closed pullback preserves bounded constructibility. -/
  closed_pull_mem : ∀ K : ConstantModelBoundedConstructible Λ X,
    constantModelBoundedConstructible Λ Z ((moduleObjectDerivedPullback Λ i).obj K.obj)
  /-- Open pullback preserves bounded constructibility. -/
  open_pull_mem : ∀ K : ConstantModelBoundedConstructible Λ X,
    constantModelBoundedConstructible Λ U ((moduleObjectDerivedPullback Λ j).obj K.obj)
  /-- The right adjoint on bounded constructible objects, clause (2). -/
  exceptional : ConstantModelBoundedConstructible Λ X ⥤ ConstantModelBoundedConstructible Λ Z
  /-- Its defining adjunction to the actual closed direct image. -/
  adjunction : (constantModelBoundedConstructible Λ X).lift
    ((constantModelBoundedConstructible Λ Z).ι ⋙ moduleObjectDerivedPushforward Λ i)
      closed_mem ⊣ exceptional

variable {Λ} {X Z U : Scheme.{u}} {i : Z ⟶ X} {j : U ⟶ X}

/-- The actual closed direct image, restricted to Dbc.
Source: clause (2) (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.closedPush (L : ClosedLocalization Λ i j) :=
  (constantModelBoundedConstructible Λ X).lift
    ((constantModelBoundedConstructible Λ Z).ι ⋙ moduleObjectDerivedPushforward Λ i) L.closed_mem

/-- The actual open direct image, restricted to Dbc.
Source: clause (1) (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.openPush (L : ClosedLocalization Λ i j) :=
  (constantModelBoundedConstructible Λ X).lift
    ((constantModelBoundedConstructible Λ U).ι ⋙ moduleObjectDerivedPushforward Λ j) L.open_mem

/-- The actual open pullback, restricted to Dbc.
Source: clause (3) (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.openPull (L : ClosedLocalization Λ i j) :=
  (constantModelBoundedConstructible Λ U).lift
    ((constantModelBoundedConstructible Λ X).ι ⋙ moduleObjectDerivedPullback Λ j) L.open_pull_mem

/-- The actual closed pullback, restricted to Dbc.
Source: clause (3') (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.closedPull (L : ClosedLocalization Λ i j) :=
  (constantModelBoundedConstructible Λ Z).lift
    ((constantModelBoundedConstructible Λ X).ι ⋙ moduleObjectDerivedPullback Λ i) L.closed_pull_mem

/-- The prescribed support triangle with a variable last arrow; the first two arrows
are the exceptional counit and ordinary open adjunction unit.
Source: clause (3) (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.triangle (L : ClosedLocalization Λ i j)
    (K : ConstantModelBoundedConstructible Λ X)
    (δ : (moduleObjectDerivedPushforward Λ j).obj
        ((moduleObjectDerivedPullback Λ j).obj K.obj) ⟶
      ((moduleObjectDerivedPushforward Λ i).obj (L.exceptional.obj K).obj) ⟦(1 : ℤ)⟧) :=
  Triangle.mk (L.adjunction.counit.app K).hom
    ((derivedUpperStarLowerStarAdjunction Λ j).unit.app K.obj) δ

/-- Clauses (3)--(4), including all shifted orthogonality, unique boundary and
functoriality with its prescribed three vertex maps. IsZero and IsIso are in the
ambient category; fullness makes these precisely the corresponding assertions in Dbc.
Source: clauses (3)--(4) (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.Support (L : ClosedLocalization Λ i j) : Prop :=
  (∀ (P : ConstantModelBoundedConstructible Λ Z)
    (G : ConstantModelBoundedConstructible Λ U) (m : ℤ),
    Subsingleton (((moduleObjectDerivedPushforward Λ i).obj P.obj) ⟦m⟧ ⟶
      (moduleObjectDerivedPushforward Λ j).obj G.obj)) ∧
  (∀ K : ConstantModelBoundedConstructible Λ X,
    ∃! δ, L.triangle K δ ∈ distTriang _) ∧
  (∀ (K K' : ConstantModelBoundedConstructible Λ X) (f : K ⟶ K') (δ δ'),
    L.triangle K δ ∈ distTriang _ → L.triangle K' δ' ∈ distTriang _ →
    ∃ t : L.triangle K δ ⟶ L.triangle K' δ',
      t.hom₁ = (moduleObjectDerivedPushforward Λ i).map (L.exceptional.map f).hom ∧
      t.hom₂ = f.hom ∧
      t.hom₃ = (moduleObjectDerivedPushforward Λ j).map
        ((moduleObjectDerivedPullback Λ j).map f.hom)) ∧
  (∀ G : ConstantModelBoundedConstructible Λ U,
    IsZero (L.exceptional.obj (L.openPush.obj G)).obj) ∧
  (∀ Q : ConstantModelBoundedConstructible Λ Z, IsIso (L.adjunction.unit.app Q))

/-- The finite-Tor clauses. The restrictions of the same adjunction, triangle and
vanishing assertions are expressed on all finite-Tor objects, with no new morphisms.
Source: (1')--(4') (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.FiniteTor (L : ClosedLocalization Λ i j) : Prop :=
  (∀ G : ConstantModelBoundedConstructible Λ U, DerivedCategory.finiteTorAmplitude _ G.obj →
    DerivedCategory.finiteTorAmplitude _ (L.openPush.obj G).obj) ∧
  (∀ K : ConstantModelBoundedConstructible Λ X, DerivedCategory.finiteTorAmplitude _ K.obj →
    DerivedCategory.finiteTorAmplitude _ (L.exceptional.obj K).obj) ∧
  (∀ (P : ConstantModelBoundedConstructible Λ Z) (a b : ℤ), a ≤ b →
    DerivedCategory.torAmplitudeIn _ a b P.obj →
    DerivedCategory.torAmplitudeIn _ a b (L.closedPush.obj P).obj) ∧
  (∀ (K : ConstantModelBoundedConstructible Λ X) (a b : ℤ), a ≤ b →
    DerivedCategory.torAmplitudeIn _ a b K.obj →
    DerivedCategory.torAmplitudeIn _ a b (L.closedPull.obj K).obj ∧
    DerivedCategory.torAmplitudeIn _ a b (L.openPull.obj K).obj)

/-- The dimension used in the bound: d is the ordinary Krull dimension for nonempty U
and zero for empty U. This uses the recorded dimension, including its bottom element.
Source: paragraph before (1') (blueprint: prop-sf-localization-all-stages). -/
def localizationDimension (U : Scheme.{u}) (d : ℕ) : Prop :=
  (IsEmpty U ∧ d = 0) ∨ topologicalKrullDim U = (d : WithBot ℕ∞)

/-- The two explicit Tor bounds at a finite coefficient stage.
Source: (1')--(2') (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.TorBounds (L : ClosedLocalization Λ i j) (d c : ℕ) : Prop :=
  (∀ (G : ConstantModelBoundedConstructible Λ U) (a b : ℤ), a ≤ b →
    DerivedCategory.torAmplitudeIn _ a b G.obj →
    DerivedCategory.torAmplitudeIn _ a (b + 2 * (d : ℤ) + c) (L.openPush.obj G).obj) ∧
  (∀ (K : ConstantModelBoundedConstructible Λ X) (a b : ℤ), a ≤ b →
    DerivedCategory.torAmplitudeIn _ a b K.obj →
    DerivedCategory.torAmplitudeIn _ a (b + 2 * (d : ℤ) + c + 1) (L.exceptional.obj K).obj)


variable (Λ)

/-- The four coefficient stages of the proposition, using the actual positive quotient,
integral continuous ring, finite extension with its extending norm, and condensed closure.
The isomorphisms identify ring objects, including their operations.
Source: opening coefficient paragraph (blueprint: prop-sf-localization-all-stages). -/
def IsLocalizationCoefficient (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ell] E]
    [FiniteDimensional ℚ_[ell] E] (n : ℕ) : Prop :=
  Nonempty (Mon.mk Λ ≅ Mon.mk (IntegralQuotient.finite ell E n)) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (IntegralQuotient.integral ell E)) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousCoefficientRingObj E)) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))

/-- All four coefficient stages have the closed exceptional adjunction, the unique
functorial distinguished support triangle, vanishing, unit isomorphism and finite-Tor
restrictions. The nonempty structure is a right adjoint with its defining adjunction,
not a choice of an unrelated functor.
Source: clauses (1)--(4), (1')--(4') (blueprint: prop-sf-localization-all-stages).

Proof: At finite coefficients descend to an etale bounded constructible origin. Direct
image comparison, finite-type constructibility and truncation give open finiteness.
At the other stages use six-operation stability and Dctf = Dbc. The fibre of the open
unit is bounded constructible, vanishes on U and is therefore i_* of its closed
restriction. Shifted orthogonality identifies the represented Hom functor, giving Ri!
and its adjunction. It gives uniqueness of the boundary, functoriality, Ri! Rj_* = 0
and the invertible closed unit. Exact monoidal pullbacks preserve Tor intervals.
For closed direct image apply the residue criterion and exact closed restriction to
its cohomology supported on Z. For open direct image combine the finite etale cd bound
with the finite-constant projection formula and truncation; the support triangle then
bounds Ri!. Reduction transports the integral bounds uniformly; at rational and closure
coefficients Dctf = Dbc. Fullness restricts the same triangles and adjunctions to Dctf. -/
theorem condensedClosedLocalization
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hEll : ell ≠ D.p) (E : Type u) [NormedField E] [NormedAlgebra ℚ_[ell] E]
    [FiniteDimensional ℚ_[ell] E] (n : ℕ)
    (_hΛ : IsLocalizationCoefficient Λ ell E n)
    (X Z U : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i.left] [IsOpenImmersion j.left]
    (_hij : Set.range i.left.base = (Set.range j.left.base)ᶜ) :
    ∃ L : ClosedLocalization Λ i.left j.left, L.Support ∧ L.FiniteTor := by
  sorry

variable {Λ}

/-- Finite-stage Tor bounds, with the empty-open convention and the recorded torsion
cohomological dimension. Any adjunction choice gives the same exceptional functor.
Source: (1')--(2') (blueprint: prop-sf-localization-all-stages).

Proof: Put kappa = A/(pi). The residue criterion detects each Tor interval. Descend
the bounded constructible input to the etale site, where exact comparison reflects
its residue interval. The cd bound is 2d+c. Resolve kappa by finite free modules;
finite truncations satisfy projection, and the cd bound makes their tails vanish in
each fixed degree, giving projection for kappa. Truncation bounds Rj_*. Tensor the
support triangle with kappa and use its long exact sequence to obtain the extra +1
for Ri!, then restrict to Z. Uniqueness of adjoints identifies every L with this one. -/
theorem condensedClosedLocalization_finiteBounds
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hEll : ell ≠ D.p) (E : Type u) [Field E] [Algebra ℚ_[ell] E]
    [FiniteDimensional ℚ_[ell] E] (n : ℕ)
    (X Z U : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i.left] [IsOpenImmersion j.left]
    (_hij : Set.range i.left.base = (Set.range j.left.base)ᶜ)
    (L : ClosedLocalization (IntegralQuotient.finite ell E n) i.left j.left)
    (d c : ℕ) (_hd : localizationDimension U.left d)
    (_hc : (Spec (.of D.k)).HasTorsionEtaleCohomologicalDimensionLE c) :
    L.TorBounds d c := by
  sorry

/-- At finite coefficients the right adjoint just constructed is exactly the recorded
etale exceptional inverse image transported to pro-etale coefficients. The encoding
is the normalized section-action equivalence, not an arbitrary comparison functor.
Source: clause (2), finite identification (blueprint: prop-sf-localization-all-stages).

Proof: Closed direct image is exact and fully faithful on both sites. Its supported
right adjoint and triangle are compatible with site comparison on bounded-below
etale-origin objects. Finite constructible descent and the normalized coefficient
encoding identify the closed direct images. Transport the etale exceptional adjunction
through them; uniqueness of right adjoints gives the displayed natural isomorphism. -/
theorem condensedClosedLocalization_finiteExceptional
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hEll : ell ≠ D.p) (E : Type u) [Field E] [Algebra ℚ_[ell] E]
    [FiniteDimensional ℚ_[ell] E] (n : ℕ)
    (X Z U : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i.left]
    (L : ClosedLocalization (IntegralQuotient.finite ell E n) i.left j.left)
    (eX : FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing ell E (n + 1)) X.left)
    (eZ : FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing ell E (n + 1)) Z.left) :
    letI : Z.left.Over (Spec (.of D.k)) := ⟨Z.hom⟩
    letI : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
    letI : LocallyOfFiniteType (Z.left ↘ Spec (.of D.k)) :=
      inferInstanceAs (LocallyOfFiniteType Z.hom)
    letI : QuasiCompact (Z.left ↘ Spec (.of D.k)) :=
      inferInstanceAs (QuasiCompact Z.hom)
    letI : LocallyOfFiniteType (X.left ↘ Spec (.of D.k)) :=
      inferInstanceAs (LocallyOfFiniteType X.hom)
    letI : QuasiCompact (X.left ↘ Spec (.of D.k)) :=
      inferInstanceAs (QuasiCompact X.hom)
    Nonempty (L.exceptional ⋙ (constantModelBoundedConstructible
        (IntegralQuotient.finite ell E n) Z.left).ι ⋙ eZ.ordinaryDerived.functor ≅
      (constantModelBoundedConstructible (IntegralQuotient.finite ell E n) X.left).ι ⋙
        eX.ordinaryDerived.functor ⋙
        Scheme.finiteExceptionalInverseImage ell E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
          D.k Z.left X.left i.left) := by
  sorry

/-- Identification with the specified Brown exceptional functor at every nonfinite stage.
The localizing choice is exactly the one used by the recorded definition.
Source: clause (2), exceptional identification (blueprint: prop-sf-localization-all-stages).

Proof: For a closed immersion compact support is direct image. Restrict the Brown
adjunction to bounded constructible objects, using Dctf = Dbc at these coefficients.
Both right adjoints represent the same Hom functor; adjunction uniqueness provides
the natural isomorphism to the native definition, itself the Brown restriction. -/
theorem condensedClosedLocalization_nativeExceptional
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hΛ : IsNativeExceptionalCoefficient ell Λ)
    (X Z U : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i.left]
    (L : ClosedLocalization Λ i.left j.left) :
    Nonempty (L.exceptional ≅ constructibleExceptionalInverseImage Λ ell k i hΛ) := by
  sorry

/-- Ordinary reduction of Ri! and the uniform integral Tor bounds. The reduction maps
are the actual quotient maps O_E -> A_{E,m}; the index m has exponent m+1.
Source: (2), (1')--(2') at O_E (blueprint: prop-sf-localization-all-stages).

Proof: The coefficient comparisons for the six operations identify reductions of Ri!
and Rj_* with their finite-stage operations. Restrict the comparisons to the full
constructible categories. Apply the finite residue bounds at each level. They depend
only on d,c and the single input interval, hence are uniform in m. -/
theorem condensedClosedLocalization_integralReduction
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hEll : ell ≠ D.p) (E : Type u) [Field E] [Algebra ℚ_[ell] E]
    [FiniteDimensional ℚ_[ell] E]
    (X Z U : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i.left] [IsOpenImmersion j.left]
    (_hij : Set.range i.left.base = (Set.range j.left.base)ᶜ)
    (L : ClosedLocalization (IntegralQuotient.integral ell E) i.left j.left)
    (Ln : ∀ n : ℕ, ClosedLocalization (IntegralQuotient.finite ell E n) i.left j.left)
    (d c : ℕ) (_hd : localizationDimension U.left d)
    (_hc : (Spec (.of D.k)).HasTorsionEtaleCohomologicalDimensionLE c) :
    (∀ n : ℕ, ∃ hX : ∀ K : ConstantModelBoundedConstructible
        (IntegralQuotient.integral ell E) X.left,
        constantModelBoundedConstructible (IntegralQuotient.finite ell E n) X.left
          ((IntegralQuotient.scalar ell E X.left n).obj K.obj),
      Nonempty (L.exceptional ⋙ (constantModelBoundedConstructible
          (IntegralQuotient.integral ell E) Z.left).ι ⋙ IntegralQuotient.scalar ell E Z.left n ≅
        (constantModelBoundedConstructible (IntegralQuotient.finite ell E n) X.left).lift
          ((constantModelBoundedConstructible (IntegralQuotient.integral ell E) X.left).ι ⋙
            IntegralQuotient.scalar ell E X.left n) hX ⋙ (Ln n).exceptional ⋙
              (constantModelBoundedConstructible (IntegralQuotient.finite ell E n) Z.left).ι)) ∧
    (∀ (G : ConstantModelBoundedConstructible (IntegralQuotient.integral ell E) U.left)
      (a b : ℤ), a ≤ b →
      (∀ n : ℕ, DerivedCategory.torAmplitudeIn _ a b
        ((IntegralQuotient.scalar ell E U.left n).obj G.obj)) →
      ∀ n : ℕ, DerivedCategory.torAmplitudeIn _ a (b + 2 * (d : ℤ) + c)
        ((IntegralQuotient.scalar ell E X.left n).obj (L.openPush.obj G).obj)) ∧
    (∀ (K : ConstantModelBoundedConstructible (IntegralQuotient.integral ell E) X.left)
      (a b : ℤ), a ≤ b →
      (∀ n : ℕ, DerivedCategory.torAmplitudeIn _ a b
        ((IntegralQuotient.scalar ell E X.left n).obj K.obj)) →
      ∀ n : ℕ, DerivedCategory.torAmplitudeIn _ a (b + 2 * (d : ℤ) + c + 1)
        ((IntegralQuotient.scalar ell E Z.left n).obj (L.exceptional.obj K).obj)) := by
  sorry


variable (Λ)

/-- The recorded exact Frobenius action restricted to Dbc. At the two field stages
Dbc = Dctf; its fixed pairs are thus the strict Weil pairs of the recorded definition.
Source: Weil paragraph (blueprint: prop-sf-localization-all-stages). -/
def localizationAction {T : Scheme.{u}} (g : T ≅ T) :
    ConstantModelBoundedConstructible Λ T ⥤ ConstantModelBoundedConstructible Λ T :=
  (constantModelBoundedConstructible Λ T).lift
    ((constantModelBoundedConstructible Λ T).ι ⋙ StrictWeil.action Λ g)
    (fun K ↦ ((StrictWeil.action_preserves Λ g K.obj).1).mpr K.property)

/-- Pullback composition across a commuting automorphism square. This is constructed
from the actual module-derived compositors and the exact Frobenius comparison.
Source: Weil paragraph, derived pullback composition
(blueprint: prop-sf-localization-all-stages). -/
def localizationPullExchange {S T : Scheme.{u}} (f : S ⟶ T)
    (gS : S ≅ S) (gT : T ≅ T) (h : f ≫ gT.hom = gS.hom ≫ f) :
    moduleObjectDerivedPullback Λ f ⋙ StrictWeil.action Λ gS ≅
      StrictWeil.action Λ gT ⋙ moduleObjectDerivedPullback Λ f :=
  (Functor.isoWhiskerLeft (moduleObjectDerivedPullback Λ f)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ gS.hom)).symm ≪≫
    (leftDerivedUpperStarComp Λ gS.hom f).symm ≪≫
    Functor.leftDerivedFunctorNatIso _ (upperStarCongr Λ h.symm) ≪≫
    leftDerivedUpperStarComp Λ f gT.hom ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ gT.hom)
      (moduleObjectDerivedPullback Λ f)

variable {Λ}

/-- The closed pullback/direct-image adjunction restricted from the specified ambient
module adjunction. Source: Weil paragraph (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.closedPullPushAdjunction (L : ClosedLocalization Λ i j) :
    L.closedPull ⊣ L.closedPush :=
  (derivedUpperStarLowerStarAdjunction Λ i).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (Iso.refl _) (Iso.refl _)

/-- The open pullback/direct-image adjunction with its specified ambient unit.
Source: Weil paragraph (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.openPullPushAdjunction (L : ClosedLocalization Λ i j) :
    L.openPull ⊣ L.openPush :=
  (derivedUpperStarLowerStarAdjunction Λ j).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (Iso.refl _) (Iso.refl _)

/-- Restrict the canonical Frobenius square comparison for closed pullback.
Source: Weil paragraph (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.closedPullExchange (L : ClosedLocalization Λ i j)
    (gZ : Z ≅ Z) (gX : X ≅ X) (h : i ≫ gX.hom = gZ.hom ≫ i) :
    L.closedPull ⋙ localizationAction Λ gZ ≅ localizationAction Λ gX ⋙ L.closedPull :=
  NatIso.ofComponents (fun K ↦ (constantModelBoundedConstructible Λ Z).isoMk
    ((localizationPullExchange Λ i gZ gX h).app K.obj))
    (fun f ↦ ObjectProperty.hom_ext _ ((localizationPullExchange Λ i gZ gX h).hom.naturality
      f.hom))

/-- Restrict the canonical Frobenius square comparison for open pullback.
Source: Weil paragraph (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.openPullExchange (L : ClosedLocalization Λ i j)
    (gU : U ≅ U) (gX : X ≅ X) (h : j ≫ gX.hom = gU.hom ≫ j) :
    L.openPull ⋙ localizationAction Λ gU ≅ localizationAction Λ gX ⋙ L.openPull :=
  NatIso.ofComponents (fun K ↦ (constantModelBoundedConstructible Λ U).isoMk
    ((localizationPullExchange Λ j gU gX h).app K.obj))
    (fun f ↦ ObjectProperty.hom_ext _ ((localizationPullExchange Λ j gU gX h).hom.naturality
      f.hom))

/-- Every arrow of the support triangle intertwines the indicated Weil structures.
Using a triangle isomorphism includes the canonical shift comparison on its last arrow.
Source: Weil paragraph, final sentence (blueprint: prop-sf-localization-all-stages). -/
def ClosedLocalization.WeilTriangle (L : ClosedLocalization Λ i j)
    (gZ : Z ≅ Z) (gX : X ≅ X) (gU : U ≅ U)
    (hj : j ≫ gX.hom = gU.hom ≫ j)
    (ei : L.closedPush ⋙ localizationAction Λ gX ≅
      localizationAction Λ gZ ⋙ L.closedPush)
    (er : L.exceptional ⋙ localizationAction Λ gZ ≅
      localizationAction Λ gX ⋙ L.exceptional)
    (ej : L.openPush ⋙ localizationAction Λ gX ≅
      localizationAction Λ gU ⋙ L.openPush) : Prop :=
  ∀ (K : Endofunctor.IsoAlgebra (localizationAction Λ gX)) (δ),
    L.triangle K.carrier δ ∈ distTriang _ →
    ∃ e : (StrictWeil.action Λ gX).mapTriangle.obj (L.triangle K.carrier δ) ≅
        L.triangle K.carrier δ,
      e.hom.hom₁ =
        ((Endofunctor.IsoAlgebra.mapOfNatIso ei).obj
          ((Endofunctor.IsoAlgebra.mapOfNatIso er).obj K)).str.hom.hom ∧
      e.hom.hom₂ = K.str.hom.hom ∧
      e.hom.hom₃ =
        ((Endofunctor.IsoAlgebra.mapOfNatIso ej).obj
          ((Endofunctor.IsoAlgebra.mapOfNatIso (L.openPullExchange gU gX hj)).obj K)
        ).str.hom.hom

variable (Λ)

/-- The geometric base change of a model morphism, reusing the actual pullback functor.
Source: descended immersion pair in the Weil paragraph
(blueprint: prop-sf-localization-all-stages). -/
def localizationFiberMap (D : WeilConjectures.FiniteFieldDatum.{u})
    {S T : Over (Spec (.of D.k₀))} (f : S ⟶ T) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f).left

/-- At field coefficients the closed adjunction lifts to strict Weil pairs with its
original unit and counit, and the support triangle is equivariant. The exchanges for
both direct images and for Ri! are fixed to be the mates of the canonical pullback
comparisons. Thus no arbitrary Weil structure is substituted for the geometric one.
Source: final Weil paragraph (blueprint: prop-sf-localization-all-stages).

Proof: Base-change functoriality gives the two commuting geometric Frobenius squares.
Derived pullback composition provides the displayed closed/open pullback comparisons.
The exact Frobenius functors are equivalences. Their mates under pullback/direct image
are therefore invertible; the mate under i_* / Ri! is invertible as well. The fixed-pair
adjunction lift has precisely the original carrier unit and counit. They are equivariant.
Apply Frobenius to the support triangle and conjugate its vertices by these structures.
The first two arrows are unchanged by the mate identities. Boundary uniqueness makes
the third unchanged. This applies to all strict pairs, hence also to the underlying pairs
of native Weil complexes, without requiring a triangulation of the fixed-pair category. -/
theorem condensedClosedLocalization_weil
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hEll : ell ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ell)
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (X₀ Z₀ U₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom] [IsSeparated Z₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
    (i₀ : Z₀ ⟶ X₀) (j₀ : U₀ ⟶ X₀)
    [IsClosedImmersion i₀.left] [IsOpenImmersion j₀.left]
    (_hij : Set.range i₀.left.base = (Set.range j₀.left.base)ᶜ)
    (L : ClosedLocalization Λ (localizationFiberMap D i₀) (localizationFiberMap D j₀)) :
    ∃ (hi : localizationFiberMap D i₀ ≫ (StrictWeil.modelFrobenius D X₀).hom =
          (StrictWeil.modelFrobenius D Z₀).hom ≫ localizationFiberMap D i₀)
      (hj : localizationFiberMap D j₀ ≫ (StrictWeil.modelFrobenius D X₀).hom =
          (StrictWeil.modelFrobenius D U₀).hom ≫ localizationFiberMap D j₀)
      (ei : L.closedPush ⋙ localizationAction Λ (StrictWeil.modelFrobenius D X₀) ≅
        localizationAction Λ (StrictWeil.modelFrobenius D Z₀) ⋙ L.closedPush)
      (er : L.exceptional ⋙ localizationAction Λ (StrictWeil.modelFrobenius D Z₀) ≅
        localizationAction Λ (StrictWeil.modelFrobenius D X₀) ⋙ L.exceptional)
      (ej : L.openPush ⋙ localizationAction Λ (StrictWeil.modelFrobenius D X₀) ≅
        localizationAction Λ (StrictWeil.modelFrobenius D U₀) ⋙ L.openPush),
      (mateEquiv L.closedPullPushAdjunction L.closedPullPushAdjunction
        (TwoSquare.mk _ _ _ _
          (L.closedPullExchange (StrictWeil.modelFrobenius D Z₀)
            (StrictWeil.modelFrobenius D X₀) hi).inv)).natTrans = ei.hom ∧
      (mateEquiv L.adjunction L.adjunction
        (TwoSquare.mk _ _ _ _ ei.inv)).natTrans = er.hom ∧
      (mateEquiv L.openPullPushAdjunction L.openPullPushAdjunction
        (TwoSquare.mk _ _ _ _
          (L.openPullExchange (StrictWeil.modelFrobenius D U₀)
            (StrictWeil.modelFrobenius D X₀) hj).inv)).natTrans = ej.hom ∧
      L.WeilTriangle (StrictWeil.modelFrobenius D Z₀) (StrictWeil.modelFrobenius D X₀)
        (StrictWeil.modelFrobenius D U₀) hj ei er ej := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
