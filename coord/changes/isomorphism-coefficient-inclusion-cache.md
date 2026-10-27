# isomorphismCoefficientInclusion

## Reason

The small coefficient model is `Shrink E`. Its algebra map is elaborated with the
separate `Shrink.instSemiring`, while the pullback and scalar APIs use the semiring
projected from `Shrink.instField`. Rechecking their equality repeatedly expands the
transferred structures. A checked header using an inclusion cached at the
field-induced semiring took 19.3 seconds, compared with 36--52 seconds before.
The helper is the original coefficientInclusion, with its existing algebraic
structures made explicit, so it changes no map or mathematical definition.
The existing public definitions remain in their original module. The new inclusion
cache is shared with the smaller statements through its own module, to avoid mixing
the original and field-structured presentations during kernel checking.
The integral unit and tower lemmas now share the original adapter definitions via
this same module, and the original public names alias those data. This eliminates
repeated kernel conversion between independently elaborated adapter expressions.
No scalar map, associator, unitor or coherence equation changes.

## Old

```lean
/-- The integral balancing associator, conjugated by the existing completion comparison
and the actual equality of the small coefficient inclusions. It introduces no new map.
Source: blueprint scalar-tower clause; prop-weil-pbc-scalar-extension
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
def isomorphismPullbackIntegralAssociator (W : Scheme.{u})
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E L h ⋙
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W L M k ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E M (h.trans k) :=
  sfIntegralScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
      (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k) ≪≫
    eqToIso (congrArg
      (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω M) · W)
      ((coefficientInclusion_laws l Ω).2 E L M h k))

/-- Identity scalar extension with its existing completion-unit normalization.
Source: blueprint identity-extension clause; lem-weil-scalar-extension-composition
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
def isomorphismPullbackIntegralUnitor (W : Scheme.{u}) (E : Index l Ω) :
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E E le_rfl ≅
      𝟭 (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) W) :=
  eqToIso (congrArg
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω E) · W)
    ((coefficientInclusion_laws l Ω).1 E)) ≪≫
  sfIntegralScalarUnit l (Coefficient.{u} l Ω E) W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime))

/-- Shift exactness and integral components of the already prescribed rational comparison.
There is no additional choice of a rational comparison.
Source: blueprint scalar-localization and shift clauses
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
def isomorphismPullbackRationalScalarLaws
    (S : ∀ E : Index l Ω,
      IsomorphismPullbackCoefficientStage l (Coefficient.{u} l Ω E) g hX hY)
    (E L : Index l Ω) (h : E ≤ L)
    (integral : constructibleIntegralPullback l (Coefficient.{u} l Ω E) g ⋙
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h ≅
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h ⋙
      constructibleIntegralPullback l (Coefficient.{u} l Ω L) g) : Prop :=
  isomorphismPullbackShiftSquare
    (rationalDerivedPullback l (Coefficient.{u} l Ω E) g)
    (sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h))
    (sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h))
    (rationalDerivedPullback l (Coefficient.{u} l Ω L) g)
    (S E).rationalShift
    (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h)
    (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h)
    (S L).rationalShift (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) g) ∧
  ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y,
      HEq ((rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) g).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).map
          (integral.hom.app K.obj))

attribute [local irreducible] isomorphismPullbackRationalScalarLaws

/-- The specified integral scalar comparison, with naturality on all integral arrows,
and exactness of it and its already-prescribed rationalization. Both endpoint shifts
are those of the same stage family, not independently chosen for each extension.
Source: blueprint scalar/shift paragraph; integral-operations scalar comparison
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
structure IsomorphismPullbackScalarComparison
    (S : ∀ E : Index l Ω,
      IsomorphismPullbackCoefficientStage l (Coefficient.{u} l Ω E) g hX hY)
    (E L : Index l Ω) (h : E ≤ L) where
  integral : constructibleIntegralPullback l (Coefficient.{u} l Ω E) g ⋙
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h ≅
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h ⋙
      constructibleIntegralPullback l (Coefficient.{u} l Ω L) g
  integral_normalization : ∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y,
    integral.app K = integralPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) g K
  integral_shift :
    (fun [_sE : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ]
      [_sL : (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ] ↦
        NatTrans.CommShift integral.hom ℤ)
      (_sE := (S E).integralShift) (_sL := (S L).integralShift)
  rational_laws : isomorphismPullbackRationalScalarLaws l Ω g hX hY S E L h integral

/-- The identity and tower equations for the same normalized comparison family.
Identity is expressed through the canonical scalar unitors, so that identity extensions
are included even in the unnormalized tensor presentation of the integral categories.
Source: blueprint final automorphism sentence, unit and tower clause
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
structure IsomorphismPullbackCoefficientCoherence
    (S : ∀ E : Index l Ω,
      IsomorphismPullbackCoefficientStage l (Coefficient.{u} l Ω E) g hX hY)
    (B : ∀ (E L : Index l Ω) (h : E ≤ L),
      IsomorphismPullbackScalarComparison l Ω g hX hY S E L h) : Prop where
  integral_unit : ∀ (E : Index l Ω)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (B E E le_rfl).integral.hom.app K ≫
        (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).map
          ((isomorphismPullbackIntegralUnitor l Ω Y E).hom.app K) =
      (isomorphismPullbackIntegralUnitor l Ω X E).hom.app
        ((constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).obj K)
  integral_tower : ∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X L M k).map
          ((B E L h).integral.hom.app K) ≫
        (B L M k).integral.hom.app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h).obj K) ≫
        (constructibleIntegralPullback l (Coefficient.{u} l Ω M) g).map
          ((isomorphismPullbackIntegralAssociator l Ω Y E L M h k).hom.app K) =
      (isomorphismPullbackIntegralAssociator l Ω X E L M h k).hom.app
          ((constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).obj K) ≫
        (B E M (h.trans k)).integral.hom.app K
  rational_unit : ∀ (E : Index l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω E) (coefficientInclusion l Ω E E le_rfl) g).hom.app K ≫
        (rationalDerivedPullback l (Coefficient.{u} l Ω E) g).map
          ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω Y E).hom.app K) =
      (GeneralAlgebraicallyClosedCoefficients.unitor l Ω X E).hom.app
        ((rationalDerivedPullback l (Coefficient.{u} l Ω E) g).obj K)
  rational_tower : ∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (sfRationalScalarExtension l (Coefficient.{u} l Ω L) X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω M)
          (coefficientInclusion l Ω L M k)).map
          ((rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) g).hom.app K) ≫
        (rationalPullbackScalarComparison l (Coefficient.{u} l Ω L)
          (Coefficient.{u} l Ω M) (coefficientInclusion l Ω L M k) g).hom.app
          ((sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h)).obj K) ≫
        (rationalDerivedPullback l (Coefficient.{u} l Ω M) g).map
          ((GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E L M h k).hom.app K) =
      (GeneralAlgebraicallyClosedCoefficients.associator l Ω X E L M h k).hom.app
          ((rationalDerivedPullback l (Coefficient.{u} l Ω E) g).obj K) ≫
        (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω M) (coefficientInclusion l Ω E M (h.trans k)) g).hom.app K

```

## New

The shared module defines the same inclusions and integral structural maps once.
The item preserves its original public imports and adds the public import of this
shared interface. Its existing adapter names are abbreviations of those same data.
The other existing definitions below retain their equations with the field-induced
structures explicit. All target signatures remain verbatim. The definition change
reopens semantic review for every target in this transitive closure, although the
presentations are definitionally equal.

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

/-! # Coefficient inclusions with explicit field-induced structures -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open AlgebraicallyClosedCoefficients
  (Index Coefficient coefficientInclusion coefficientInclusion_laws)

/-- Cache the existing coefficient inclusion with field-induced semiring structures.
Source: the finite-coefficient models of the current blueprint automorphism pullback;
`AlgebraicallyClosedCoefficients.coefficientInclusion` is used verbatim.
(blueprint: def-pod-isomorphism-coefficient-inclusions). -/
def isomorphismCoefficientInclusion
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E L : Index l Ω) (h : E ≤ L) :
    @AlgHom ℚ_[l] (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      inferInstance
      (show Field (Coefficient.{u} l Ω E) from inferInstance).toSemiring
      (show Field (Coefficient.{u} l Ω L) from inferInstance).toSemiring
      inferInstance inferInstance := coefficientInclusion l Ω E L h

/-- Identity and composition for the same field-structured inclusions.
Source: the existing coefficient-inclusion laws. Proof: apply those laws directly;
the map and algebra structures are definitionally equal presentations of the same data.
(blueprint: def-pod-isomorphism-coefficient-inclusions). -/
theorem isomorphismCoefficientInclusion_laws
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :
    (∀ E : Index l Ω, isomorphismCoefficientInclusion.{u} l Ω E E le_rfl =
      AlgHom.id ℚ_[l] (Coefficient.{u} l Ω E)) ∧
    (∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M),
      (isomorphismCoefficientInclusion.{u} l Ω L M k).comp
        (isomorphismCoefficientInclusion.{u} l Ω E L h) =
      isomorphismCoefficientInclusion.{u} l Ω E M (h.trans k)) := by
  exact coefficientInclusion_laws.{u} l Ω

section
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The integral balancing associator, conjugated by the existing completion comparison
and the actual equality of the small coefficient inclusions. It introduces no new map.
Source: blueprint scalar-tower clause; prop-weil-pbc-scalar-extension
(blueprint: def-pod-isomorphism-coefficient-inclusions). -/
def isomorphismCoefficientIntegralAssociator (W : Scheme.{u})
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E L h ⋙
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W L M k ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E M (h.trans k) :=
  sfIntegralScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (isomorphismCoefficientInclusion l Ω E L h) W 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
      (Coefficient.{u} l Ω M) (isomorphismCoefficientInclusion l Ω L M k) ≪≫
    eqToIso (congrArg
      (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω M) · W)
      ((isomorphismCoefficientInclusion_laws.{u} l Ω).2 E L M h k))

/-- Identity scalar extension with its existing completion-unit normalization.
Source: blueprint identity-extension clause; lem-weil-scalar-extension-composition
(blueprint: def-pod-isomorphism-coefficient-inclusions). -/
def isomorphismCoefficientIntegralUnitor (W : Scheme.{u}) (E : Index l Ω) :
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E E le_rfl ≅
      𝟭 (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) W) :=
  eqToIso (congrArg
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω E) · W)
    ((isomorphismCoefficientInclusion_laws.{u} l Ω).1 E)) ≪≫
  sfIntegralScalarUnit l (Coefficient.{u} l Ω E) W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime))

end

end WeilConjectures

/-- The integral balancing associator, conjugated by the existing completion comparison
and the actual equality of the small coefficient inclusions. It introduces no new map.
Source: blueprint scalar-tower clause; prop-weil-pbc-scalar-extension
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
abbrev isomorphismPullbackIntegralAssociator (W : Scheme.{u})
    (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E L h ⋙
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W L M k ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E M (h.trans k) :=
  isomorphismCoefficientIntegralAssociator l Ω W E L M h k

/-- Identity scalar extension with its existing completion-unit normalization.
Source: blueprint identity-extension clause; lem-weil-scalar-extension-composition
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
abbrev isomorphismPullbackIntegralUnitor (W : Scheme.{u}) (E : Index l Ω) :
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E E le_rfl ≅
      𝟭 (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) W) :=
  isomorphismCoefficientIntegralUnitor l Ω W E

/-- Shift exactness and integral components of the already prescribed rational comparison.
There is no additional choice of a rational comparison.
Source: blueprint scalar-localization and shift clauses
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
def isomorphismPullbackRationalScalarLaws
    (S : ∀ E : Index l Ω,
      IsomorphismPullbackCoefficientStage l (Coefficient.{u} l Ω E) g hX hY)
    (E L : Index l Ω) (h : E ≤ L)
    (integral : constructibleIntegralPullback l (Coefficient.{u} l Ω E) g ⋙
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h ≅
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h ⋙
      constructibleIntegralPullback l (Coefficient.{u} l Ω L) g) : Prop :=
  isomorphismPullbackShiftSquare
    (rationalDerivedPullback l (Coefficient.{u} l Ω E) g)
    (sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (isomorphismCoefficientInclusion l Ω E L h))
    (sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
      (isomorphismCoefficientInclusion l Ω E L h))
    (rationalDerivedPullback l (Coefficient.{u} l Ω L) g)
    (@IsomorphismPullbackCoefficientStage.rationalShift l _
      (Coefficient.{u} l Ω E) _ _ _ X Y g _ _ _ hX hY (S E))
    (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h)
    (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h)
    (@IsomorphismPullbackCoefficientStage.rationalShift l _
      (Coefficient.{u} l Ω L) _ _ _ X Y g _ _ _ hX hY (S L)) (rationalPullbackScalarComparison l
      (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h) g) ∧
  ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y,
      HEq ((rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h) g).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).map
          (integral.hom.app K.obj))

attribute [local irreducible] isomorphismPullbackRationalScalarLaws

/-- The specified integral scalar comparison, with naturality on all integral arrows,
and exactness of it and its already-prescribed rationalization. Both endpoint shifts
are those of the same stage family, not independently chosen for each extension.
Source: blueprint scalar/shift paragraph; integral-operations scalar comparison
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
structure IsomorphismPullbackScalarComparison
    (S : ∀ E : Index l Ω,
      IsomorphismPullbackCoefficientStage l (Coefficient.{u} l Ω E) g hX hY)
    (E L : Index l Ω) (h : E ≤ L) where
  integral : constructibleIntegralPullback l (Coefficient.{u} l Ω E) g ⋙
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h ≅
    GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h ⋙
      constructibleIntegralPullback l (Coefficient.{u} l Ω L) g
  integral_normalization : ∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y,
    integral.app K = integralPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h) g K
  integral_shift :
    (fun [_sE : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).CommShift ℤ]
      [_sL : (constructibleIntegralPullback l (Coefficient.{u} l Ω L) g).CommShift ℤ] ↦
        NatTrans.CommShift integral.hom ℤ)
      (_sE := (@IsomorphismPullbackCoefficientStage.integralShift l _
      (Coefficient.{u} l Ω E) _ _ _ X Y g _ _ _ hX hY (S E))) (_sL :=
      (@IsomorphismPullbackCoefficientStage.integralShift l _
      (Coefficient.{u} l Ω L) _ _ _ X Y g _ _ _ hX hY (S L)))
  rational_laws : isomorphismPullbackRationalScalarLaws l Ω g hX hY S E L h integral

/-- The identity and tower equations for the same normalized comparison family.
Identity is expressed through the canonical scalar unitors, so that identity extensions
are included even in the unnormalized tensor presentation of the integral categories.
Source: blueprint final automorphism sentence, unit and tower clause
(blueprint: lem-pod-isomorphism-pullback-texact-coefficients). -/
structure IsomorphismPullbackCoefficientCoherence
    (S : ∀ E : Index l Ω,
      IsomorphismPullbackCoefficientStage l (Coefficient.{u} l Ω E) g hX hY)
    (B : ∀ (E L : Index l Ω) (h : E ≤ L),
      IsomorphismPullbackScalarComparison l Ω g hX hY S E L h) : Prop where
  integral_unit : ∀ (E : Index l Ω)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (B E E le_rfl).integral.hom.app K ≫
        (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).map
          ((isomorphismPullbackIntegralUnitor l Ω Y E).hom.app K) =
      (isomorphismPullbackIntegralUnitor l Ω X E).hom.app
        ((constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).obj K)
  integral_tower : ∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X L M k).map
          ((B E L h).integral.hom.app K) ≫
        (B L M k).integral.hom.app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h).obj K) ≫
        (constructibleIntegralPullback l (Coefficient.{u} l Ω M) g).map
          ((isomorphismPullbackIntegralAssociator l Ω Y E L M h k).hom.app K) =
      (isomorphismPullbackIntegralAssociator l Ω X E L M h k).hom.app
          ((constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).obj K) ≫
        (B E M (h.trans k)).integral.hom.app K
  rational_unit : ∀ (E : Index l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω E) (isomorphismCoefficientInclusion l Ω E E le_rfl) g).hom.app K ≫
        (rationalDerivedPullback l (Coefficient.{u} l Ω E) g).map
          ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω Y E).hom.app K) =
      (GeneralAlgebraicallyClosedCoefficients.unitor l Ω X E).hom.app
        ((rationalDerivedPullback l (Coefficient.{u} l Ω E) g).obj K)
  rational_tower : ∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (sfRationalScalarExtension l (Coefficient.{u} l Ω L) X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω M)
          (isomorphismCoefficientInclusion l Ω L M k)).map
          ((rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h) g).hom.app K) ≫
        (rationalPullbackScalarComparison l (Coefficient.{u} l Ω L)
          (Coefficient.{u} l Ω M) (isomorphismCoefficientInclusion l Ω L M k) g).hom.app
          ((sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
          (isomorphismCoefficientInclusion l Ω E L h)).obj K) ≫
        (rationalDerivedPullback l (Coefficient.{u} l Ω M) g).map
          ((GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E L M h k).hom.app K) =
      (GeneralAlgebraicallyClosedCoefficients.associator l Ω X E L M h k).hom.app
          ((rationalDerivedPullback l (Coefficient.{u} l Ω E) g).obj K) ≫
        (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω M) (isomorphismCoefficientInclusion l Ω E M (h.trans k)) g).hom.app K

```

## Users

The refreshed downstream search found 676 transitive importers. Searches for every
changed definition name find references only in the item itself. The changes are
definitionally equal, so external statements retain their meanings and no source
adaptation is required. Claim labels below are the local snapshot; newly appearing
transitive importers have no source edits in this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IsomorphismPullbackTExactCoefficients | S5 | Same structural maps and types; shared presentation and proof assembly. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.ContinuousCoefficientGeometricCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.FiniteStageFibreVanishing | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.NormalizedContinuousCoefficientFamily | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.NormalizedStratifiedEmbeddedLattices | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.OrdinarySectionScalarComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicComparisonBridge | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicStrataBridge | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.FourierTransform.FourierDeligneTransform | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicClosureScalarCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicCommonStageFibreTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicCommonStageFibreZeroMap | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicCommonStageHeartExactness | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicCompletedProjectionShift | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicFibreComparisonCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicFibreComparisonData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicFiniteConstructibilityComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicFiniteRealizationCocone | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicFiniteRealizationData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicFiniteScalarCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicNormalizedFibreCommonStage | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicNormalizedFibreCommonStageData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicNormalizedFibreData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicNormalizedFibreExactness | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicNormalizedFibrePullback | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicNormalizedFibreScalar | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicProjectionShiftData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicPunctualWeights | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicRealizationFamilyData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicReindexingCore | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicReindexingFunctoriality | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicReindexingHom | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicReindexingTensor | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicTraceTensorShift | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AffineCurveHcZero | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AffineLineInvariance | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AffineSpaceProductDomain | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AffineSpaceTraceProductData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ArithmeticRoots | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AutomorphismConstructibleStageEquivalence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.AutomorphismSquareRationalScalar | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.BarrettIndRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ChernFlagFormula | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalFiltrationDiagramFibres | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalFiltrationExactDiagram | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalFrontierExistence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRawLisseCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonDescent | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonFibres | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestriction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonSystem | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRawLisseFiniteConstruction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRawLisseFiniteOperations | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRawLisseIntrinsicFibrePullback | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRawLisseOperations | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRawLissePointFibres | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRawLisseRealizationData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRawLisseScalarCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRealizationLocalSpectrum | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRealizationPunctualPurity | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalRealizedAnchorEigenvalue | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalSystemRawLisseRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalTwoFibreCommonData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalTwoFibreScalarData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalWeilCoherentDiagramStages | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationTransportData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalWeilFiniteDiagramDescent | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalWeilPrescribedIsomorphismLifts | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ClopenPrescribedWeilFiltration | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CommonAdicSectionData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CommonStageOpenHeartAdjunction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CompletedContinuousHomHypotheses | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CompletedLocalFibreComparisonData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CompletedPullbackFractionDescent | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CondensedOpenCoefficientModels | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CondensedOpenCounitComparisons | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CondensedOpenCounitUnits | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CondensedOpenUnitComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantDirectImageTowerRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantExtensionReturnData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantExtensionReturnExactFunctor | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalSpectra | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantExtensionReturnTransportComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantExtensionSheetGeometry | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstructibleMateCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstructiblePullbackTExact | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstructibleRationalHomComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstructibleTruncations | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ConstructibleWeilModelSquares | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CoordinateAdjunctionComposition | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CoordinateCartierBoundarySign | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CoordinateProductPresentations | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CoordinateSectionArrows | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CoordinateSectionProductRecursion | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CoordinateSectionProjection | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CoordinateSectionProjectiveTrace | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CoordinateSectionSiteTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CoordinateSectionTensorTrace | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CoordinateSupportedProductRecursion | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CoordinateZeroBaseChange | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.DerivedPoincarePairing | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.DerivedTensorRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.DualStalkFrobenius | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FieldCohomologyPerfectDescent | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FilteredCondensedCanonicalComparisons | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FilteredCondensedCounitBijective | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FilteredCondensedCounitFiniteFormula | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPairData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportGeometricSquares | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportSiteSquare | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteRationalHeartComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteSheafH0Augmentation | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FlagLocalComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FlagPullbackInjective | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FourierKernelConvolution | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FourierTraceFormula | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FrobeniusPullbackOrdinaryExchange | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.FrobeniusSystemExchangeInverse | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.GeometricCommonStageDirectImage | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.GeometricQuotientWeilCompositionSeries | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.GlobalIdentityNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.GlobalVerdierDualityData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.IdentityCompactificationSystemMate | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.IntegralLissePullbackNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.IntegralSectionsPerfectReduction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.IntegralSemilinearGermSquare | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.IsomorphismFieldTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.KummerSiteCohomologyNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseExtensionInertia | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseFieldNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseLatticeChoiceExistence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseLatticeHeartLift | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseLatticeHeartLiftData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseLatticeLisseDescent | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseLatticeNormalizedRealizations | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseLatticeRealizationFaithful | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseLatticeSingleComparisons | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LissePointNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LissePointSectionsRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LissePullbackNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseRationalRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseTensorNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealizationData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCoefficients | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionAssociativity | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeScalarTower | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeTransportAddition | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeTransportNaturality | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeWeilAddition | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LocalFrobeniusStepCompatibility | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LocalizedTopChern | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.MixedCupCoefficientChange | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.MixedCupCoefficientSquare | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.MixedCupFieldCoordinates | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.MixedCupFieldNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.MixedCupFieldOperations | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.MixedCupOperationComparisons | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.MixedCupRingedNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.MixedCupTensorClosure | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.MixedCupTensorComparisons | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.MixedCupTensorElementary | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.MixedCupTensorNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NativeAdicFiniteNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NativeAdicRealizationData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NativeAdicReindexingData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NativeAdicTensorReindexing | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NormalizedHeartRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NormalizedLatticeFiniteFree | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NormalizedPullbackCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NormalizedPullbackNaturality | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.NormalizedPullbackObjects | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.OpenWeilCarrierRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.OpenWeilCoefficientFibres | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.OpenWeilFiniteStageFrobenius | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.OpenWeilGeometricFibres | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.OpenWeilPunctualSpectrum | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.OrientationCoordinateBoundaryPullback | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.OrientationCoordinateModelBoundary | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.OrientationLocalResidue | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PointRealizationStandardCohomology | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PointScalarPunctualSpectrum | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PointWeilAlgebraicFlag | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PointWeilHeartFlag | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PointWeilHeartFlagData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PointWeilPairingCoordinates | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PointWeilPairingRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PointWeilTensorRepresentatives | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PointWeilTransportUnitShift | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ProperSupportCoefficientAdjunction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ProperSupportFiniteAdjunction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ProperWeilIterateGermFormula | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurAdicReconstruction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurCoordinateRepresentingFamily | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPairData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurIntegralSupportComparisonData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurIntegralSupportDerivedComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurSupportPresentationAlpha | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurityAffineLineBoundaryRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurityChernClasses | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurityGysinStructure | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurityKummerTriangleConcentration | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurityRelativeKummer | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalAmbientPullComposition | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalAmbientPullModels | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalBalancedFreePullback | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalContinuousComparisonCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalContinuousFiltrationModels | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalContinuousPullbackTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalModuleRealizationFunctor | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalOrdinaryCohomologyTensor | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalPullSingleComputation | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalRealizationFiniteConeModels | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalRealizationHomTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalRealizationPullbackComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalRealizationScalarCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalScalarBalancedLocalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalScalarCompletionUnitSquare | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalScalarMixedUnitCancellation | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalStalkExact | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalStratumPullbackData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalStratumPullbackModels | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RealWeights | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ReconstructedBrownMateLaws | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ReconstructedRefinementCommon | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ReconstructedRefinementSingleDegree | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ReconstructedRefinementTraceSquare | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ReconstructedRefinementTraceTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RefinementFiniteOriginEvaluation | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RelativeKummerSiteNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RelativeKunneth | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RelativeKunnethClosedFibre | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RelativeKunnethConstructions | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ScalarFibreCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ScalarFibreComponentData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ScalarFibreComponents | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ScalarFibreNaturality | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SectionsRationalModelComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SemilinearCommonOrdinaryCubes | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SemilinearCommonRefinementCubes | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SemilinearCommonSupportCubes | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SemilinearExchangeCubeData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SemilinearFieldOperationLifts | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SemilinearGermIterationDescent | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SemilinearRationalOrdinaryCubes | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SemilinearRationalRefinementCubes | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SemilinearRationalSupportCubes | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SfAdicCommonStageDescentEquivalence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SfQbarLocalizationCommonStage | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SfRecollementReductionBoundary | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TensorHeartSpecialization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TensorHomExchange | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwFrobeniusAction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCore | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionSign | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.VectorBundleThom | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.VectorBundleThomClass | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.VerdierHomChainCompositionData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilFourierInversion | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilGenericLissity | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilGeometricFiberProperties | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilIndOpenRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilIndOpenRepresentability | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilIndProperHigherRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilIndProperHigherRepresentability | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilIndProperOpenHigher | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilPullbackFibreReturn | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionPunctualSpectrum | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionStalkConjugacy | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlImmersionFilteredReductionTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlImmersionRestrictionAssembly | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlOpenExtensionAssembly | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlSfPbcNormalizedHeartModel | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlShriekComposition | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlWeilPullCompositorEquivariance | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunctionData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescent | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentIsIso | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyRealizationTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCoefficient | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCompletion | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateDescent | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateFinite | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateIntegral | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.RamifiedScalarPreparation | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.RamifiedScalarSupportCompatibility | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.SupportedWeilMateLift | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftCoherence | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.TraceFormula.CompactDirectPowerTransportNormalization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.TraceFormula.FrobeniusCompactPowerExchange | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.TraceFormula.LocalNormalizationStrictRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.WeilSheaf.DualRealizationComparison | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | not recorded in local snapshot | Transitive importer; no direct reference or adaptation. |

## Status

landed 20261026T002644-L-105314 2026-10-26 (merge of deliver/S5/Sheaf.Paper.IsomorphismPullbackTExactCoefficients)
