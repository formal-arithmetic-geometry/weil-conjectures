/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.Paper.CompactSupportRepresentativeIndependence

/-! # Normalized compact-support finite action

Source: blueprint order 1494, coherent strict-tower realization and rationalization
(blueprint: def-weil-compact-support-finite-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open TensorProduct
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients

section FiniteAction
variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The exact integral-functor predicate of the already recorded strict-tower realization.
The predicate retains the chosen tower, derived limit and projection normalizations.
Naming the predicate keeps the large proof-normalized realization out of later types.
Source: blueprint order 1494, proof steps 1--4
(blueprint: def-weil-compact-support-finite-action). -/
def SfCompactSupportFiniteRealizationSpec
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    (sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y) → Prop :=
  (fun {P : (sfIntegralConstructibleCategory l E X ⥤
      sfIntegralConstructibleCategory l E Y) → Prop} (_h : ∃ F, P F) ↦ P)
    ((exists_compactSupportRepresentativeComparison l
      E K₀ hl X Y f c).choose_spec.choose_spec.2.2.choose_spec.choose_spec
        |>.2.2.choose_spec.2)

/-- The integral realization package with its exact recorded predicate.
Source: blueprint order 1494, proof steps 1--4
(blueprint: def-weil-compact-support-finite-action).
Proof: project the integral-functor conjunct after the specified tower, evaluation,
right-derived limit, unit and Roos projections in
exists_compactSupportRepresentativeComparison. Unfold the named predicate; it is
exactly the predicate in that conjunct, with no added choice or normalization. -/
theorem sfCompactSupportFiniteRealization (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    ∃ F, SfCompactSupportFiniteRealizationSpec l K₀ hl c E F := by
  sorry

/-- The already normalized integral compact-support functor, retaining its coherent
strict-tower construction and the fixed projections of sfCompactSupportTerm.
Source: blueprint order 1494, proof steps 1--4
(blueprint: def-weil-compact-support-finite-action). -/
@[irreducible] def sfCompactSupportFiniteIntegralFunctor
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y :=
  (sfCompactSupportFiniteRealization l K₀ hl c E).choose

/-- Linearity of the fixed integral realization.
Source: blueprint order 1494, proof steps 3--4
(blueprint: def-weil-compact-support-finite-action).
Proof: project the additive and integral-linear conjuncts for the chosen integral
functor in sfCompactSupportFiniteRealization. -/
theorem sfCompactSupportFiniteIntegralFunctor_linear (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    (sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).Additive ∧
      (sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).Linear
        (Padic.coefficientExtensionIntegers l
          E) := by
  sorry

/-- The actual tensor extension of the fixed integral Hom map.
Source: blueprint order 1494, proof step 4
(blueprint: def-weil-compact-support-finite-action). -/
def sfCompactSupportFiniteHomMap (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K L : sfRationalConstructibleCategory l E X) :
    (K ⟶ L) →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l
      E)]
      ((⟨(sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K.obj⟩ :
        sfRationalConstructibleCategory l E Y) ⟶
        (⟨(sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj L.obj⟩ :
          sfRationalConstructibleCategory l E Y)) :=
  letI := (sfCompactSupportFiniteIntegralFunctor_linear l K₀ hl c E).1
  letI := (sfCompactSupportFiniteIntegralFunctor_linear l K₀ hl c E).2
  ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).mapLinearMap
    (Padic.coefficientExtensionIntegers l
      E)).baseChange
        (Localization.Away (Padic.coefficientExtensionUniformizer l
          E))

/-- The tensor Hom map preserves identities and composition.
Source: blueprint order 1494, proof step 4
(blueprint: def-weil-compact-support-finite-action).
Proof: on pure tensors, baseChange sends a tensor v to a tensor F(v). Apply the
integral functor laws and the prescribed tensor-composition formula. Extend by
additivity in both variables, since pure tensors generate the localized Hom modules. -/
theorem sfCompactSupportFiniteHomMap_laws (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    (∀ K : sfRationalConstructibleCategory l E X,
      sfCompactSupportFiniteHomMap l K₀ hl c E K K (𝟙 K) =
        𝟙 (⟨(sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K.obj⟩ :
          sfRationalConstructibleCategory l E Y)) ∧
    (∀ (K L N : sfRationalConstructibleCategory l E X) (a : K ⟶ L) (b : L ⟶ N),
      sfCompactSupportFiniteHomMap l K₀ hl c E K N (a ≫ b) =
        sfCompactSupportFiniteHomMap l K₀ hl c E K L a ≫
          sfCompactSupportFiniteHomMap l K₀ hl c E L N b) := by
  sorry

/-- The raw Hom scalar extension of the fixed integral action. Objects and all
morphisms are constructed explicitly; on pure tensors the map is a tensor F(v).
Source: blueprint order 1494, proof step 4
(blueprint: def-weil-compact-support-finite-action). -/
def sfCompactSupportFiniteFunctor (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y where
  obj K := ⟨(sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K.obj⟩
  map {K L} a := sfCompactSupportFiniteHomMap l K₀ hl c E K L a
  map_id K := (sfCompactSupportFiniteHomMap_laws l K₀ hl c E).1 K
  map_comp a b := (sfCompactSupportFiniteHomMap_laws l K₀ hl c E).2 _ _ _ a b

/-- The value equality retained in the fixed integral realization.
Source: blueprint order 1494, integral realization clause
(blueprint: def-weil-compact-support-finite-action).
Proof: project the object-normalization conjunct of the already recorded
exists_compactSupportRepresentativeComparison package used in the definition. -/
theorem sfCompactSupportFiniteIntegralFunctor_obj
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X) :
    (sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K =
      sfIntegralCompactSupportValue l E K₀ hl c K := by
  sorry

/-- The canonical n-th reduction comparison is the tensor/restriction adjoint of
the fixed n-th projection in the definition of sfIntegralCompactSupportValue.
Source: blueprint definition order 1490 and lem-fix-operation-reduction
(blueprint: def-weil-compact-support-finite-action). -/
def sfCompactSupportChosenReduction (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X)
    (n : ℕ) :
    (scalarReductionDerivedExtension l E
      Y n).obj (sfIntegralCompactSupportValue l
        E K₀ hl c K).obj ⟶
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l
      E (n + 1)) c).obj
        ((scalarReductionDerivedExtension l E X n).obj K.obj) := by
  letI : HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
    integralOperationsDerivedCountableProducts l E Y
  let h := (exists_isDerivedLimit_and_iso
    (sfCompactSupportTerm l E c K.obj) (sfCompactSupportTransition l E c K.obj)).1
  let hM : IsDerivedLimit (sfCompactSupportTransition l E c K.obj) (Classical.choose h) :=
    Classical.choose_spec h
  exact ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
    (Classical.choose hM ≫ Pi.π (sfCompactSupportTerm l E c K.obj) n)

/-- The specified projection adjunct is invertible, without an extra Tor or
finite-base-field assumption.
Source: definition order 1490; lem-fix-operation-reduction, compact-support paragraph
(blueprint: def-weil-compact-support-finite-action).
Proof: the source is the chosen derived limit of the actual compact-support tower.
Proper direct image commutes with the perfect two-term quotient tensor, and open
extension is exact and commutes with that tensor. These are the normalized unit/counit
mates. Their reduction cocycle identifies the displayed adjunct with the finite-level
comparison. The proper/open coefficient-change theorem makes it invertible. -/
theorem sfCompactSupportChosenReduction_isIso (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X)
    (n : ℕ) : IsIso (sfCompactSupportChosenReduction l K₀ hl c E K n) := by
  sorry

/-- Reduction of the fixed integral functor, using its actual value equality and
the uniquely specified projection adjunct, rather than a freely chosen isomorphism.
Source: definition order 1490; lem-fix-operation-reduction
(blueprint: def-weil-compact-support-finite-action). -/
def sfCompactSupportFiniteReductionIso (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X)
    (n : ℕ) :
    (scalarReductionDerivedExtension l E
      Y n).obj ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj ≅
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l
      E (n + 1)) c).obj
        ((scalarReductionDerivedExtension l E X n).obj K.obj) :=
  (scalarReductionDerivedExtension l E Y n).mapIso
      ((sfIntegralConstructible l E Y).ι.mapIso
        (eqToIso (sfCompactSupportFiniteIntegralFunctor_obj l K₀ hl c E K))) ≪≫
    @asIso _ _ _ _ (sfCompactSupportChosenReduction l K₀ hl c E K n)
      (sfCompactSupportChosenReduction_isIso l K₀ hl c E K n)


end FiniteAction
end WeilConjectures
