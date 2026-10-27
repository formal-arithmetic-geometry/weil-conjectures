/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.CanonicalTateComparisons
public import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
public import Sheaf.SixFunctors.SchemeGeometricFrobenius
public import Sheaf.SixFunctors.FrobeniusSquareCartesian
public import Sheaf.Paper.CartesianCoefficientTwists
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.OrientationIntegralCoefficientTwists
public import Sheaf.Paper.IntegralTwistBaseChange
public import Sheaf.Paper.SignedTwistReductionComparison
public import Sheaf.Paper.CanonicalTateScalarNaturality

/-! # Canonical Tate naturality: ArrowNaturality

Source: current blueprint, def-pur-tate-datum, canonical root-arrow comparisons.
Existing declarations are retained in this compilation subdivision.
(blueprint: lem-pur-canonical-tate-arrow-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures.CanonicalTate
open FrobeniusCoefficientTwists

attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived
attribute [local irreducible] HasDerivedCategory.standard
  integralPull finitePull rationalPull commonPull
  integralProduct finiteProduct rationalProduct commonProduct
  proEtaleRingModulePullback proEtaleRingModuleAdjunction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
private local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- All four coefficient stages and whole strict quotient systems.
Source: blueprint canonical Tate naturality and additivity
(blueprint: lem-pur-canonical-tate-arrow-naturality). -/
def allStageLaws (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {X Y : Scheme.{u}}
    (w : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X) [IsIso g] [IsIso g']
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (h : g' ≫ w = w ≫ g) : Prop :=
  (∀ n : ℕ, finiteGeometricLaws l E w g g' h n) ∧
    integralGeometricLaws l E w g g' h ∧ rationalGeometricLaws l E w g g' h ∧
    commonGeometricLaws l Ω w g g' h ∧ strictGeometricLaws l E w g g' h ∧
    rootTowerLaws l w g g' h

/-- The geometric base change of the model morphism, with no smoothness assumption.
Source: blueprint finite-field conventions and arbitrary model pullback
(blueprint: lem-pur-canonical-tate-arrow-naturality). -/
def geometricMap (D : FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀))} (w₀ : X₀ ⟶ Y₀) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map w₀).left

/-- The statement specialized to the geometric Galois Frobenius of the given models.
Instances of prime invertibility come from the finite-field conventions themselves.
Finite level n denotes positive exponent n+1, so every quotient exponent occurs.
Source: blueprint def-pur-tate-datum, canonical Tate factors in the purity composite
(blueprint: lem-pur-canonical-tate-arrow-naturality). -/
def geometricTateLaws (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (w₀ : X₀ ⟶ Y₀) : Prop := by
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI : ∀ y : (D.geometricFiber Y₀).left,
      Invertible (l : (D.geometricFiber Y₀).left.residueField y) :=
    fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  exact allStageLaws l E Ω (geometricMap D w₀) (D.geometricFrobenius Y₀).hom
      (D.geometricFrobenius X₀).hom (D.frobenius_square_cartesian X₀ Y₀ w₀).2.2.2.2.1 ∧
    allStageLaws l E Ω (𝟙 (D.geometricFiber Y₀).left)
      (D.geometricFrobenius Y₀).hom (D.geometricFrobenius Y₀).hom
      ((Category.comp_id _).trans (Category.id_comp _).symm) ∧
    coefficientLaws l E (D.geometricFiber X₀).left (D.geometricFrobenius X₀).hom ∧
    coefficientLaws l E (D.geometricFiber Y₀).left (D.geometricFrobenius Y₀).hom ∧
    strictCoefficientLaws l E (D.geometricFiber X₀).left (D.geometricFrobenius X₀).hom ∧
    strictCoefficientLaws l E (D.geometricFiber Y₀).left (D.geometricFrobenius Y₀).hom ∧
    (∀ (r s : ℕ) (p : ℤ),
      (((2 * (s : ℤ)) * p).negOnePow : ℤ) = 1 ∧
        (((2 * (r : ℤ)) * (2 * (s : ℤ))).negOnePow : ℤ) = 1)

/-- The proposition collecting the non-arithmetic canonical Tate clauses. -/
def geometricTateCoreProp (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (w₀ : X₀ ⟶ Y₀) : Prop := by
  letI : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI : ∀ y : (D.geometricFiber Y₀).left,
      Invertible (l : (D.geometricFiber Y₀).left.residueField y) :=
    fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  exact allStageLaws l E Ω (geometricMap D w₀) (D.geometricFrobenius Y₀).hom
      (D.geometricFrobenius X₀).hom
      (D.frobenius_square_cartesian X₀ Y₀ w₀).2.2.2.2.1 ∧
    allStageLaws l E Ω (𝟙 (D.geometricFiber Y₀).left)
      (D.geometricFrobenius Y₀).hom (D.geometricFrobenius Y₀).hom
      ((Category.comp_id _).trans (Category.id_comp _).symm) ∧
    coefficientLaws l E (D.geometricFiber X₀).left
      (D.geometricFrobenius X₀).hom ∧
    coefficientLaws l E (D.geometricFiber Y₀).left
      (D.geometricFrobenius Y₀).hom ∧
    strictCoefficientLaws l E (D.geometricFiber X₀).left
      (D.geometricFrobenius X₀).hom ∧
    strictCoefficientLaws l E (D.geometricFiber Y₀).left
      (D.geometricFrobenius Y₀).hom

/-- The non-arithmetic clauses of the canonical Tate laws.
Source: the geometric, coefficient and strict-system clauses of the canonical Tate
naturality composite (blueprint: lem-pur-canonical-tate-arrow-naturality-core).
Proof: the finite, integral, rational, common-stage, strict-system and root-tower
identities are established by the corresponding canonical comparison calculations;
the final parity identities are intentionally separated into the elementary
arithmetic lemma used by `canonicalTateArrowNaturality`.
-/
theorem geometricTateCore (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (w₀ : X₀ ⟶ Y₀) :
    geometricTateCoreProp l E D hl Ω X₀ Y₀ w₀ := by
  sorry

private theorem geometricTateSigns :
    ∀ (r s : ℕ) (p : ℤ),
      (((2 * (s : ℤ)) * p).negOnePow : ℤ) = 1 ∧
        (((2 * (r : ℤ)) * (2 * (s : ℤ))).negOnePow : ℤ) = 1 := by
  intro r s p
  constructor
  · have he : Even ((2 * (s : ℤ)) * p) := by
      refine ⟨(s : ℤ) * p, ?_⟩
      ring
    simpa using (Int.negOnePow_eq_one_iff _).2 he
  · have he : Even ((2 * (r : ℤ)) * (2 * (s : ℤ))) := by
      refine ⟨(r : ℤ) * (2 * (s : ℤ)), ?_⟩
      ring
    simpa using (Int.negOnePow_eq_one_iff _).2 he

/-- Naturality, coefficient naturality, additivity and the mixed identity for the
canonical roots-of-unity Tate Weil arrows, including strict quotient systems.
Source: current blueprint def-pur-tate-datum, source-of-purity composite
(blueprint: lem-pur-canonical-tate-arrow-naturality).

Proof:
1. The geometric Frobenius square commutes on both fibre-product projections,
by lem-weil-frobenius-square-cartesian. The inverse-image root adjuncts commute
under the unit-normalized compositor: on a local unit both paths are pullback of
that same unit along the composite projection.
2. These identities commute with every root power transition. Projecting to each
finite root level proves the limit identity. Only Frobenius inverse image needs
to commute with the inverse limit, since it is an equivalence. Tensoring with
constant coefficients gives the line square on each scalar/root generator.
3. Coefficient extension sends (t tensor a) tensor b to t tensor ab, so it commutes
with the root comparison. Finite quotients, completed scalar extension and
successive coefficient extensions all preserve this formula. In a ramified
extension use a sufficiently large source quotient for each target quotient;
enlarging that source exponent gives the same map.
4. The lines are locally free of rank one, including the coefficient unit at zero.
Their degree-zero single complexes are flat K-flat models. Exact inverse image,
the universal quotient counits and the specified completed augmentation identify
the geometric and coefficient equations with these ordinary generator equations.
5. Concatenating root tensors gives alpha. The canonical tensor/pullback comparison
sends a tensor of unit sections to their tensor. Consequently both additive paths
send every ordered scalar/root tensor to the same concatenated tensor.
6. The equations hold on the whole strict quotient complexes, since the maps
commute with every quotient transition. The normalized Roos realization preserves
them, with its zero second coordinate. This uses completed-operation tower
substitution and integral-operations well-definedness, not separate choices of maps.
7. Rationalization preserves these equations. At a finite common coefficient stage
the same rational equations hold; the normalized scalar cocycles identify them
under every enlargement, so they descend to the recorded common-stage category.
8. Tensor the spatial square with the first Tate arrow, use naturality of mu,
and then additivity to obtain the mixed equation with exactly the displayed
inverse C and twist comparison. The case of an empty root list is the unit.
9. In shifted-tensor-morphism-calculus the signs are (-1)^(bp) and (-1)^(ab).
For b=2s and a=2r both exponents are even. Thus every indicated sign is one,
also at ell=2. The twist complexes themselves are concentrated in degree zero. -/
theorem canonicalTateArrowNaturality (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (w₀ : X₀ ⟶ Y₀) : geometricTateLaws l E D hl Ω X₀ Y₀ w₀ := by
  rcases geometricTateCore l E D hl Ω X₀ Y₀ w₀ with ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, geometricTateSigns⟩

end WeilConjectures.CanonicalTate
