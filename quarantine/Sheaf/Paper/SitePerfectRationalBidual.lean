/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.SixFunctors.RationalVerdier
public import Sheaf.SixFunctors.RationalOperations
public import Sheaf.Paper.CompletedTensorHomTranspose
public import Sheaf.Paper.SitePerfectComplex

/-! # Canonical rational evaluation comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] WeilConjectures.rationalDerivedTensor
  WeilConjectures.rationalDerivedInternalHom WeilConjectures.podRationalClosed
  WeilConjectures.pullbackTensorRationalBraiding

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The coefficient bidual arrow is invertible for rational site-perfect objects.
The arrow is the transpose of the recorded evaluation after signed symmetry.
Source: blueprint lem-coef-rational-retract-evaluation, proof paragraph 3;
Stacks Tag 08JJ, with rational finite-projective local models
(blueprint: lem-coef-site-perfect-rational-bidual).

Proof: restrict completed evaluation and transposition to slices using exact
internal Hom restriction and the K-flat/Roos tensor model. On a bounded local
model, the degree-r bidual map is x ↦ (phi ↦ (-1)^r phi(x)). The unit is reflexive;
finite sums and split retracts remain reflexive, with inverse obtained by
restricting the inverse on the larger object. The signed shift and all three
triangle squares are supplied by coefficient bidual triangle compatibility.
Descending the finite stupid-truncation triangles proves invertibility locally,
without lifting the rational termwise splittings to integral ones. Write the
global rational map as an integral numerator divided by a uniformizer power,
and take its integral constructible cone. Refine the local models to a finite
affine pro-etale cover; in the empty case every sheaf is zero. Local rational
vanishing kills the local cone identities by finite uniformizer powers. Their
maximum kills every global cone cohomology sheaf by separatedness. Derived
completeness and exact countable products bound this cone's cohomology.
Hom exactness in a triangle shows that powers killing the two ends add to a
power killing its middle. Finite induction over the cohomological truncations
therefore kills the cone identity by some power. Inverting the uniformizer
makes the cone zero, proving invertibility of this actual global map. -/
theorem sitePerfect_rational_bidual
    (h : ∀ K M : sfRationalConstructibleCategory l E X,
      constructibleRationalHomPairs l E X (op K, M))
    (K : sfRationalConstructibleCategory l E X)
    (hK : IsSfRationalCoefficientSitePerfect l E X K) :
    IsIso ((@podRationalClosed l _ E _ _ _ X
      (RationalVerdier.units D l hl X)).transpose K
      ⟨(op ((RationalOperations.homDual l E X h
          (RationalOperations.coefficientUnit l E X D hl)).obj (op K)),
        RationalOperations.coefficientUnit l E X D hl), h _ _⟩
      ((@pullbackTensorRationalBraiding l _ E _ _ _ X
        (RationalVerdier.units D l hl X) K
        ((RationalOperations.homDual l E X h
          (RationalOperations.coefficientUnit l E X D hl)).obj (op K))).hom ≫
      (@podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)).evaluation
        ⟨(op K, RationalOperations.coefficientUnit l E X D hl), h _ _⟩)) := by
  sorry

end WeilConjectures
