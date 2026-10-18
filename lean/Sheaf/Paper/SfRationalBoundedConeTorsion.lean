/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.SfIntegralConstructibleLinear
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.CategoryTheory.ScalarLocalization

import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
/-!
# Bounded cohomological power torsion implies rational vanishing

Source: Weil blueprint main-20261015, sec-six-functors/sk-prop-sf-dualizable-biduality,
local bounded-complex argument and its rational supplement; Stacks Tags 05RU, 08J5,
0149 and 0118 (blueprint: lem-sf-rational-bounded-cone-torsion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

/-- A uniform power annihilating all cohomology of an integral constructible object
annihilates its identity after multiplication of the exponent by the interval length
plus one, and its image in raw rationalization is zero.
The scalar-torsion hypothesis is written as the cohomology functor applied to the
canonical scalar endomorphism: this is multiplication by the same constant section
on the cohomology sheaf, without choosing an additional module structure.
Source: Weil blueprint main-20261015, sec-six-functors/sk-prop-sf-dualizable-biduality,
local bounded-complex argument and rational supplement; Stacks Tags 05RU, 08J5,
0149 and 0118 (blueprint: lem-sf-rational-bounded-cone-torsion).

Proof:
1. The completed coefficient sheaf has its constant O_E scalars. The canonical
ambient action and the inherited full-subcategory action are those of
`lem-weil-integral-constructible-linear`; `lem-weil-linear-abelian-derived-category`
makes localization and shifts linear. Put r = uniformizer^N.
2. In the ambient derived category set K_q = tau_{<=q} C. By
`lem-weil-pbc-truncation-cohomology`, K_{u-1} is acyclic and hence zero, while
K_v -> C is a quasi-isomorphism and hence an isomorphism. No constructibility of
these intermediate truncations is needed.
3. By `lem-weil-pbc-truncation-triangle` there is a distinguished triangle
K_{q-1} -> K_q -> H^q(C)[-q] -> K_{q-1}[1]. Multiplication by r on the third
term is zero: it is already zero on its single nonzero cohomology term, and
localization and shifts preserve the scalar action.
4. Induct from q=u-1 to v. If s=r^(q-u) kills the identity of K_{q-1}, then
s id_{K_q} vanishes after precomposition with K_{q-1} -> K_q. Clause (i) of
`lem-weil-pbc-hom-out-of-triangle-exact` factors it through H^q(C)[-q].
Multiplication by r kills this factorization, proving r^(q-u+1) id_{K_q}=0.
5. Transport the equality at q=v across K_v isomorphic to C. Multiplying once
more by r gives uniformizer^(N*(v-u+2)) id_C=0. The inclusion is full and its
scalar structure is inherited, so this is the required ambient identity.
6. In the Hom tensor E description of `def-weil-rationalization-karoubi`, with
m=N*(v-u+2), tensor balancing gives id_C tensor 1 =
(uniformizer^m id_C) tensor uniformizer^(-m)=0. This also covers m=0.
An object with zero identity has every incoming and outgoing map zero, so its
rational image is a zero object. -/
theorem sfRationalBoundedConeTorsion
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{u})
    (_hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (C : sfIntegralConstructibleCategory l E X)
    (a b : ℤ) (_hab : a ≤ b) (N : ℕ)
    (_hBounds : ∀ d : ℤ, d ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor (scalarReductionSource l E X) d).obj C.obj))
    (_hTorsion : ∀ d : ℤ,
      (DerivedCategory.homologyFunctor (scalarReductionSource l E X) d).map
        ((Padic.coefficientExtensionUniformizer l E) ^ N • 𝟙 C.obj) = 0) :
    (Padic.coefficientExtensionUniformizer l E) ^ (N * (b - a + 2).toNat) •
        𝟙 C.obj = 0 ∧
      IsZero ((sfRationalConstructibleLocalization l E X).obj C) := by
  sorry

end WeilConjectures
