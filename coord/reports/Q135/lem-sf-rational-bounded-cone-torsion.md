## Worker report

The module `Sheaf.Paper.SfRationalBoundedConeTorsion` states
`WeilConjectures.sfRationalBoundedConeTorsion`, with its sole proof `sorry`.
It supplies no new definitions and changes only the item's `lean` record.
No statement correction, disputed statement, missing dependency, or node fault was found.

Clause-by-clause correspondence:

- A prime ell is `(l : ℕ) [Fact l.Prime]`.
- A finite extension E/Q_ell is `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. Its valuation ring and the uniformizer are the
  recorded `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionUniformizer l E`. These are the same fixed choices
  used to define the integral category, its reduction tower, and rationalization.
- The scheme is `(X : AlgebraicGeometry.Scheme.{u})`; ell invertible on X is
  `_hInv : ∀ x : X, IsUnit (l : X.presheaf.stalk x)`, the usual stalkwise
  criterion. No structure over a finite field or finiteness condition on X is added.
- The specified object C is `(C : sfIntegralConstructibleCategory l E X)`.
  Its underlying ambient derived object is `C.obj`. This is the full subcategory
  defined by derived completeness, constructible positive reductions, and their
  uniform finite amplitude. The ambient category is the derived category of
  modules over the inverse-limit completed coefficient sheaf, not the discrete
  constant integral sheaf.
- The integers u,v in the prose are renamed `(a b : ℤ)`, with `_hab : a ≤ b`.
  Nonnegative N is `(N : ℕ)`.
- Vanishing outside the closed interval is `_hBounds : ∀ d : ℤ,
  d ∉ Set.Icc a b → IsZero ((DerivedCategory.homologyFunctor
  (scalarReductionSource l E X) d).obj C.obj)`.
- Multiplication by uniformizer^N on every cohomology sheaf is zero precisely
  when `_hTorsion` holds: each `homologyFunctor ... d` maps
  `uniformizer ^ N • 𝟙 C.obj` to zero. The ambient linearity dependency fixes
  scalar multiplication to the actual constant-section action on complexes and
  its descent. Taking cohomology of that endomorphism is exactly multiplication
  by that same constant section on H^d(C). This is not the stronger assertion
  that uniformizer^N already kills the identity of C.
- The first conclusion is the equality
  `uniformizer ^ (N * (b - a + 2).toNat) • 𝟙 C.obj = 0`
  in the ambient completed-module derived category. Because a ≤ b, the integer
  b-a+2 is positive; `toNat` is exactly the natural exponent in the statement,
  not a change of its value.
- The second conclusion, conjoined with the first, is
  `IsZero ((sfRationalConstructibleLocalization l E X).obj C)`.
  This uses the specified integral-to-rational functor into the raw scalar
  localization. `IsZero` means precisely the object is zero (equivalently
  isomorphic to the existing zero object), without adjoining idempotents.

Dependency declarations read and used:

- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`, the currently recorded integral category.
- `Sheaf.Paper.CompletedIntegralCoefficientGerm`:
  `integralConstantToCompletion`, publicly importing
  `Sheaf.Paper.CompletedIntegralCoefficients` and its
  `completedIntegralCoefficientSheafUnrestricted`. The ambient category in
  `scalarReductionSource` uses exactly this completion.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory` and
  `sfRationalConstructibleLocalization`, raw localization with the unchanged
  objects and Hom tensor E coordinates.
- `Sheaf.Paper.SfIntegralConstructibleLinear`:
  `sfIntegralCoefficientLinear`, `sfIntegralConstructibleLinear`, and
  `sfIntegralConstructible_linear`, fixing the ambient and restricted scalars.
- Proof plan imports: `Mathlib.Algebra.Homology.DerivedCategory.Linear`
  (`DerivedCategory.instLinear`, `instLinearCochainComplexIntQ`,
  `instLinearShiftFunctorInt`); `Mathlib.Algebra.Homology.Embedding.CochainComplex`
  (`CochainComplex.quasiIsoAt_ιTruncLE`);
  `WeilConjectures.CategoryTheory.TruncationTriangle`
  (`DerivedCategory.truncation_triangle`, read through `scompile.py --source`
  because the older source checkout lacks this module);
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
  (`CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂`);
  and `Sheaf.CategoryTheory.ScalarLocalization`
  (`CategoryTheory.ScalarLocalization`, `ScalarLocalization.localization`).
- Cohomology is the existing `DerivedCategory.homologyFunctor` from
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`, with its factor
  comparison identifying it with cochain-complex cohomology. The derived category
  and linear-category notions are the recorded Mathlib declarations.

The theorem docstring carries all six DAG proof steps: constant-section linearity;
acyclic initial truncation and final quasi-isomorphism; successive truncation
triangle; Hom-exactness factorization and induction; the explicit exponent; and
tensor balancing to a zero rational identity. The source unit was opened in the
current main-20261015 snapshot. As the item's split report records, the scalar
induction is an extracted rational supplement, not a change to the unit statement.

Edge cases checked before writing: N=0 makes the torsion premise say each
cohomology identity is zero, hence C is acyclic; the conclusion's exponent is
also zero and correctly asks id_C=0. For a=b the exponent is 2N, a valid
(nonminimal) bound. Negative a,b work unchanged because the difference is
nonnegative and cohomology is indexed by ℤ. Zero C and the empty scheme are
included. No positivity of N or nonemptiness of X is assumed. The finite
truncation argument remains ambient, so no additional assertion that integral
constructible truncations exist is required.

Searches (2026-10-17):

- `msearch.py ... leanfinder`, query "In a bounded derived category a scalar
  annihilating all cohomology has a power annihilating the identity and its
  scalar localization is zero": eight hits, including `DerivedCategory.isLE_iff`,
  `isGE_iff`, and `isZero_of_isLE`; none asserts this lemma.
- `msearch.py ... loogle`, query `DerivedCategory, CategoryTheory.Linear`:
  ten hits on linear derived categories and functors; support for scalar actions,
  not the bounded nilpotence/rational vanishing assertion.
- `msearch.py ... grep`, query `annihilat|nilpoten|torsion`, directory
  `Algebra/Homology/DerivedCategory`: zero hits.
- `rg` in the upstream `WeilConjectures` and side `lean/Sheaf` trees for
  `rational-bounded-cone-torsion|bounded.*(torsion|annihilat)|annihilat.*identity`:
  only unrelated bounded torsion, torsion cohomology, and constructibility
  results. No existing statement found.
- `grep -rn lem-sf-rational-bounded-cone-torsion` in the upstream source:
  no hits. `rg sfRationalBoundedConeTorsion` in upstream names, upstream sources,
  side sources, and Mathlib: no naming collision.

Validation: the prescribed `scompile.py Q135 lem-sf-rational-bounded-cone-torsion`
compiled the sandbox form and the actual library module separately, cleanly,
with no errors or warnings. All variables and the universe are explicitly bound;
`autoImplicit` is false. The only postponed theorem is the assigned node itself.

## Second reading by Q135

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
