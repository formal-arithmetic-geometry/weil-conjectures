## Worker report

The module `Sheaf.RingTheory.RegularFibreLocalPerfect` states
`DerivedCategory.isPerfect_and_tensor_homology_vanish_of_regular_closed_fibre`,
with its sole proof `sorry`. No definitions, helper nodes, or dependency repairs
are needed. The node is unchanged except for its `lean` record.

Source read: `literature/stacks-project/more-algebra.tex`,
`lemma-perfect-over-regular-local-ring`, Tag 09PC, including all four assumptions
and the proof. The node uses the explicitly allowed residue-field version of
assumption (4). Its conclusion and dimension shift agree exactly with the source.

The correspondence, hypothesis by hypothesis and clause by clause:

- The nonzero commutative local rings R and B are `{R B : Type u}`,
  `[CommRing R] [CommRing B] [IsLocalRing R] [IsLocalRing B]`.
  `IsLocalRing` extends `Nontrivial`, so nonzero is included without another assumption.
- The homomorphism is `(φ : R →+* B)`. The inverse-image condition is exactly
  `hlocal : (IsLocalRing.maximalIdeal B).comap φ = IsLocalRing.maximalIdeal R`.
- Flatness is `hflat : φ.Flat`, the recorded `RingHom.Flat`.
- The closed fibre is the actual quotient
  `B ⧸ (IsLocalRing.maximalIdeal R).map φ`; `Ideal.map` is the extended ideal m_R B.
  Its regular locality is `hregular : IsRegularLocalRing (...)`.
- The dimension is `d : ℕ` and `hd : ringKrullDim (...) = (d : WithBot ℕ∞)`.
  Thus it is finite and nonnegative; zero dimension is permitted.
- The object is `K : DerivedCategory (ModuleCat.{u} B)` and pseudo-coherence is
  `hK : K.IsPseudoCoherent`, using the dependency's bounded-above finite-free predicate.
- The base residue field k is `R ⧸ IsLocalRing.maximalIdeal R`.
  It is regarded as an R-module by `ModuleCat.of R (...)` and placed in degree zero
  using `(singleFunctor (ModuleCat.{u} R) 0).obj`.
- Restriction of K from B to R is `(ModuleCat.derivedRestrictScalars φ).obj K`.
  Its tensor with k[0] is precisely K tensor_R^L k as an underlying R-derived object.
  The exact restriction functor and K-flat monoidal tensor are existing constructions;
  no arbitrary map, resolution, or comparison is assumed.
- The integers and their ordering are `(a b : ℤ) (hab : a ≤ b)`.
  The hypothesis `hfibre` quantifies over every integer i and requires
  `IsZero ((homologyFunctor ... i).obj (...))` whenever `i < a ∨ b < i`.
  These are cohomological indices because the category localizes cochain complexes.
  Vanishing as an R-module is equivalent to vanishing as a k-module.
- The first conclusion `K.IsPerfectRingComplex` is exactly the recorded bounded
  finite-projective-model predicate, with no change in localization or coefficients.
- The second conclusion quantifies over every `N : ModuleCat.{u} B` and `j : ℤ`.
  `K ⊗ (singleFunctor ... 0).obj N` is K tensor_B^L N. Its cohomology vanishes when
  `j < a - (d : ℤ) ∨ b < j`, exactly the claimed Tor interval [a-d,b].
- Neither R nor B has an `IsNoetherianRing` binder. The closed fibre's regularity
  includes its own Noetherianity, as required by the source.

The two `HasDerivedCategory.{u} (ModuleCat.{u} ...)` binders express the existing
small-Hom derived categories; their canonical existence comes from the published
Grothendieck module-category framework. They impose no algebraic condition.
The common ambient universe u can contain both rings and all module objects under
consideration. There is no independent lower universe for test modules.

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, with module notion `Module.Flat`.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, the ring clause of
  def-weil-regular-scheme's retained `mathlib_match`. The scheme-specific declaration
  `AlgebraicGeometry.IsRegularScheme` is unnecessary for this ordinary-ring statement.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` (publicly available through
  the regular-local import).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `Q` (publicly available through the model predicates).
- `WeilConjectures.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`:
  `CategoryTheory.MorphismProperty.kFlat`, publicly reached through the existing
  `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory` construction.
  That module's monoidal instance computes tensor products on K-flat representatives.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, the dependency's recorded general predicate.
- `WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange`:
  `ModuleCat.derivedRestrictScalars`, the existing exact restriction to the derived category.
- `DerivedCategory.homologyFunctor` and `DerivedCategory.singleFunctor` are the existing
  cohomology and degree-zero embedding functors, publicly imported by the dependencies.

All stated proof dependencies are imported privately for stage 3: bounded-flat K-flatness,
ordinary derived change of rings, regular-local finite global dimension, ordinary Tor,
the bounded tensor-Tor spectral sequence, and the maximal-fibre perfection criterion.
The declaration docstring records all five proof steps and these node ids.

Edge cases checked before writing: d = 0 leaves [a,b] unchanged; a = b is allowed;
the zero complex and zero test module satisfy the vanishing statements; endpoints a-d
and b are not excluded; all negative cohomological degrees are included via ℤ.
For k → k[[x]] and K = k in degree zero, d = 1 and [a,b] = [0,0], so the bound is
[-1,0], matching the two degrees of the derived residue tensor. The identity of a
local ring has field closed fibre and d = 0. Zero rings are intentionally excluded
by the node itself. No finite-generation condition is imposed on test N.

Searches for an existing statement (2026-10-24; raw wrapper entries in searches.jsonl):

- LeanFinder: "A pseudo coherent complex over a flat local ring map with regular closed
  fibre and bounded derived residue fibre is perfect with Tor amplitude bounded by the
  dimension of the closed fibre". Eight hits on standard smoothness and ordinary module
  freeness; none states the derived perfection theorem.
- Loogle: `"PseudoCoherent", "Perfect"`; zero hits.
- LeanSearch: "A pseudo coherent complex over a flat local ring map with regular closed
  fibre is perfect if its derived residue fibre has bounded cohomology". Eight hits,
  including `Module.free_of_flat_of_isLocalRing` and `RingHom.Flat.propertyIsLocal`;
  none matches the derived statement or its dimension shift.
- msearch grep: `pseudo.?coherent|regular.*fibre.*perfect|regular.*fiber.*perfect|perfect.*closed.*fib`;
  zero Mathlib hits.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  the node id, regular-fibre perfection phrases, and the proposed declaration name:
  only ordinary regular-fibre results and the proof citation in
  `FlatQuotientNestedRegularIdeals.lean`; no matching theorem or name collision.
- rg for scalar restriction in the module-derived sources located the existing
  `ModuleCat.derivedRestrictScalars`; its exact definition and signature were read.

Validation: scompile.py compiled this delivered module in both sandbox and library
modes, each in 1.7 seconds, with no compiler errors or warnings.
No statement dispute or node fault was found.

## Second reading by N5

A separate second pass was made by the same worker, respecting the dispatcher's
instruction not to start other agents; this is not represented as an independent review.
I reopened the node and final Lean file and checked the flat local map, exact maximal-ideal
comap equality, the actual closed-fibre quotient, regular locality, finite dimension d,
pseudo-coherence, and the base residue tensor separately. In particular, the hypothesis
uses the base residue field R/m_R after restricting K, while the conclusion uses arbitrary
B-modules. The lower endpoint is a-d and the upper endpoint remains b, with strict
outside-interval inequalities in both places. Perfectness uses the recorded dependency
predicate. Locality supplies nonzero rings, and no Noetherian hypotheses on R or B appeared.
All variables and the universe are explicit under `autoImplicit false`; there are no
file-local notations, instances, helper assumptions, or hidden let binders. No mismatch
was found and no mathematical correction was needed. The sole postponed proof is the
named theorem belonging to this node.
