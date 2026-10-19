## Worker report

The item is stated in `Sheaf.Paper.RestrictionDirectImage`, with main declaration
`AlgebraicGeometry.ProEtale.restrictionDirectImage`. The module also states
`AlgebraicGeometry.ProEtale.finiteCoefficientBoundedConstructible_isTriangulated`, the
triangulated closure needed for the actual continuous-function finite-coefficient
presentation. Both proofs are `by sorry`. Dependency definitions are imported from the published
library; this delivery contains only the item module and its node record.

The theorem renders the node's hypotheses as follows. `A : Type (u + 1)` with
`[CommRing A] [IsNoetherianRing A]` is the commutative Noetherian coefficient ring;
`I : Ideal A`, `hI : I.FG`, and `htorsion : IsAddTorsion (A ⧸ I)` give the finitely
generated ideal and additive torsion quotient. The family
`[hfinite : ∀ m : ℕ+, Finite (A ⧸ I ^ (m : ℕ))]` gives finite positive quotients, and
`hperfect` gives the recorded `DerivedCategory.IsPerfectRingComplex` predicate for
each quotient in degree zero. The positive level is `n : ℕ+`, with coefficient ring
literally `A ⧸ I ^ (n : ℕ)`.

The schemes and map are `{S T : Scheme.{u}}` and `f : S ⟶ T`; only
`[IsNoetherian T]`, the finite-dimensional bound
`hdim : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞)`, and the local-order
condition `horder` are assumed. `c : ℕ` is the specified nonnegative bound, and
`hfin` is exactly the two-clause `ConstructibleDirectImageFiniteness` predicate from
the dependency definition. The explicit topology and discrete-topology binders on the
finite quotient provide the coefficient assumptions required by the recorded module
category.

For the conclusion, `FiniteCoefficientBoundedConstructibleDerivedCategory V Λ` is the
strictly full subcategory of the ambient finite-coefficient derived category whose
objects have bounded constructible etale origin, exactly the node's `Dbc`. The first
part of the result supplies `h`, proving the ambient derived direct image maps every
source object to the target subcategory. Mathlib's `ObjectProperty.lift` then gives a
functor on the full subcategories whose composite with the inclusion is the ambient
`finiteCoefficientDerivedDirectImage`; its `IsTriangulated` conjunct records the exact
triangulated restriction and hence its action on every morphism and distinguished
triangle. The second part quantifies over every source object `K` and every integers
`a,b`; the hypothesis says its cohomology vanishes outside `[a,b]`, and the conclusion
says the image vanishes outside `[a,b+c]`. Thus `a>b`, zero objects, and all integer
endpoints remain allowed.

The helper theorem's proof docstring records the finite-ring comparison argument: the
etale constructible class is weak Serre after common finite stratifications, exact
comparison preserves it, and the bounded derived essential image is triangulated.
The item proof docstring records the FIN argument: degree-zero images have no negative
cohomology, FIN bounds their positive cohomology by `c`, and successive truncation
triangles give the interval shift and bounded constructibility. The direct-image
functor is the published ordinary K-injective right derived functor.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, `FiniteCoefficientBoundedConstructibleDerivedCategory`,
  `isBoundedConstructibleFiniteCoefficient`, and `finiteCoefficientDerivedComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage` (published
  `def-weil-pbc-proetale-operations` interface): canonical connected-component
  coefficient maps, `finiteCoefficientModuleDirectImage`,
  `finiteCoefficientDerivedDirectImage`. The item module exposes its canonical
  shift and triangulated structures with `inferInstanceAs` from the existing generic
  right-derived-functor instances; these are real data, not postponed proofs.
- `Sheaf.AlgebraicGeometry.ConstructibleDirectImageFiniteness` (the published
  interface for `def-weil-pbc-constructible-direct-image-finiteness`):
  `IsConstructibleFiniteCoefficientSheaf`,
  `finiteCoefficientHigherDirectImage`, and the two-clause
  `ConstructibleDirectImageFiniteness` predicate.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` through the finite-module
  construction; Mathlib's `Scheme`, `Ideal`, `IsNoetherianRing`, `topologicalKrullDim`,
  `DerivedCategory.IsPerfectRingComplex`, `DerivedCategory.homologyFunctor`,
  `ObjectProperty.lift`, and `Functor.IsTriangulated`.

Edge cases checked: the zero and unit ideals, zero coefficient ring, empty schemes,
zero sheaves, `q=0`, `c=0`, negative cohomological degrees, and `a>b` are all admitted.
No properness, finite type, separation, nonempty scheme, positive number of strata, or
extra Noetherianity of `S` was added. The small-site object/Hom universe distinction is
preserved.

Searches for an existing statement or definition (2026-10-15 UTC):

- `msearch.py ... leanfinder` for a finite-cohomological-dimension direct image preserving
  bounded constructibles: eight generic derived T-structure hits, no exact statement.
- `msearch.py ... loogle` for `Functor.IsTriangulated, ObjectProperty.FullSubcategory`:
  the service reported unknown `Functor.IsTriangulated`, so this was not treated as a match.
- `msearch.py ... grep` for `constructible.*(rightDerived|directImage)|rightDerived.*constructible`:
  no hits in the source library; direct `rg` likewise found no exact declaration.
- `msearch.py ... leansearch` for a uniform constructible direct-image bound: unavailable
  (Internal Server Error), recorded as unavailable rather than a match.
- Whole-DAG and source searches found no existing declaration for this item. The nearby
  intrinsic `proEtale_bounded_constructible_isTriangulated` uses a different ULift
  constant-ring presentation and a different constructibility predicate, so it is not
  reused as the item's statement; the dependency-module repair preserves it by public
  import and adds the actual finite-coefficient interface.

No statement correction or `STATEMENT-DISPUTED` finding. The repaired single-file compile and delivery dry run are recorded below.


## Returned delivery repair

The return identified a duplicate `AlgebraicGeometry.ProEtale.ConstructibleDirectImageFiniteness`
in the immutable delivery and `Sheaf.Paper.ConstructibleDirectImageFiniteness`.
I checked the current published source using `scompile.py --source`: the Paper module is
no longer published, while `Sheaf.AlgebraicGeometry.ConstructibleDirectImageFiniteness`
is published and contains exactly the original finite-coefficient definition and its
helpers. The shared node now records that same module. Consequently I removed the
sandbox's duplicate FIN module and dependency node record, and retained the item's
public import of the published AlgebraicGeometry module. No declaration was renamed
and no second FIN predicate was introduced.

The canonical finite-coefficient direct-image module has also been published since the
returned delivery. I removed its stale sandbox module and dependency node record too,
so this delivery does not overwrite the newer published interface (which also includes
the canonical pullback construction). The item uses the recorded existing dependencies
through imports. Its mathematical statement, hypotheses, and interval clause are unchanged.

Searches during repair: `rg` over the shared `lean/Sheaf` tree and the upstream
`WeilConjectures` tree for `ConstructibleDirectImageFiniteness`, `restrictionDirectImage`,
and `finiteCoefficientBoundedConstructible_isTriangulated`; inspection of the current
DAG dependency records; and `scompile.py --source` for both FIN module paths and the
canonical finite-coefficient direct-image module. The published AlgebraicGeometry FIN
module is an exact match, including the actual continuous-function coefficient sheaf,
etale-origin constructibility, ordinary direct image, and the fixed uniform bound.
The prior semantic LeanFinder/Loogle/grep searches remain recorded above and in
`searches.jsonl`. There is no new statement correction or disputed statement.

The two canonical ambient instances previously carried by the removed sandbox operations
module are exposed in the item module as `finiteCoefficientDerivedDirectImage_commShift`
and `finiteCoefficientDerivedDirectImage_isTriangulated`. Both use `inferInstanceAs`
on the generic right derived functor of the published module direct image; they introduce
no new operation or theorem and are listed in the item node's `lean.declarations`.

Validation after repair: `scompile.py Q18 prop-weil-pbc-restriction-direct-image`
compiled the final item module successfully both under the sandbox module name and
its library module name, with no warnings or errors (9.8 s and 15.3 s respectively).
The first two attempts encountered server temporary-overlay creation failures with
`OSError: [Errno 28] No space left on device`; the final prescribed local-overlay
compilation succeeded. The node's recorded signature is verbatim from the final file,
all Lean lines are at most 100 characters, and only the item module and item node remain
in this delivery. The independent second reader must reread this repaired version.

## Second reading by Q18

I opened the node `prop-weil-pbc-restriction-direct-image`, its source note (blueprint
order 1302, with Stacks Tags 09C1, 09C2, 09C7, 095U and 0GL0), the final module, and
the three dependency declarations. The item-by-item comparison is:

* The coefficient datum object `A` is rendered as `A : Type (u + 1)` with
  `[CommRing A] [IsNoetherianRing A]`; `I : Ideal A` and `hI : I.FG` render the
  finitely generated ideal; `htorsion : IsAddTorsion (A ⧸ I)` renders additive
  torsion; the instance `∀ m : ℕ+, Finite (A ⧸ I ^ (m : ℕ))` and `hperfect` render
  the finite and perfect positive quotients. This is exactly the datum required by
  the FIN dependency, not an additional mathematical hypothesis.
* The level object `n : ℕ+` and the coefficient expression
  `A ⧸ I ^ (n : ℕ)` render `Λ = P_n`. The two local `letI` binders give the required
  discrete finite-level coefficient topology.
* The schemes and morphism are `{S T : Scheme.{u}}` and `f : S ⟶ T`, matching
  `u : S → T`; `[IsNoetherian T]`, `hdim`, and `horder` render precisely the target
  Noetherian, finite-dimensional, and local additive-order hypotheses required by
  FIN. There is no properness, finite-type, separation, or Noetherian hypothesis on
  `S`.
* `c : ℕ` is the specified nonnegative bound and
  `hfin : ConstructibleDirectImageFiniteness ... f c` is exactly
  `FIN(u, Λ; c)` from the dependency module, including its two clauses.
* The first conclusion clause is rendered by the witness `h`, which sends every
  `FiniteCoefficientBoundedConstructibleDerivedCategory S Λ` object into the target
  object property, followed by `ObjectProperty.lift` on the composite of the source
  inclusion and `finiteCoefficientDerivedDirectImage f Λ`. Its `.IsTriangulated`
  conjunct is the exact triangulated restriction of the ambient direct image; the
  canonical ambient shift and triangulated instances are explicitly exposed in the
  same module.
* The final clause quantifies over every source object `K` and every `a b : ℤ`, assumes
  `IsZero` homology for every `i < a ∨ b < i`, and concludes `IsZero` target homology
  for every `i < a ∨ b + (c : ℤ) < i`. This is exactly the interval `[a,b+c]`, with
  the quantifier order and strict endpoint inequalities preserved.

The edge cases in the worker report remain admitted by the signature: zero and unit
ideals, the zero coefficient ring, empty schemes, zero objects, `c = 0`, negative
cohomological degrees, and `a > b` are not excluded; `n` is positive as required by
the source datum. The small-site coefficient universe is retained (`A` and quotients
at `u + 1`, schemes at `u`).

For the H4 search I reran the prescribed `msearch.py` searches for a finite
cohomological-dimension direct-image restriction (LeanFinder), the triangulated full
subcategory pattern (Loogle), and constructible/right-derived declarations (grep),
and inspected the project and source trees with `rg`. LeanFinder returned only generic
derived T-structure declarations, Loogle returned no exact `Functor.IsTriangulated`
match, and grep returned no exact constructible direct-image theorem. The existing
FIN, finite-module, and finite-coefficient direct-image declarations are the canonical
dependency interfaces and are imported directly; no duplicate notion is introduced.

No mismatch was found in the node-to-Lean comparison, so no statement or module change
was needed. The only prior worker repair (removing stale duplicate FIN and direct-image
copies after the published AlgebraicGeometry interfaces appeared) was checked again:
the final module imports those canonical declarations and contains only the three
ambient/restriction declarations listed by the item node. `scompile.py` compiled the
module under both the sandbox and library names with no errors or warnings, and the
node's `lean.statement` is verbatim the theorem signature.
