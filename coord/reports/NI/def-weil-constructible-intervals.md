## Worker report

The module `Sheaf.Paper.ConstructibleIntervals` defines the object predicate
`AlgebraicGeometry.Scheme.finiteTorsionConstructibleIn` and the full category
`AlgebraicGeometry.Scheme.finiteTorsionConstructibleIntervalCategory`.
It contains real definitions only: no theorem, proof, axiom, or `sorry` is introduced.
The node is unchanged except for `lean`. No new nodes or dependency repairs are needed.

Source read: the original blueprint file
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-constructible-intervals.md`,
order 1466, obtained by reading the server copy (the literature archive is absent
from this read-only local checkout). Its displayed formula and surrounding text agree
with the node. The stage-1 clarification of inherited full-subcategory morphisms is
implemented by Mathlib's `ObjectProperty.FullSubcategory`.

Hypotheses and clauses, individually:

- A prime ell is `(l : ℕ) [Fact l.Prime]`.
- A finite extension E/Q_l is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`; the coefficient-extension dependency fixes
  the extended absolute value, valuation ring and chosen uniformizer.
- The positive integer level is `(n : ℕ) (hn : 1 ≤ n)`, including n = 1.
- The arbitrary scheme Y is `(Y : Scheme.{u})`.
- Ell invertible on Y is `_hl : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)` in
  the predicate and `hl` of that same type in the category. Invertibility of the
  canonical integer section is local, so this is exactly invertibility on Y.
  The formula does not otherwise use this hypothesis; it is retained as stated.
- Integer bounds and their ordering are `(a b : ℤ) (_hab : a ≤ b)` in the
  predicate, and `(a b : ℤ) (hab : a ≤ b)` in the category. The proof is passed
  unchanged to the predicate, with no strengthening to strict inequality.
- A is exactly `Padic.coefficientExtensionRing l E n`, the quotient
  `coefficientExtensionIntegers l E ⧸ coefficientExtensionIdeal l E n`;
  that ideal is the nth power of the span of the recorded uniformizer.
- The ambient derived category is `proEtaleDerivedCategory Y A`, using the
  constant ring sheaf on the small pro-etale site, with its existing universe lift.
- Membership in D^b_c is `intrinsicFiniteTorsionConstructible l E n hn Y`.
  Its definition imposes finite cohomological support and constructibility of
  every cohomology sheaf by finite locally closed constructible stratifications,
  locally constant restrictions and finite stalks. No etale-origin replacement is used.
- The displayed vanishing condition is `∀ r : ℤ, r ∉ Set.Icc a b → IsZero
  ((DerivedCategory.homologyFunctor (proEtaleRingModules Y
  (proEtaleConstantRing Y A)) r).obj K)`. This is precisely the dependency's
  cohomology functor on the same module category. `Set.Icc` includes both endpoints.
- `⊓` conjoins bounded constructibility and that vanishing predicate.
- `.FullSubcategory` supplies objects satisfying both conditions, with ambient
  morphisms and inherited identities and composition. Since D^b_c is itself full
  in the same derived category, these are exactly Hom in D^b_c as required.

Dependency declarations inspected and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, and its imported original
  `Sheaf.NumberTheory.Padics.CoefficientExtension` constructions, especially
  `Padic.coefficientExtensionRing`, `coefficientExtensionIdeal`, and
  `coefficientExtensionUniformizer` (their full definitions/docstrings were read).
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`,
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`. Its imported
  `FiniteTorsionConstructibility` and `ProEtaleConstructibleSheaf` definitions
  and `ProEtaleDerivedCategory` encoding were also read.
- Mathlib `Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`, for both
  the cohomology-sheaves leaf and the cohomological-support leaf. The support
  leaf's `DerivedCategory.isGE_iff` and `isLE_iff` were read: the displayed
  vanishing condition is exactly amplitude in the inclusive interval.
- Mathlib `CategoryTheory.InducedCategory`, `CategoryTheory.InducedCategory`,
  `inducedFunctor`, and `fullyFaithfulInducedFunctor`; and
  `CategoryTheory.ObjectProperty.FullSubcategory`,
  `ObjectProperty.FullSubcategory`, whose category instance uses that induced
  category and whose morphism wrapper carries exactly an ambient morphism.

Edge cases checked before writing: a = b allows cohomology in that one degree;
negative endpoints and intervals crossing zero are allowed; r = a and r = b
are not required to vanish, while r < a and b < r are; all-zero complexes satisfy
the amplitude condition; there is no nonemptiness hypothesis on Y, so on the empty
scheme the invertibility condition is vacuous as it should be. n = 1 is included,
n = 0 is excluded by the stated positive-level hypothesis. There is no added
finite-type, Noetherian, connectedness or finite-field-base assumption. The
universe convention is the recorded dependency interface, with every variable
and universe explicit and `autoImplicit false`.

Searches for an existing exact definition:

- `msearch.py`, LeanFinder: "Full subcategory of bounded constructible derived
  complexes with cohomology vanishing outside an inclusive integer interval".
  Eight hits: `DerivedCategory.IsGE`, `IsLE`, the standard t-structure and
  representative-bound lemmas. No intrinsic constructibility predicate.
- `msearch.py`, Loogle: `DerivedCategory.IsGE, DerivedCategory.IsLE`.
  Two representative lemmas, no constructible interval definition.
- `msearch.py`, grep: `constructib|homologyConcentratedIn`, scoped to
  `Algebra/Homology/DerivedCategory`. Zero Mathlib hits.
- `rg` in the source project: `constructibleIn|constructibleInterval|
  ConstructibleInterval|intrinsicFiniteTorsionConstructible`; and search for
  the blueprint id. Read both tagged upstream interval definitions and their
  surrounding docstrings/signatures. The etale version uses a different site;
  the pro-etale version uses the essential image of the etale derived category
  in a category of module-valued sheaves, rather than the recorded intrinsic
  ringed-module-sheaf predicate. These are not the identical notion/interface.
- Read upstream `DerivedCategory.homologyConcentratedIn`: this supplies the
  general amplitude condition via the t-structure, not constructibility.
  This delivery combines the existing intrinsic predicate with the explicit
  cohomology vanishing condition instead of recreating any cohomology functor.
- `rg` under `lean/Sheaf` found uses of `intrinsicFiniteTorsionConstructible`
  in finite-Tor and integral-coefficient modules, but no constructible interval
  category. `rg` of `finiteTorsionConstructibleIn|constructibleInterval` in
  `dag/lean_names_upstream.json`, Mathlib, the source project, and `lean/Sheaf`
  found no declaration-name conflict.

No statement fault or STATEMENT-DISPUTED finding.

Validation: the initial module passed `scompile.py` cleanly (sandbox probe and
library-name compile, 8.5 s and 11.9 s). The final module additionally imports
the coefficient dependency directly; `deliver2.py --no-push` recompiles it
and runs the current server preflight. No global build or delivery push is run.

## Second reading by NI

I independently opened the delivered node and both definitions, every direct
statement-dependency node, and the source declarations below. I also read the
original blueprint `def-weil-constructible-intervals.md`, order 1466, its unit's
`_section.md`, and `def-weil-finite-torsion-constructibility.md`, order 1454,
from the literature archive on the project server. The item's source is the
blueprint, not a Stacks theorem. I read Stacks `categories.tex`,
`definition-subcategory` (001D), for the full-subcategory clarification.
The source explicitly allows an arbitrary scheme with ell invertible; the
unit's hypotheses on morphisms do not add hypotheses to this definition.

The objects, hypotheses and clauses, matched independently:

1. Prime ell: `(l : ℕ) [Fact l.Prime]`. Exact.
2. Finite field extension E/Q_ell: `(E : Type u) [Field E]
   [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. Exact;
   these give precisely a finite-dimensional extension of the p-adic field.
3. Positive integral level: `(n : ℕ) (hn : 1 ≤ n)`. Exact positive-integer
   indexing, with no change in the lower bound.
4. Scheme Y and invertibility: `(Y : Scheme.{u})` and
   `∀ y : Y, IsUnit (l : Y.presheaf.stalk y)`. Exact: the canonical integer
   section is a unit iff it is a unit in each local ring. `_hl` in the
   predicate retains this hypothesis even though the formula is independent
   of the proof; the category passes `hl` to that predicate.
5. Bounds: `(a b : ℤ)` and `a ≤ b`, passed as `_hab`/`hab`.
   Exact non-strict ordering; no positivity imposed on either endpoint.
6. Coefficients: `Padic.coefficientExtensionRing l E n`. I read
   `CoefficientExtension.lean`: this is the quotient of the recorded valuation
   subring by `(Ideal.span {coefficientExtensionUniformizer l E}) ^ n`,
   hence precisely O_E/(varpi_E^n). `CoefficientExtensionFinite.lean`
   supplies finiteness at positive levels. Exact; no arbitrary coefficient
   ring or extra valuation structure is substituted.
7. Ambient objects: `proEtaleDerivedCategory Y
   (Padic.coefficientExtensionRing l E n)`. I read
   `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: the standard derived
   category of `SheafOfModules` over the constant ring sheaf on the small
   pro-etale site, with its coefficient lift. Exact.
8. K belongs to D^b_c: the left factor
   `intrinsicFiniteTorsionConstructible l E n hn Y`. I read its full body in
   `IntrinsicFiniteTorsionConstructibility.lean`, the original
   `FiniteTorsionConstructibility.lean`, and `ProEtaleConstructibleSheaf.lean`.
   It says finite support of cohomology and constructibility of every
   cohomology sheaf, using finite locally closed constructible strata,
   locally constant restrictions and finite geometric stalks. Exact recorded
   dependency, with no etale-origin replacement. The original global datum
   and l ≠ p parameters are unused in that predicate; the recorded intrinsic
   interface removes them and introduces no assumptions on Y.
9. Every degree outside the inclusive interval vanishes:
   `∀ r : ℤ, r ∉ Set.Icc a b → IsZero
   ((DerivedCategory.homologyFunctor (proEtaleRingModules Y
   (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))) r).obj K)`.
   Exact. I read `proEtaleRingModules` in `ProEtaleOperations.lean`,
   Mathlib's `homologyFunctor` and `homologyFunctorFactors`, and
   `DerivedCategory.isGE_iff`/`isLE_iff`. The functor is H^r of that same
   ringed-module category, not cohomology of global sections; `IsZero` means
   zero sheaf. `Set.Icc` includes both endpoints, so this is precisely the
   recorded cohomological amplitude condition.
10. Both object conditions hold simultaneously: the `⊓` in
    `finiteTorsionConstructibleIn` is pointwise conjunction. Exact.
11. Category and all morphisms: `.FullSubcategory` in
    `finiteTorsionConstructibleIntervalCategory`. I read Mathlib's
    `ObjectProperty.FullSubcategory`, its induced category instance and
    `InducedCategory.Hom`, identities and composition. Every morphism is one
    ambient morphism; identities and composition are inherited. Since the
    bounded constructible category is itself full in this ambient category,
    this gives exactly Hom in D^b_c, as the node requires. Exact.

Edge cases: `a = b`, negative endpoints and intervals crossing zero are
included. Degrees `a` and `b` need not vanish. The zero object has empty
cohomological support and satisfies the vanishing condition for every allowed
interval. The empty scheme is not excluded: invertibility is vacuous, and the
recorded finite-stratification interface permits an empty stratum, so its
positive number-of-strata convention does not exclude it. There is no separate
index-family binder in this item. `n = 1` is included and `n = 0` is excluded
exactly as in the source. There is no fixed characteristic, base field,
Noetherian, finite-type, nonempty or separated hypothesis. The common universe
`u` follows the recorded coefficient and scheme interfaces, and is arbitrary;
objects can be represented in a common larger universe. The small-site object
and morphism universes remain `u+1` and `u`, respectively, and coefficients and
modules use the existing `u+1` lift; no equality between those site universes
or additional smallness instance is imposed. `autoImplicit false` and the
explicit `universe u` leave no unbound variables.

Independent searches used different phrasings and checked the candidates:

- LeanFinder: "Full subcategory of finite constructible torsion sheaves in a
  derived category with cohomology supported in degrees between two integers".
  Eight results, only general `DerivedCategory.IsGE`/`IsLE` and representative
  bounds; no constructible interval.
- Loogle: `"homologyFunctor"`. General cohomology API, no exact interval
  category with intrinsic constructibility.
- LeanSearch: "Bounded constructible sheaf complexes with cohomology in a
  closed integer interval". Service returned Internal Server Error; recorded
  as unavailable, with no negative mathematical verdict inferred.
- `msearch.py` grep: `constructib|stratification` in
  `Algebra/Homology/DerivedCategory`: no hits. Direct `rg` of Mathlib's
  homological-algebra and module-sheaf sources and of `lean/Sheaf`, using
  `IsConstructible|constructibleIn|ConstructibleInterval|constructibleInterval`,
  found no exact definition. Declaration-name checks in Mathlib, the source
  project, `lean/Sheaf`, and `dag/lean_names_upstream.json` found no conflict.
- Direct source search and reading of
  `WeilConjectures.CategoryTheory.DerivedCategory.Constructible` and
  `WeilConjectures.SixFunctors.ProEtale.Derived.Constructible` found the
  tagged etale and pro-etale interval candidates. The first uses the etale
  site; the second uses etale origin and module-valued sheaves. Neither is
  the recorded intrinsic `SheafOfModules` construction. The generic upstream
  `DerivedCategory.homologyConcentratedIn` supplies amplitude alone, not this
  combined notion.
- I also read `coord/pefw-upstream-framework.md` and the exact newer
  `lean/WeilConjectures/ConstructibleSheaf/ProEtaleModule/DerivedCategory.lean`
  and `Def.lean`. Their bounded constructibility is for internal module
  objects with locally finite presentation on strata, with no matching
  interval definition or direct interface for this node. It is not silently
  substituted for the node's recorded finite-stalk predicate.

No mismatch was found. The Lean module and node record are unchanged; this
reading adds only this independent review. There are no new nodes, dependency
modules, statement corrections or citers requiring a correction audit. Both
definitions have real data, no theorem or `sorry` is introduced, and all three
docstrings identify the source and blueprint node. The node has no proof steps
because it is a definition. The record's `lean.statement` was checked with
`tools/stage2_delivery.py signature` and matches the file verbatim under the
project's signature convention. Compilation and the prescribed delivery
preflight are run after this review.
