## Worker report

The item is stated in `lean/Sheaf/Paper/ProEtaleConstructibleOrigin.lean`, namespace
`AlgebraicGeometry.ProEtale`, with principal theorem `constructible_proEtale_origin`.
Its conclusion is the explicitly defined proposition `ConstructibleOriginComparison`:
the two comparison-induced equivalences and equality of the two ambient object classes.
Nothing is proved. The main theorem and the canonical constant-ring comparison's
invertibility obligation have whole proofs `by sorry`; every other declaration has real data.
The invertibility obligation is a helper belonging to the coefficient identification in
this item, with its full universal-property proof plan in its docstring. Its inverse is
therefore uniquely determined, rather than chosen from an arbitrary existence theorem.

Hypothesis-by-hypothesis correspondence:

- The global finite-field datum is `(D : WeilConjectures.FiniteFieldDatum.{u})`; its
  fields retain the prime, positive exponent, cardinality and fixed algebraic closure.
- The coefficient prime is `(l : ℕ) [Fact l.Prime]` and `_hl : l ≠ D.p`.
- The finite extension is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. Its valuation ring and chosen uniformizer are
  precisely those used by the recorded `Padic.coefficientExtensionRing` construction.
- The positive finite level is `(n : ℕ) (hn : 1 ≤ n)`.
- The actual coefficient ring is `Padic.coefficientExtensionRing l E n`.
  Its finiteness is supplied explicitly by `Padic.finite_coefficientExtensionRing l E n hn`,
  rather than imposed as another hypothesis. Its lifted copy is `ULift.{u+1,u} B` in
  fixed-ring module sheaves, matching the recorded etale universe convention.
- The scheme is an arbitrary `(T : Scheme.{u})`. There is no finite type, Noetherian,
  quasi-compactness, quasi-separatedness or base-field structure hypothesis on T.

Clause-by-clause correspondence:

- The comparison morphism is the recorded `comparisonUpperStar`, as used by
  `finiteCoefficientComparison`; `originComparison` fixes its discrete coefficient topology.
  The associated-module-sheaf construction is the recorded `finiteCoefficientRealization`.
- Clause (i) is the first conjunct of `ConstructibleOriginComparison`. Its source is
  `ObjectProperty.FullSubcategory (Scheme.IsConstructibleEtaleModuleSheaf ...)`, using
  exactly the predicate of the recorded etale constructible-complex definition.
  Its target is `ObjectProperty.FullSubcategory
  (Scheme.IsConstructibleProEtaleModuleSheaf T B)`, with the dependency repair below.
  An equivalence `e` is accompanied by a natural isomorphism identifying its functor,
  after the full inclusions, with `originComparison ⋙ originConstantModules`.
  This natural isomorphism is in the category of modules over the constant ring sheaf,
  so it is linear for all sections of the coefficient ring, not merely additive.
- Clause (ii) is the second conjunct. Its source is the full subcategory of
  `Etale.DerivedCategory.isBoundedConstructible (ULift B) T`, using the recorded predicate
  and the same ambient category as `Etale.BoundedConstructibleDerivedCategory`.
  Its target is the full subcategory of `intrinsicOriginBoundedConstructible T B`.
  A natural isomorphism after the full inclusions identifies the equivalence functor
  with `originDerivedComparison`, definitionally the recorded
  `finiteCoefficientDerivedComparison` at the discrete lifted coefficient ring.
- Intrinsic bounded constructibility is defined as: for every `q : ℤ`, the cohomology
  sheaf, computed by `DerivedCategory.homologyFunctor (OriginModules T B) q`, satisfies
  the recorded intrinsic constructibility predicate after canonical scalar conversion;
  and `∃ a b : ℤ, a ≤ b ∧ ∀ q, (q < a ∨ b < q) → IsZero (H^q K)`.
  This is exactly constructible cohomology vanishing outside a finite degree interval.
- The final sentence is the third conjunct, equality of object predicates
  `intrinsicOriginBoundedConstructible T B = etaleOriginBoundedConstructible T B`.
  The latter unfolds to the recorded `isBoundedConstructibleFiniteCoefficient`.
  Both sides concern the SAME ambient `FiniteCoefficientDerivedCategory`, so this is
  equality of object classes, not just an abstract equivalence between unrelated categories.
- `originCoefficientRing`, `OriginModules`, `OriginDerivedCategory` and the comparison
  wrappers only instantiate existing constructions. `originConstantRingComparison` is the
  canonical sheafification comparison. `originCoefficientMap` is its inverse followed by
  the sheafified constant scalar map. `originConstantModules` is ordinary restriction of
  scalars along that map, leaving the additive sheaf unchanged. Thus no arbitrary map,
  arbitrary equivalence, or extra hypothesis replaces the specified coefficient identification.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, importing the recorded quotient and uniformizer.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules`, through `finiteCoefficientComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: the original small pro-etale site
  and constant-ring module encoding, retained by `proEtaleConstantRing` and its module category.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible` and its full subcategory.
- `Sheaf.Paper.ProEtaleConstructibleSheaf`:
  `Scheme.IsConstructibleProEtaleModuleSheaf`, with its own module repaired below.
- `def-weil-scheme-morphism-properties` is a convention node, not a declaration.
  The locally closed immersed partition is the existing `Scheme.LocallyClosedStratification`;
  constructibility is `Topology.IsConstructible`.
- The `mathlib_match` of `def-weil-derived-cohomology-sheaves` is
  `DerivedCategory.homologyFunctor`, read with its factorization on representing complexes
  in `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `finiteCoefficientRingSheaf`,
  `FiniteCoefficientModules`, `FiniteCoefficientDerivedCategory`,
  `finiteCoefficientScalarMap`, `finiteCoefficientComparison`,
  `finiteCoefficientDerivedComparison`, `isBoundedConstructibleFiniteCoefficient`.
- `lem-cbc-proetale-stalk-conservative` has no recorded Lean declaration in the base.
  It supplies proof locality and the warning mentioned in the node's explanatory last
  sentence. The item statement requires no stalk functor or locality theorem from it:
  the bounded constructible etale-origin object property is already supplied by
  `def-weil-pbc-proetale-modules`. No unstated object is used through this dependency.

The main theorem's docstring gives all nine proof steps, with their dependency IDs:
preservation, full faithfulness and the counit criterion, Zariski locality, closure under
extensions, induction on strata, reflection and sheaf equivalence, exactness on
cohomology, induction on amplitude, and equality of object classes. It explicitly avoids
using geometric-stalk conservativity for arbitrary pro-etale sheaves.

Edge cases checked before finalizing the statement:

- T may be empty. The positive-stratum convention admits an empty stratum; all geometric
  stalk conditions are then vacuous. The zero object is allowed on both sites.
- Empty strata, zero sheaves, and zero complexes are allowed. For a zero complex choose
  any interval with a ≤ b; its cohomology vanishes everywhere.
- The coefficient conversion and intrinsic predicate also make sense for a zero finite
  ring. The main theorem retains n ≥ 1 exactly as requested, and makes no extension to n = 0.
- The amplitude may have a = b. All integer degrees, including negative degrees, are used.
- Arbitrary disconnected and non-quasi-compact schemes remain included. No local-to-global
  replacement of the node's finite global stratification condition is made.
- The site retains object universe u+1 and morphism universe u; module values live in u+1.
  Finite extension fields and schemes can always be placed in one common universe by
  cumulativity. No equality of the site's object and morphism universes is imposed.
- The natural isomorphisms specify the actual inverse image, rather than merely asserting
  the existence of unrelated equivalences.

Searches performed:

- `msearch.py leanfinder`: “Pullback from the etale to proetale site induces an equivalence
  of constructible sheaves and bounded constructible derived categories”. Results were
  generic site equivalences, dense-subsite equivalences, and sheaf pullback constructions;
  no statement of this complete item.
- `msearch.py leansearch`: “equivalence constructible sheaves etale proetale finite
  coefficients”. The service returned UNAVAILABLE (Internal Server Error), recorded as
  unavailable, with no mathematical absence verdict based on that service.
- `msearch.py loogle`: “Functor.IsEquivalence, ObjectProperty.FullSubcategory”. The service
  returned zero hits with unknown unqualified identifier `Functor.IsEquivalence`.
  Direct source reads supplied the category interfaces used here.
- `msearch.py grep`: “constructible|Constructible” in `AlgebraicGeometry/Sites`, zero hits.
- `rg` in upstream `WeilConjectures`, the copied pro-etale framework, and `lean/Sheaf`
  found `ProEtale.isConstructible_iff_exists_isConstructibleSheaf_iso_comparisonUpperStar_obj`.
  Its complete declaration covers sheaf essential origin only, uses the distinct upstream
  predicate, and does not give clause (ii) or equality with the recorded intrinsic class.
  The upstream derived `boundedConstructible` is DEFINED by etale origin, so cannot supply
  the missing intrinsic comparison. Both source modules were read.
- The same search found `Scheme.finiteRing_constructibleSheaf_origin` in
  `Sheaf.Paper.FiniteRingConstructibleSheafOrigin`; its current server source was read with
  `scompile.py --source`. It covers clause (i) for general finite commutative rings but
  does not state the derived clause or equality of object classes, so no complete
  `existing: true` match exists for the item.
- Further exact-name searches found no existing `originCoefficientMap`,
  `ConstructibleOriginComparison`, or `intrinsicOriginBoundedConstructible` declaration.
- Stacks Tags 09AK and 09AL were opened directly because the cited literature checkout
  is not present locally. Their sheaf equivalence and derived comparison agree with the
  node's intent; the delivery retains the node's explicit bounded/global-partition version.

## Dependency modules

`def-weil-proetale-constructible-sheaf`: its recorded module said “constructible” in the
docstring but did not require constructibility of the partition's strata. Reading
`Scheme.LocallyClosedStratification` confirmed that it supplies local closedness and
immersion data only. On arbitrary schemes local closedness does not imply constructibility;
thus the original interface did not give the notion stated by this dependency node.
The delivery repairs that SAME module and declaration by adding
`(∀ i : Fin S.n, Topology.IsConstructible (S.stratum i))` after the original positive-stratum
condition. Every original condition, pullback and geometric-stalk quantifier is retained.
Only the dependency's `lean` record changes, with this reason in `lean.note`.
No dependency statement is corrected and no new definition node is introduced.

Proof import compatibility: `ComparisonPullbackCoherence`,
`ProEtaleExtensionZeroComparison`, `ComparisonDirectImage`, and
`ProEtaleOpenClosedSequence` cannot be imported together with the recorded ringed intrinsic
constructibility module: they pull in the `FiniteCoefficient.UpperLowerStar.Defs`
reorganization while the intrinsic module imports the original `UpperLowerStar.Defs`.
The compiler reports both declare `AlgebraicGeometry.ProEtale.«term(_)_*[_]»`.
Individual file probes isolated this failure for `ComparisonPullbackCoherence`;
removing the conflicting proof imports is the prescribed duplicate-import repair.
The compatible lisse-origin, finite-level, local-stratum and finite-ring-origin imports
remain. The missing open-closed and derived comparison proof imports are documented here
for the reader; their proof steps remain fully specified in the docstring.
The unstated `lem-cbc-proetale-stalk-conservative` and `thm-weil-pbc-site-comparison`
are used only as future proof dependencies, not as missing statement data.
The Mathlib proof leaves are imported through SingleTriangle, ExactFunctor,
HomologySequence, TStructure, Pretriangulated, and TruncLEGT.

Source pages read: [Stacks 09AK](https://stacks.math.columbia.edu/tag/09AK) and
[Stacks 09AL](https://stacks.math.columbia.edu/tag/09AL).

## Second reading by Q14

I read the node statement, its dependency signatures, the source place in the
blueprint, and Stacks Tags 09AK and 09AL before checking the Lean file. The
item-by-item rendering is:

- The fixed global datum is `D : WeilConjectures.FiniteFieldDatum`, with the
  prime `l` satisfying `[Fact l.Prime]` and `_hl : l ≠ D.p`; these are exactly
  the node's finite-field and `l ≠ p` hypotheses.
- The coefficient field is `E : Type u` with `[Field E]`, `[Algebra (Padic l) E]`
  and `[FiniteDimensional (Padic l) E]`. The recorded `Padic` construction
  supplies the valuation ring, chosen uniformizer, and quotient
  `Padic.coefficientExtensionRing l E n`; no additional finiteness hypothesis
  is assumed. The item has `n : ℕ` and `hn : 1 ≤ n`, exactly as the node.
- The scheme is the unrestricted `T : Scheme.{u}`. There is no finite-type,
  Noetherian, quasi-compact, separated, or characteristic hypothesis on `T`.
- Clause (i) is the first conjunct of `ConstructibleOriginComparison`: the
  full subcategory given by `Scheme.IsConstructibleEtaleModuleSheaf` is
  equivalent to the full subcategory given by
  `Scheme.IsConstructibleProEtaleModuleSheaf T B`. Its natural isomorphism
  identifies the equivalence with `comparisonUpperStar`, followed by the
  canonical coefficient realization and scalar restriction. This is the
  specified `ν_T^*`, rather than an unrelated equivalence.
- Clause (ii) is the second conjunct: the source is the full subcategory of
  `Etale.DerivedCategory.isBoundedConstructible`; the target is the full
  subcategory of `intrinsicOriginBoundedConstructible`. The latter requires
  constructibility of every `DerivedCategory.homologyFunctor` cohomology
  sheaf and an integer interval outside which every cohomology object is
  `IsZero`, so it includes all finite amplitudes and all integer degrees.
  Its natural isomorphism again identifies the functor with the recorded
  derived comparison.
- The final conjunct is equality of `intrinsicOriginBoundedConstructible`
  and `etaleOriginBoundedConstructible` on the same ambient finite-coefficient
  derived category, exactly the node's assertion that intrinsic and
  etale-origin readings have the same objects.

The edge cases are covered. The empty scheme is represented by a one-stratum
empty partition (the predicate requires a positive finite number of strata),
empty strata and zero sheaves/complexes remain allowed, and the coefficient
ring may be the zero quotient. The theorem retains `n ≥ 1`; it does not add an
`n = 0` case. The amplitude permits `a = b`, negative degrees, and arbitrary
finite intervals. Universes retain the small pro-etale object universe and
morphism universe convention through the `ULift` coefficient presentation;
no equality of those universes is imposed.

Searches were checked in the recorded `searches.jsonl`, with fresh reads of
the project and upstream sources. LeanFinder found only generic site and
sheaf-equivalence infrastructure; Loogle had no relevant hit; LeanSearch was
unavailable; grep found no constructible pro-etale sheaf or complete origin
theorem. The existing `finiteRing_constructibleSheaf_origin` covers only the
sheaf clause, while the upstream bounded-constructible definition is already
by etale origin, so neither is an exact match for this two-clause statement.
The Stacks pages confirm the sheaf equivalence (09AK) and derived equivalence
(09AL) for an arbitrary scheme and Noetherian coefficient ring; finite
coefficients satisfy that source condition.

No semantic mismatch remains in the main item: the worker's lifted finite
coefficient category and `originConstantModules` are the recorded canonical
transport from the finite-function coefficient sheaf to the constant-module
presentation, and the helpers are definitions with real data. The dependency
module `ProEtaleConstructibleSheaf` was already repaired in this delivery to
add `Topology.IsConstructible` for every stratum; I verified that this is the
only dependency-interface change and that all original clauses remain.
No Lean statement or definition required a further edit in this second
reading. Both sibling modules compile cleanly through `scompile.py` with no
warnings.
