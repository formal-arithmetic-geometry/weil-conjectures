# Q43 — lem-sf-integral-compact-support-constructible

## Worker report

This delivery states `WeilConjectures.sfIntegralCompactSupport_constructible` in
`Sheaf.Paper.SfIntegralCompactSupportConstructible`. It uses the actual chosen
compactification, its finite-level extension by zero followed by proper derived
pushforward, the canonical quotient transitions, and an arbitrary Roos-triangle
derived limit. The earlier attempt's ordinary direct-image object has been removed.
The theorem proof is `sorry`; definitions contain real constructions. The docstring
records all eight steps of the DAG proof, including transition and unit compatibility.

Hypotheses and clauses are rendered as follows:

- The base field is `(K₀ : Type u) [Field K₀]`. The two schemes have `Over` structures
  over `Spec (.of K₀)` and `LocallyOfFiniteType` and `QuasiCompact` structure maps.
  These two properties together mean finite type, without any separatedness assumption
  on either structure map.
- The map `f : X ⟶ Y` has `f.IsOver (Spec (.of K₀))`, `IsSeparated f`,
  `LocallyOfFiniteType f`, and `QuasiCompact f`.
- The prime and its invertibility are `(l : ℕ) [Fact l.Prime]` and
  `IsUnit (l : K₀)`. The coefficient field is `(E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. Its valuation ring, chosen
  uniformizer and quotient rings are the existing `Padic.coefficientExtensionRing`.
- `c : Compactification f` contains the open immersion `c.i`, proper map `c.g`,
  and their factorization. `sfAmbientCompactSupportCandidate A c` is exactly
  `(sfIntrinsicExtensionByZero c.i A).mapDerivedCategory ⋙
  proEtaleConstantDerivedDirectImage c.g A`.
- `K : DerivedCategory (scalarReductionSource.{u,u} l E X)` is a complex over
  the completed coefficient sheaf, not the discrete constant valuation ring.
  `sfIntegralConstructible l E X K` gives its derived completeness, every
  constructible finite reduction, and one interval containing all reductions.
- The natural index `n` consistently means exponent `n+1`. Thus every positive
  coefficient exponent occurs, and the first exponent is one. `scalarReductionDerivedExtension
  l E X n` is the canonical K-flat-normalized derived tensor with that quotient.
- `sfCompactSupportTerm l E c K n` is precisely
  `Res_n (R(c.g)_{*,n} c.i_! (K tensor^L A_{n+1}))`.
- `sfCompactSupportReductionTransition` is the adjunct, under the higher
  reduction/restriction adjunction, of the lower reduction unit transported through
  the identity-on-sections composite restriction comparison. The normalized unit
  identifies this on a K-flat representative with `id tensor quotient`.
- `sfCompactSupportTransition` applies the higher-level candidate to that reduction
  map, follows it by `sfCompactSupportRestriction`, applies higher-level completed
  restriction, and then identifies the two restrictions by
  `sfCompactSupportDerivedRestrictionComp`. This is the exact transition specified
  by the node; it is neither an unspecified map nor an ordinary-image transition.
- `[HasProduct (sfCompactSupportTerm l E c K)]` exposes the product used by the
  recorded definition `CategoryTheory.IsDerivedLimit`. The assertion applies to
  every product choice and every object `M` satisfying that Roos-triangle predicate;
  it does not choose a preferred derived limit or impose boundedness on it.
- The conclusion `sfIntegralConstructible l E Y M` expands to
  `IsSfDerivedComplete l E Y M` and integers `a ≤ b` such that for every `n`
  the actual finite reduction is `intrinsicFiniteTorsionConstructible` and its
  `proEtaleCohomologicalSupport` is contained in `Set.Icc a b`. This includes each
  clause of the concluding sentence and uses a single interval, independent of `n`.

Dependency declarations used (full signatures and docstrings were read):

- Scheme properties: Mathlib `AlgebraicGeometry.LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated`, `Scheme.Over`, and `Hom.IsOver`, following the
  convention node `def-weil-scheme-morphism-properties`.
- `WeilConjectures.Compactification.Refinement`: `AlgebraicGeometry.Compactification`
  and its existing refinement/category interface, imported through the candidate.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its imported `CoefficientExtension` gives
  `Padic.coefficientExtensionRing` and `Padic.coefficientExtensionTransition`.
- `Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint`:
  `AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate`.
  `ProEtaleIntrinsicExtensionByZero` supplies `sfIntrinsicModuleEquivalence` and
  `sfIntrinsicExtensionByZero`, using the existing finite intrinsic realization.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`
  and its full-subcategory interface; `SfDerivedComplete` supplies
  `IsSfDerivedComplete`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionSource`, `scalarReductionTarget`, `scalarReductionRestriction`,
  `scalarReductionRestriction_exact`, `scalarReductionDerivedRestriction`,
  `scalarReductionDerivedExtension`, and
  `derivedScalarExtensionRestrictionAdjunction`. The adjunction is normalized on
  every K-flat representative; selecting it therefore does not select arbitrary data.
- `Sheaf.Paper.CompletedIntegralCoefficients`:
  `completedIntegralCommRingSheafUnrestricted`,
  `completedIntegralCommRingProjectionUnrestricted`, and `integralCoefficientSheaf`.
  The unrestricted completion is the same inverse limit as the recorded completion;
  its construction does not require a global finite-field datum.
- `Sheaf.Paper.SfIntegralReductionTower`: `sfDerivedReductionUnit`.
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars`:
  `proEtaleCoefficientRestrictScalars`, its exactness instances,
  `proEtaleCoefficientDirectImageComparison`, and
  `proEtaleDerivedDirectImage_restrictScalars`. The last fixes the comparison on
  K-injective representatives, including the resolution map after restriction.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars`:
  `Sheaf.restrictCoextendScalarsAdj`; the fixed-coefficient open comparison is the
  uniqueness isomorphism of the resulting left adjoints, with its adjunction units.
- `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`:
  `Functor.mapDerivedCategorySquareIso`; the exact-functor interfaces give
  `mapDerivedCategoryCompIso` and `mapDerivedCategoryNatIso`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimit`, using the established Roos triangle.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.

Edge cases checked: the empty source or target and zero complexes are allowed;
no nonemptiness, positive dimension, nonzero cohomology, or separated structure-map
hypothesis was introduced. The zero complex admits any interval, including `[0,0]`.
Exponent zero is not a level of this tower. Arbitrary positive ramification and arbitrary
finite extensions `E/ℚ_l` are allowed. Positive-characteristic base fields satisfy
precisely the stated invertibility condition; characteristic zero is allowed. Neither
finite Tor amplitude nor perfectness was added. The fixed compactification is actually
used. The conclusion concerns every derived limit, including arbitrary isomorphic choices.
The coefficient-site universe is `u+1`, while morphisms of the small pro-etale site
remain in universe `u`; no equality of those universes is imposed.

Searches for an existing statement:

- `msearch.py`, LeanFinder, “compact support direct image commutes with restriction
  of scalars for finite rings”: eight `Finsupp` support results, no sheaf comparison.
- `msearch.py`, Loogle, `CategoryTheory.Functor.mapDerivedCategory`: exact descent
  infrastructure, not the compact-support constructibility theorem.
- `msearch.py`, grep, `compactSupport.*construct|lowerShriek.*construct`: no Mathlib hit.
- Earlier sandbox logs also contain LeanFinder searches for integral compact-support
  constructibility and proper-support adic pushforward; these returned module completion,
  local cohomology and constructible-subset statements. Loogle searches combining
  `DerivedCategory`, `constructible`, `SheafOfModules`, `pushforward` found no exact match.
- LeanSearch, “integral compact support constructibility adic reduction tower”:
  service unavailable (`Internal Server Error`), recorded as unavailable, not no match.
- `rg` in upstream `WeilConjectures` and in `lean/Sheaf` for the item id and compact
  support/constructibility patterns found no existing theorem stating the item.
  Searches for restriction, finite realization, extension by zero and derived scalar
  change found the canonical interfaces listed above, which are reused.
- The earlier log's exact queries and raw responses are retained in `searches.jsonl`.

The source was checked online: Bhatt–Scholze, arXiv:1309.1198, Definition 6.7.6 and
Lemma 6.7.7 (p.55) define compact support by the proper/open factorization and preserve
constructibility; the preceding discussion gives the reduction and completeness route.
Stacks Tag 0GL0 supplies the finite-level compact-support constructibility result.
The node's classical bounded-cohomology convention is respected by its existing
finite-torsion and integral predicates; no paper-specific perfectness condition is added.
Links: https://arxiv.org/pdf/1309.1198 and https://stacks.math.columbia.edu/tag/0GL0.

No statement correction or disputed mathematical statement is proposed. Only `lean`
records of existing nodes are repaired. Every new theorem has its source, blueprint
owner and natural-language proof plan in its docstring.

## Dependency modules

`def-weil-compact-support-candidate`: lean-only existing-declaration repair. The old
`WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek` import conflicts with the
published finite-coefficient framework's lower-star notation. The already published
`sfAmbientCompactSupportCandidate` gives exactly the node's formula on intrinsic
constant-ring module sheaves. Its open extension is transported through the canonical
finite realization and its proper image is computed by K-injectives. No candidate is
redefined, and the compactification is retained.

`def-weil-derived-complete-integral-detailed`: lean-only existing-declaration repair to
`sfIntegralConstructible`. The recorded interface required an unrelated global
`FiniteFieldDatum`, unavailable for the arbitrary base field of this node. The
published intrinsic predicate has the same completed coefficients, derived completeness,
every finite constructible reduction and one common interval, without that auxiliary datum.

`lem-weil-restriction-of-scalars-exact`: lean-only existing-declaration repair to
`scalarReductionRestriction_exact` in `DerivedScalarExtensionRestrictionAdjunction`.
It is the same termwise restriction along the completed projection and has exactly
finite-limit and finite-colimit preservation, without an auxiliary finite-field datum.

`def-weil-integral-derived-reduction`: lean-only existing-declaration repair to
`scalarReductionDerivedExtension` in `DerivedScalarExtensionRestrictionAdjunction`.
The recorded interface required an auxiliary `FiniteFieldDatum`; this published
unrestricted interface supplies precisely the same canonical derived tensor along
the completion projection, with its universal counit and K-flat computations.
The finite-to-finite quotient transition needed only by the item's tower is a helper
in the item's own module. It uses the identity-on-sections composite restriction
comparison, then the normalized reduction adjunction. No reduction notion is redefined.

`lem-sf-compact-support-restriction-of-scalars`: this existing DAG prerequisite had no
Lean record. `SfCompactSupportRestrictionOfScalars` supplies the normalized realization
square, its inverse-equivalence square, the fixed and intrinsic extension-by-zero
squares, and the K-injective-normalized derived direct-image square. Their composite
is the exact isomorphism specified by the node. The final theorem states its coherence
for every pair of coefficient maps, using identity-on-sections restriction composition.
It binds the source's separated finite-type and invertibility hypotheses. Helpers are
parts of this existing notion; no new independent definition node is required.

## Validation

Both delivered modules compile cleanly through `scompile.py`, separately in dependency
order, in both sandbox and library modes. The final two-module check completed with
no errors or warnings: the compact-support comparison took 15–23 seconds per check
and the integral compact-support module took 13–22 seconds, within the 60-second limit.
All six node copies differ from the shared originals only in `lean`. The declared
signatures and complete declaration inventories were refreshed from the final files.
The prescribed `deliver2.py --no-push` is the final delivery gate; nothing is pushed.
An independent second reading remains for the next worker; this report does not claim one.

## Second reading by Q43

I read the item node, its source place, the final item module, and every repaired
dependency record. The node's objects and their Lean renderings match as follows.

- A field `K₀`, prime `ℓ` invertible in it, and finite-type `K₀`-schemes `X,Y` are
  rendered by `(K₀ : Type u) [Field K₀] (_hl : IsUnit (l : K₀))`, the two
  `Scheme.Over (Spec (.of K₀))` instances, and the paired
  `LocallyOfFiniteType`/`QuasiCompact` instances on the structure maps. This is
  finite type over the field and adds no separatedness of either structure map.
- The separated finite-type morphism `f : X ⟶ Y` over `K₀` is rendered by
  `[f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]`; these are exactly the node's hypotheses.
- The finite extension `E/ℚ_l`, its coefficient rings and positive levels are
  rendered by the section variables `[Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`, `Padic.coefficientExtensionRing`, and the
  `n + 1` indexing in `sfCompactSupportFiniteRestriction` and the term definitions.
  The finite instance is constructed for every positive level.
- The chosen compactification `c=(j,\bar f)` is the explicit section variable
  `(c : Compactification f)`. `sfCompactSupportTerm` is exactly restriction of
  the proper derived image of extension by zero, with the canonical derived
  reduction and completed-coefficient restriction.
- The integral object `K ∈ D^b_c(X, O_E)` is rendered by
  `K : DerivedCategory (scalarReductionSource l E X)` and
  `_hK : sfIntegralConstructible l E X K`; that predicate expands to derived
  completeness, constructibility of every positive finite reduction, and one
  common cohomological interval.
- The node's reduction tower and its canonical quotient transitions are rendered
  by `sfCompactSupportReductionTransition`, `sfCompactSupportTerm`, and
  `sfCompactSupportTransition`. Their types are respectively the higher-level
  reduction to the restricted lower level, the restricted proper compact-support
  term, and the map from level `n+1` to level `n`; the comparison is the recorded
  `sfCompactSupportRestriction` followed by the normalized restriction-composition
  isomorphism.
- The arbitrary product choice and arbitrary Roos derived limit are rendered by
  `[HasProduct (sfCompactSupportTerm l E c K)]`, `M`, and
  `_hM : IsDerivedLimit (sfCompactSupportTransition l E c K) M`. Thus the theorem
  quantifies over every chosen product and every object satisfying the node's
  derived-limit predicate.
- The conclusion is `sfIntegralConstructible l E Y M`, which expands to derived
  completeness, constructibility of every positive reduction, and a single
  interval independent of the level. No clause of the node is omitted or added.

The source was checked at Bhatt--Scholze Definition 6.7.6 and Lemma 6.7.7
(arXiv:1309.1198, p. 55), which assume separated finitely presented qcqs maps and
define `f_!` through an open/proper factorization and preservation of
constructibility. The node specializes this to finite-type schemes over a field;
the Lean hypotheses express that specialization and retain the chosen factorization.
The Stacks finite-level source Tag 0GL0 was also checked, including the actual
`more-etale.tex` source at `theorem-constructible-shriek`: finite presentation,
qcqs source and target, Noetherian coefficients, and torsion constructible input
are its hypotheses. Finite rings are Noetherian and torsion, and finite type over
a field supplies the relevant scheme finiteness conditions here. The fetched
source is retained only in the sandbox scratchpad.

Edge cases were checked: empty `X` or `Y`, zero complexes, and zero finite-level
reductions are permitted; the zero object satisfies any interval containing its
empty support. The natural index starts at `n = 0`, representing exponent one, so
all and only positive coefficient levels occur. Characteristic zero and positive
characteristic bases are both admitted subject only to `IsUnit (l : K₀)`. No
nonemptiness, positive dimension, perfectness, finite Tor amplitude, or extra
universe equality is assumed; the source and morphism site universes remain as
declared.

Independent searches, logged by `msearch.py` in `searches.jsonl`:

- LeanFinder: "Derived pushforward with proper supports preserves adic
  constructible complexes and uniform cohomology bounds" returned eight hits:
  derived-category t-structure/support bounds and light condensed modules,
  with no compact-support or integral constructibility theorem.
- Loogle: `"DerivedCategory", "support"` returned no hits.
- Mathlib grep: `adic.*constructible|constructible.*shriek|compact.*pushforward`
  returned no hits. The same `rg` search in upstream `WeilConjectures` and
  `lean/Sheaf` found definitions of adic constructibility, compact-support
  candidates, and finite-level etale preservation, which were inspected; none
  states the completed-coefficient tower theorem of this item.
- LeanSearch for the same natural-language query returned `Internal Server Error`;
  it is recorded as unavailable, not as a negative result.

Dependency audit: `Compactification` has the specified proper and open factors
and factorization equation; no density hypothesis is added. Its possibly non-qc
open immersion is qc here because `f` is qc, as its declaration docstring records.
`sfAmbientCompactSupportCandidate` unfolds to the exact composite in the node.
`sfIntrinsicExtensionByZero` transports the established fixed-coefficient extension
through `sfIntrinsicModuleEquivalence`, rather than introducing another sheaf.
The completion's unrestricted construction is the same ring-sheaf inverse limit;
`scalarReductionSource` uses that completed sheaf and `scalarReductionTarget` the
constant finite quotient. `scalarReductionRestriction_exact` supplies both finite
limit and finite colimit preservation. `scalarReductionDerivedExtension` is the
recorded canonical derived tensor, whose adjunction fixes the unit on K-flat
representatives. `sfIntegralConstructible` and
`intrinsicFiniteTorsionConstructible` retain the complete cohomological predicates,
including a single uniform interval. `IsDerivedLimit` is precisely the existential
distinguished Roos-triangle predicate, including its product hypothesis.

I also read the sibling dependency module
`SfCompactSupportRestrictionOfScalars.lean` against its node. The isomorphism is
an actual natural isomorphism, built from the uniquely sectionwise normalized
realization, the left-adjoint uniqueness comparison for extension by zero, and
the K-injective-normalized derived direct-image comparison. Its last theorem
states the full composable-map coherence with both restriction-composition maps.
Finite commutative rings, arbitrary derived objects, separated finite-type maps,
and prime invertibility on target stalks are represented exactly. The helper
existence theorems have complete normalization and proof docstrings; their chosen
data are determined by the indicated uniqueness or representative conditions.
There are no new independent definition nodes. The six node copies differ from
the shared records only in `lean`; the four existing-interface substitutions and
the supplied dependency module meet the authorized dependency-repair rules.

A further independent `rg` search for `restrictScalarsComp` and
`restrictScalars.*comp` found the fixed-coefficient sheaf comparison upstream
and the intrinsic commutative ring-sheaf comparison in
`BoundedConstructibleTower.lean`; I read their signatures and bodies.
The fixed-coefficient comparison has a different category, while the intrinsic
comparison applies exactly to the constant and completed ring sheaves here.

The second reading found an H4 duplication in the restriction-composition helpers:
`BoundedConstructibleTower.lean` already supplies
`AlgebraicGeometry.Scheme.pbcRestrictComp` with the exact identity-on-sections
normalization. I replaced both local existence/choice constructions with calls to
that shared comparison, and removed `sfRestrictionCompIsIdentity`,
`sfCompactSupportRestrictionComp_existsUnique`, and
`sfCoefficientRestrictionComp_existsUnique`. The only new postponed assertion is
`sfCompactSupportProjection_transition`: the completion cone condition needed to
apply the shared comparison. It is exactly the quotient-projection compatibility
already used in step 1 of the item's DAG proof and has a complete source/proof
docstring. The tower definitions, their types, and the main theorem signature
remain mathematically unchanged. Both declaration inventories were refreshed.
The original dry run passed, but I stopped its subsequent delivery before pushing
in order to make this repair. Both repaired modules independently passed `scompile.py` in sandbox and library
modes, with no errors or warnings. Their main signatures still match the node
records verbatim, all lines are at most 100 characters, and each theorem's proof
remains `sorry`. Final delivery preflight follows the repair.
