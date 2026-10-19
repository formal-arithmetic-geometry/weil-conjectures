## Worker report

The module `lean/Sheaf/Paper/IntegralRationalQbarCompactSupport.lean` defines
`sfIntegralCompactSupportValue`, `sfRationalCompactSupportValue`, and
`sfQbarCompactSupportValue`.  The integral definition forms the tower whose terms and
maps are the existing `sfCompactSupportTerm` and `sfCompactSupportTransition`, chooses
one object supplied by `exists_isDerivedLimit_and_iso`, and packages it with the
constructibility proof `sfIntegralCompactSupport_constructible`.  The rational definition
applies the existing unchanged-object localization functor.  The algebraically closed
definition returns the literal pair `(E₀, Rf_! K_E)` in
`generalAlgebraicallyClosedConstructibleCategory`; it uses the repaired datum-free
common-stage category and has no `FiniteFieldDatum` or relation between `K₀` and the
closure.

The declarations use the following renderings of the node's hypotheses and clauses.

* `K₀ : Type u` with `[Field K₀]` is the base field.  The `Over` instances for `X` and
  `Y`, together with `LocallyOfFiniteType` and `QuasiCompact` on their structure maps,
  render finite-type `K₀`-schemes.  `[f.IsOver ...]`, `[IsSeparated f]`,
  `[LocallyOfFiniteType f]`, and `[QuasiCompact f]` render a separated finite-type
  `K₀`-morphism.
* `l : ℕ` with `[Fact l.Prime]` renders the prime.  `_hl : IsUnit (l : K₀)` is exactly
  invertibility of `l` in the arbitrary base field.
* `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` render a finite coefficient extension.  The published
  coefficient-extension and reduction declarations supply its valuation ring,
  uniformizer, quotient rings, and maps at positive levels.
* A single `c : Compactification f` is outside the natural-number tower, so the same
  open/proper compactification is used at every level.  The existing term expands to
  restriction of the finite-level compact-support candidate applied to the derived
  reduction.  Its transition is the published reduction map followed by the normalized
  compact-support coefficient comparison and composite restriction comparison.
* The input `K : sfIntegralConstructibleCategory l E X` is the integral bounded
  constructible object.  The local `[HasProduct (sfCompactSupportTerm ...)]` is the
  product structure required by the recorded `IsDerivedLimit` interface; it is the
  product supplied by the exact countable-products route in the constructibility
  dependency.  The integral definition chooses a derived limit only after this
  structure is present, and then invokes the theorem asserting constructibility of every
  such limit.
* `sfRationalCompactSupportValue` is the localized object in
  `sfRationalConstructibleCategory l E Y`; it keeps the integral object unchanged.
* `Ω : Type v` with `[Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]` has an
  independent closure universe.  `E₀ : Padic.FiniteCoefficientFields l Ω` is the
  finite stage, and `K` uses the canonical `Coefficient l Ω E₀` size transport.  The
  final value is the literal pair in the datum-free common-stage category.
* No independence of the lattice, finite stage, or compactification is asserted by
  these definitions; those are separate statements as required by the node.

The imported dependency declarations are:

* `Sheaf.Paper.SfIntegralCompactSupportConstructible`: `sfCompactSupportTerm`,
  `sfCompactSupportTransition`, and `sfIntegralCompactSupport_constructible`.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory` and its pair category.
* `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory` and
  `sfRationalConstructibleLocalization`.
* `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory`.
* `Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence`:
  `CategoryTheory.exists_isDerivedLimit_and_iso`.
* `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`:
  `Padic.FiniteCoefficientFields`; the `Coefficient` size transport is from
  `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.
* The recorded compactification declaration is
  `WeilConjectures.Compactification.Refinement`.

The remaining statement dependencies are used through those published interfaces:
`Padic`, `IsAlgClosure`, finite coefficient extensions, intrinsic finite-torsion
constructibility, scalar reduction and restriction exactness, completed coefficients,
compact-support restriction comparisons, `IsDerivedLimit`, exact pro-etale countable
products, and the finite-subextension directed set.  No private replacement of any
notion was introduced.

Edge cases checked were the empty source and target schemes, the empty open factor, an
identity open/proper compactification, `n = 0` (the tower's first term has exponent
`n + 1`), identity coefficient transitions and repeated finite stages, zero complexes,
and zero localized objects.  The definitions require no nonempty scheme, algebraically
closed base field, or equality of the scheme and closure universes.  The prime condition
excludes exactly characteristic `l` where invertibility is required.

Searches made:

* `msearch.py ... leanfinder "integral rational algebraic closure compact support derived
  direct image as inverse limit finite coefficients"`: unrelated Mathlib hits; no exact
  notion.
* `msearch.py ... leanfinder "compact support derived limit rational algebraically closed
  coefficient pair"`: unrelated Mathlib hits; no exact notion.
* `msearch.py ... loogle "IsDerivedLimit sfCompactSupportTransition"`: zero hits (the
  project declarations are not in Mathlib).
* `msearch.py ... loogle "DerivedLimit sfCompactSupportTerm sfCompactSupportTransition"`:
  zero hits / unknown project identifier.
* `msearch.py ... grep "sfIntegralCompactSupportValue|sfRationalCompactSupportValue|
  sfQbarCompactSupportValue" WeilConjectures`: zero hits.
* Direct `rg` over `WeilConjectures/` and `lean/Sheaf` found the existing tower and
  repaired common-stage category, but no declaration of these three values.
* Mathlib grep for compact-support direct images and derived limits found only the
  pro-etale site and generic derived-category infrastructure, not this construction.

No `STATEMENT-DISPUTED` issue or source correction was found.

## Earlier second reading (a previous round; superseded)

I reread the node and the active N7 repair note after writing the module.  The owner is
`generalAlgebraicallyClosedConstructibleCategory` with arbitrary `K₀`, and the output is
its actual pair category rather than a sigma carrier.  The finite tower is indexed by
`n + 1`; the compactification is fixed; the rational stage preserves the integral
object; and no independence assertion was folded into a definition.  The module has
`autoImplicit false`, explicit universes and binders, and all lines are at most 100
characters.  The prescribed `scompile.py` check completed with no errors or warnings.

## Second reading by Q32

This is an independent reading of the worker's module, with the delivered node,
its recorded dependencies and their source declarations open. I also read the active
N7 repair notes for this item and `def-weil-algebraically-closed-coefficients`, and
`coord/reports/maintenance/N7-qbar-datum-free-interface.md`. The earlier second-reading
paragraph above is historical and does not replace this review.

Source comparison: I read the order-1490 blueprint definition, Bhatt--Scholze §6.7's
opening coefficient convention, Definition 6.7.6 and Lemma 6.7.7, and §6.8 Remark
6.8.15; also Stacks `more-etale.tex`, Theorem `theorem-constructible-shriek` (0GL0),
and `derived.tex`, Definition `definition-derived-limit` (08TC) and Lemma
`lemma-products` (07KC). The Stacks shriek theorem assumes qcqs schemes and a separated
finitely presented map, with a Noetherian coefficient ring. Here finite-type schemes
over a field are Noetherian and qcqs, finite type is finite presentation over the
Noetherian target, and the positive coefficient quotients are finite Artinian rings.
Bhatt--Scholze's coefficient ring is complete Noetherian local with finite residue
field, as is the valuation ring of the finite p-adic extension. Its l-coprimality
condition is supplied by invertibility in K₀. None of these source conventions
requires an additional geometric or coefficient hypothesis in this delivery.

The node's objects, hypotheses and clauses, matched individually:

1. Arbitrary base field K₀: `(K₀ : Type u) [Field K₀]` in all three definitions.
   Verdict: exact; neither a finite field nor a finite-field datum is introduced.
2. Finite-type K₀-schemes X and Y: `{X Y : Scheme.{u}}`, their two `Over`
   instances, and `LocallyOfFiniteType` plus `QuasiCompact` on both structure
   morphisms. Verdict: exactly finite type. In particular no separatedness of the
   individual schemes over K₀ is silently required.
3. Separated finite-type K₀-morphism f: `{f : X ⟶ Y}`, `[f.IsOver ...]`,
   `[IsSeparated f]`, `[LocallyOfFiniteType f]`, `[QuasiCompact f]`.
   Verdict: each source condition is present and no stronger condition is added.
4. Prime l invertible in K₀: `(l : ℕ) [Fact l.Prime]` and
   `(_hl : IsUnit (l : K₀))`. Verdict: exact, including characteristic zero and
   positive characteristic different from l.
5. Q_l, closure and finite extensions: `ℚ_[l]`/`Padic l` is Mathlib's completion;
   `E : Type u` with `Field`, `Algebra ℚ_[l] E`, `FiniteDimensional ℚ_[l] E`
   is a finite extension. In the closure clause, `Ω : Type v` has `Field`,
   `Algebra (Padic l) Ω` and `IsAlgClosure (Padic l) Ω`, and
   `E₀ : Padic.FiniteCoefficientFields l Ω` is exactly the subtype of finite
   intermediate fields. Verdict: exact; no embedding of the closure into K₀ is used.
6. Valuation ring, fixed uniformizer, quotients and surjections: the dependency
   `CoefficientExtensionFinite` publicly imports `CoefficientExtension`. I opened
   `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
   `coefficientExtensionIdeal`, `coefficientExtensionRing` and
   `coefficientExtensionTransition`. The ideal is the power of the principal
   uniformizer ideal; the transition is the actual quotient factor map. These are
   the existing chosen coefficient data, used unchanged. Verdict: exact.
7. Integral, rational and common-stage categories: I read `sfIntegralConstructible`
   and its full subcategory (derived completeness, all constructible positive
   reductions, one common cohomological interval), `sfRationalConstructibleCategory`
   and `sfRationalConstructibleLocalization` (raw localization with unchanged
   objects), and `GeneralAlgebraicallyClosedCoefficients.Stage`, `Pair`,
   `pairCategory` and `generalAlgebraicallyClosedConstructibleCategory`. Verdict:
   the recorded notions are used; the final category is the actual pair category,
   with common-stage Hom groups and no extra Karoubi envelope or datum binder.
8. One fixed compactification c: `(c : Compactification f)` occurs outside the
   natural-number family. I opened upstream `Compactification` in `Defs.lean` and
   its recorded `Refinement.lean`: c.i is open, c.g is proper and c.comm is the
   required factorization. Since f is quasi-compact, its open factor is also
   quasi-compact, as the upstream documentation explains. Verdict: exact.
9. Input K and finite-level terms: `K : sfIntegralConstructibleCategory l E X`
   supplies its actual derived object and membership proof. I opened
   `sfCompactSupportTerm`: its term n is completed-coefficient restriction of the
   finite candidate applied to `scalarReductionDerivedExtension ... n`. The latter
   is the recorded derived tensor along the completed-to-quotient projection;
   `scalarReductionSource` is modules over the completed sheaf, not a discrete
   constant O_E sheaf. I also opened `sfIntrinsicCompactSupport` and the ambient
   candidate: both are the same exact open extension followed by the K-injective
   derived proper image. Verdict: every part of Res_n Rf_{!,n} K_n is present.
10. Specified inverse-system maps: I read `sfCompactSupportReductionTransition`,
    `sfCompactSupportTransition`, `sfCompactSupportRestriction` and the composite
    restriction comparison. The reduction map is the transpose of the lower
    reduction unit under the higher derived extension/restriction adjunction; on
    K-flat representatives it is id tensor the quotient. The transition then
    applies the higher finite shriek, the normalized coefficient comparison,
    restriction, and the identity-on-sections restriction-composition comparison.
    Verdict: it is the node's transition, not an arbitrary family of maps.
11. Derived-limit existence and integral output: the body of
    `sfIntegralCompactSupportValue` now supplies
    `HasCountableProducts (DerivedCategory (scalarReductionSource ...))` internally
    from the published `integralOperationsDerivedCountableProducts`. I read its
    source and `integralTowerModules`: it is the identical completed coefficient
    module category, definitionally recovered by forgetting commutativity. Its
    proof plan is the exact-products and 07KC route required by the node. The
    already landed owning node `lem-pur-integral-operations-well-defined` is added
    to `stmt_deps`; it does not reach this item through statement or proof edges.
    `exists_isDerivedLimit_and_iso` supplies a Roos-triangle vertex, and
    `sfIntegralCompactSupport_constructible` supplies its full integral membership.
    Verdict: exact after removal of the worker's extra product hypothesis.
12. Rational value: `sfRationalCompactSupportValue` applies
    `(sfRationalConstructibleLocalization l E Y).obj` to the integral output.
    Its input is the integral representative K, exactly as the node's conditional
    definition requests. Every rational object has this unchanged object carrier.
    Verdict: the requested rationalized object, not an arbitrary scalar extension.
13. Algebraically closed value: `Coefficient.{u} l Ω E₀` is the existing `Shrink`
    model of E₀ with `Shrink.algEquiv`; I opened its `coefficientSmall` and
    `coefficientFinite` instances. `sfQbarCompactSupportValue` returns literally
    `⟨E₀, sfRationalCompactSupportValue ...⟩`. Verdict: precisely the pair
    (E₀,Rf_!K_E) in the recorded common-stage category, with independent u and v.
14. Independence clauses remain separate: the file defines only the three object
    values on the chosen data. Verdict: it adds no assertion of lattice, stage or
    compactification independence and no unrequested functor coherence.

Edge cases: the tower is always indexed by ℕ and exponent n+1, so n=0 is the
first positive quotient, never the zero-ring quotient at exponent zero. It has no
empty-index-set exclusion; the published countable-products interface also covers
empty products. Zero integral complexes, their localized objects, empty schemes
and empty open factors require no additional assumption. The chosen derived-limit
vertex is allowed up to the noncanonical isomorphism of the source definition.
Identity compactifications and the bottom/repeated finite field stages remain
available. The only excluded characteristic is characteristic l. Universe u is
arbitrary, and the closure universe v is independent; the existing finite-basis
size transport prevents any restriction on the cardinality of Ω. All variables
are bound explicitly or by the declared section variables with autoImplicit false.

Independent searches (other wording than the worker's):

* LeanFinder via `msearch.py`: "compactly supported pushforward of l-adic integral
  complexes using a homotopy inverse limit". Eight unrelated condensed/profinite
  constructions, no match.
* LeanSearch via `msearch.py`: "derived direct image with compact support integral
  l-adic coefficients inverse limit finite quotient reductions". Eight ordinary
  adic-completion/profinite-limit hits, no matching shriek definition.
* Loogle via `msearch.py`: `HasCountableProducts (DerivedCategory _)`; the service
  does not recognize the project identifier, so this is not positive match evidence.
* Direct rg over Mathlib, all upstream WeilConjectures and project lean/Sheaf for
  inverse/derived limits together with compact support or shriek, and for the
  three proposed full declaration names. No existing three-stage value was found.
  I opened the nearby project `CompactSupportReductionTower.lean`: it constructs
  the coherent finite reduction tower, not its integral derived-limit value or
  rational/closure values. I opened `IntegralCompactSupportUniformRestriction.lean`:
  its cbc candidate is Rp_*j_! over a different completed presentation with a
  compatible-uniform restriction, not the definition of this specified tower's
  limit. Upstream generic lowerShriek and adic comparison interfaces likewise do
  not define the node's three objects. The existing tower and category interfaces
  therefore remain reused and this module is needed.

Mismatches and repairs: the worker left `HasProduct (sfCompactSupportTerm ...)`
as an extra binder in all three values. That made existence conditional where the
node supplies it. I removed every such binder and supplied the published exact
countable-products consequence internally, adding its module import and its
already landed owner to stmt_deps. An inferred unannotated local instance did not
unfold the alternate coefficient presentation; the final explicitly typed
HasCountableProducts instance elaborates using definitional equality. I expanded
all three definition docstrings to spell out the tower, rational representative
and closure pair, and added the standard copyright header. The node's
lean.statement was refreshed verbatim from the final signature. No natural-language
statement was changed, no definition/dependency node was introduced or rewritten,
and no theorem or sorry was added. The earlier worker report's conditional-product
paragraph is superseded by this repair.

No hollow data is chosen here: the derived-limit existence theorem's proof is
complete, and its uniqueness-up-to-isomorphism clause determines the choice to the
specified equality used for this definition. Constructibility is a proof about
that chosen object, not the source of its data. Each of the three definitions has
its source and blueprint docstring; this definition node has no proof steps to
postpone. The final file compiles singly through scompile.py, within the 60-second
limit, with no errors or warnings. No variable, universe, file-local notation or
private replacement notion remains.
