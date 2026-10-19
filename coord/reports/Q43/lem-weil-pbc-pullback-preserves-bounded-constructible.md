## Worker report

The item is stated in `lean/Sheaf/AlgebraicGeometry/PullbackBoundedConstructible.lean`,
namespace `AlgebraicGeometry.ProEtale`, primary theorem
`finiteCoefficientBoundedConstructiblePullback_exact_and_interval`.
It restricts canonical derived inverse image to the recorded full essential image of
bounded constructible etale complexes, asserts exact triangulatedness, and preserves
all cohomological intervals. Every postponed proof is a named theorem with `sorry`
and source/blueprint/proof docstrings. Definitions have real data.

Hypothesis and conclusion correspondence:

- `(A : Type v) [CommRing A] (d : Scheme.CompleteCoefficientDatum A)` retains the
  commutative Noetherian ring, finitely generated ideal, additive torsion of A/I and
  perfect positive quotients. Its fields are `noetherian`, `ideal`,
  `finitelyGenerated`, `quotientTorsion`, `quotientPerfect`. The structure imposes no
  completeness condition.
- `[∀ m : ℕ, Finite (A ⧸ d.ideal ^ (m + 1))]` retains finiteness of every positive
  quotient. `(n : ℕ)` selects positive index n+1. The coefficient ring is
  `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`, with
  `(_e : Λ ≃+* A ⧸ d.ideal ^ (n + 1))` identifying it with the specified quotient.
  `[TopologicalSpace Λ] [DiscreteTopology Λ]` supplies its discrete topology.
  Universes u and v remain independent; a finite ring representative in the recorded
  coefficient universe is identified with the original quotient by `_e`.
- `{V' V : Scheme.{u}} (g : V' ⟶ V)` retains an arbitrary morphism and arbitrary
  schemes. The base T in the contextual FIN definition is not either of these
  arbitrary schemes; FIN and its target-base restrictions are not assumed here.
- `finiteCoefficientDerivedPullback V Λ g` is the published exact module inverse
  image applied termwise and descended by `Functor.mapDerivedCategory`. It implements
  Lg* = inverse image in the precise coefficient-ring-sheaf presentation.
- `finiteCoefficientBoundedConstructiblePullback g Λ` is `ObjectProperty.lift` of
  inclusion followed by that ambient functor. Its source and target are the recorded
  `FiniteCoefficientBoundedConstructibleDerivedCategory V Λ` and V' analogue.
  It acts by the ambient functor on objects and all morphisms.
- The first conjunct `.IsTriangulated` states exact triangulatedness. The named
  triangulated-closure theorem supplies the inherited triangulation. The restriction
  carries the canonical `CommShift ℤ` from exact termwise descent.
- `∀ K (a b : ℤ)` and `∀ i, (i < a ∨ b < i) → IsZero (...)` before and after
  pullback preserve precisely the same interval. Cohomology is
  `DerivedCategory.homologyFunctor` on `FiniteCoefficientModules`. No `a ≤ b`
  restriction excludes the reversed-interval case.

Dependency declarations used (all names in `AlgebraicGeometry.ProEtale` unless qualified):

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, `finiteCoefficientRealization`,
  `finiteCoefficientComparison`, `finiteCoefficientDerivedComparison`,
  `isBoundedConstructibleFiniteCoefficient`,
  `FiniteCoefficientBoundedConstructibleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`: the current recorded
  operations interface, particularly `finiteCoefficientUnrealization`,
  `finiteCoefficientPullback T Λ f`, `finiteCoefficientDerivedPullback T Λ f` and
  exactness instances. These are now reused directly, with no operations supplement.
- `Sheaf.AlgebraicGeometry.ConstructibleDirectImageFiniteness`: the published
  `ConstructibleDirectImageFiniteness`, `IsConstructibleFiniteCoefficientSheaf` and
  `finiteCoefficientHigherDirectImage`. It uses the same coefficient module category,
  linear etale-origin constructibility, and ordinary uncompleted derived direct image.
  The FIN predicate itself is contextual, not a hypothesis of the pullback theorem.
- `Sheaf.Paper.CompleteCoefficientDatum`: `Scheme.CompleteCoefficientDatum` and
  `Scheme.adicQuotientPerfect`, now imported explicitly. Its already landed node
  remains an added statement dependency for the coefficient packaging.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`, used through the recorded pro-etale
  essential-image definition, with `Scheme.IsConstructibleEtaleModuleSheaf`.
- `Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence`: the canonical comparison
  isomorphism and its coherence theorem, retained as a proof import after §1(B) repair.
  The recorded comparison node remains an explicit added dependency.
- Proof imports `Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullback`,
  `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`, and
  `WeilConjectures.CategoryTheory.DerivedCategory.Constructible` are retained.
- Mathlib `Functor.mapDerivedCategory`, `Functor.CommShift`, `ObjectProperty.lift`,
  triangulated subcategories and `DerivedCategory.homologyFunctor` supply the remaining
  constructions.

Edge cases: identity and arbitrary composites, empty schemes and zero complexes,
empty strata, zero coefficient ring, unit ideal, zero quotients, and n=0 (P_1) remain
included. Negative endpoints, a=b and b<a are quantified; in the reversed interval
all cohomology vanishes. No geometric hypothesis on g or either scheme is imposed.
The closure proof explicitly lifts maps by bounded-below comparison full faithfulness
before taking etale cones; closure is not inferred merely from being a full essential
image. Finite module-operation tables are retained in the constructible-pullback proof.

Searches from the original worker and independent reader (no exact target match):

- LeanFinder via `msearch.py`: "exact triangulated functor derived pullback bounded
  constructible pro etale schemes finite coefficient": eight adjacent site-pullback,
  exact-functor and finite-limit results, none the restriction theorem.
- Loogle via `msearch.py`: "isBoundedConstructibleFiniteCoefficient,
  mapDerivedCategory, proEtaleConstantModulePullback": no hits; the side predicate
  was unknown to the search service.
- Mathlib grep via `msearch.py`:
  "isBoundedConstructibleFiniteCoefficient|proEtaleConstantModulePullback": no hits.
- Direct rg in upstream WeilConjectures, side Sheaf, the upstream declaration map,
  Mathlib and the 51-module framework, including the prescribed item-id search:
  no exact target theorem. The nearby etale result uses a different constructibility
  predicate; the condensed result imposes finite-type separated schemes over a field
  with different coefficients.
- LeanSearch: "derived pullback bounded constructible proetale finite coefficients":
  unavailable (Internal Server Error), not treated as a match.
- Independent-reader LeanFinder: "inverse image t exact finite locally constant
  cohomology essential image": eight adjacent results, none exact. Loogle:
  "Functor.IsTriangulated, ObjectProperty.map": no hits. Mathlib grep:
  "cohomolog.*inverse|inverse.*cohomolog|essential.*constructible": no hits.
- For this repair, read current node records and current sources through
  `scompile.py --source` for FIN and `ProEtaleFiniteCoefficientDirectImage`.
  Found the published Q07/Q08 definitions and reused them rather than duplicating them.

No natural statement correction, new independent definition, or disputed statement
is introduced. The item's main theorem signature is unchanged.

## Dependency modules

Only `lem-weil-pbc-comparison-pullback` remains a delivered dependency module:
`lean/Sheaf/AlgebraicGeometry/ComparisonPullbackCoherence.lean`.
The recorded module's legacy `Comparison.LowerStar` closure collides with the finite
coefficient API's reorganized scoped notation. The repair imports the compatible
finite-coefficient inverse-image module and constructs `comparisonSiteBaseChangeIso`
and `comparisonCoefficientDirectImageIso` from the actual chosen fibre products and
continuous restriction composition. The inverse-image comparison remains the adjunction
mate of that canonical right-image comparison. The original identity, composite and
chosen Cartesian-square equations for sets, abelian groups and finite-ring modules
are retained. No abelian-category hypothesis is imposed on set coefficients.
Only `lean` changes in its node, with an explanatory `lean.note`.

## Returned immutable-head repair

Return L on head `0e8c5cd82f9e` flagged the concurrent landing of
`def-weil-pbc-constructible-direct-image-finiteness`. Decision: use the landed Q07/Q08
interface. Removed the stale FIN node copy and FIN module from this delivery, so it
cannot overwrite the published `ConstructibleDirectImageFiniteness` record or file.
Reading its actual source also exposed a concurrent published operations interface.
Removed the stale operations node copy/module and imported the published
`ProEtaleFiniteCoefficientDirectImage`; adapted ambient pullback calls to its explicit
argument order `finiteCoefficientDerivedPullback Y Λ f`. Added the explicit
`CompleteCoefficientDatum` import previously obtained through the removed FIN module.
The theorem, category, coefficient conditions and interval conclusion are unchanged.
The final delivery contains the item and comparison node records, their two modules,
and this report. FIN and operations are consumed from the published library.

## Earlier second reading (a previous round; superseded)

The following records the independent reading of the original delivery. The returned-head
repair described below supersedes its descriptions of the FIN and operations supplements;
the next reader must check the repaired imports and published dependency reuse.

I read the item, all three original sandbox modules, their owning nodes and the
recorded dependency signatures independently. I also read the actual blueprint files
for the item, FIN and operations in the local literature mirror, and Stacks
`proetale.tex`, labels `section-constructible`, `lemma-compare-constructible`,
`lemma-constructible-serre`, `lemma-compare-constructible-derived`, `definition-Dbc`
and `proposition-Noetherian-adic-constructible` (09AI, 09AK, 09B5, 09AL, 09C1, 09C7).
For operations I read `sites-modules.tex`, `lemma-adjoint-push-pull-modules`.
The comparison/Serre results require a Noetherian coefficient ring; finite commutative
rings satisfy this. They do not require a Noetherian scheme. The adic definitions
09C1/09C7 concern a different category and do not add hypotheses to this item.
The blueprint explicitly uses global finite stratifications; I checked the Lean against
that recorded criterion rather than silently replacing it with affine-local Stacks
constructibility. The already refined FIN node specifies a fixed c rather than the
ambiguous existential in the older blueprint text; the Lean follows the node.

Object/hypothesis/conclusion checklist (H3):

- The coefficient data A, I, torsion A/I, perfect positive quotients and Noetherian A
  are `(A : Type v) [CommRing A] (d : Scheme.CompleteCoefficientDatum A)`.
  I opened the structure: its five fields impose exactly these conditions, without
  completeness or flatness. Verdict: matches.
- Every P_m is finite: `[∀ m : ℕ, Finite (A ⧸ d.ideal ^ (m + 1))]`.
  The fixed positive index is `n + 1`; `_e : Λ ≃+* A ⧸ d.ideal ^ (n + 1)` identifies
  the coefficient ring. `[Finite Λ]` follows mathematically from this identification;
  `[TopologicalSpace Λ] [DiscreteTopology Λ]` implements the specified discrete topology.
  Verdict: matches, with no independent substantive extra hypothesis.
- V, V' and arbitrary g are `{V' V : Scheme.{u}} (g : V' ⟶ V)`.
  No geometric-property instance or FIN predicate is assumed. The FIN definition's
  Noetherian/dimension/invertibility assumptions on its separately introduced T do not
  become restrictions on V or V'. Verdict: matches.
- `Lg^* = g^{-1}` is `finiteCoefficientDerivedPullback g Λ`, defined by exact module
  inverse image followed by `Functor.mapDerivedCategory`. Its module functor transports
  the existing inverse image through `finiteCoefficientRealization`, not through an
  arbitrary equivalence. I read `finiteCoefficientScalarMap`, module sheafification,
  realization, and the equivalence obligation. Verdict: canonical specified functor.
- The source and target Dbc are the recorded
  `FiniteCoefficientBoundedConstructibleDerivedCategory V Λ` and V' analogue. I unfolded
  their predicate: full essential image of finite-stratification bounded constructible
  etale witnesses under `finiteCoefficientDerivedComparison`. Morphisms are all ambient
  derived morphisms. Verdict: same categories, not an adic/condensed replacement.
- The actual restriction is `finiteCoefficientBoundedConstructiblePullback`, an
  `ObjectProperty.lift` of inclusion followed by the ambient pullback. Its object
  obligation is the named preservation theorem. Verdict: restriction on objects and maps.
- Exact triangulatedness is the first conjunct `.IsTriangulated`, using the canonical
  restricted `CommShift ℤ`. The named closure theorem supplies the inherited
  pretriangulated subcategories; its proof lifts maps using bounded-below comparison
  full faithfulness before taking cones. Verdict: correct, not closure deduced merely
  from being a full essential image.
- Every interval is covered by `∀ K (a b : ℤ)` and the two identical tests
  `∀ i, (i < a ∨ b < i) → IsZero (homologyFunctor ... i ...)` before and after pullback.
  All degrees use the recorded ringed module categories. Verdict: same bounds and
  quantifier order, with no loss of negative or reversed intervals.

Dependency-module checks (H4/H5/H12/H13):

- FIN is a genuine existing DAG dependency without a declaration, now supplied in
  this delivery. Its Noetherian T, finite dimension and torsion-order invertibility
  are respectively `[IsNoetherian T]`, `_hdim`, `_horder`. Its two conjuncts quantify
  over all constructible F, all q ≥ 0 for constructibility, and all q > c for vanishing.
  `c : ℕ` is fixed uniformly in F. Higher direct image is exactly H^q(Rf_*(F[0])).
  Its constructibility predicate is the linear comparison essential image of the
  recorded finite-module etale predicate. All three definitions have actual data.
- The operations supplement publicly retains the old arbitrary identified-ring-sheaf
  operations and their normalized adjunction, then supplies the missing finite-ring
  presentation. Inverse realization is the inverse of a specified functor proved an
  equivalence, hence determined up to its equivalence, not data chosen from mere
  Nonempty. Derived pullback is exact termwise localization; direct image uses the
  existing K-injective right derived functor with exact coefficient equivalences.
- The additional comparison dependency repair keeps the original identity, composite
  and chosen-Cartesian-square coherence clauses for sets, abelian groups and every
  finite ring. The new right-image comparison is constructed from restriction and
  the canonical base-change identification; its inverse-image mate is determined by
  the existing adjunctions. No arbitrary comparison isomorphism is assumed.
- No new independent definition node was needed. Every auxiliary declaration is
  recorded in its owning node's `lean.declarations`; all postponed proofs are named
  theorems with source, blueprint identifier and natural-language proof instructions.
  No theorem was proved and no definition contains sorry data.

Edge cases: empty schemes and zero complexes remain admitted; empty strata/covers
introduce no Nonempty hypothesis. Identity, composites and arbitrary g remain included.
The zero coefficient ring, unit ideal and zero quotient are included. `n = 0` means
P_1, correctly excluding only the undefined P_0 indexing case. The characteristic is
unrestricted. `a = b`, negative endpoints and `b < a` are covered; a reversed interval
requires all cohomology to vanish. Scheme and original-ring universes u and v are
independent. Λ lives in the recorded coefficient universe u+1; any finite quotient
has such a representative, and `_e` connects it without imposing u = v. No variable
or universe is left implicit/unbound.

Independent searches used different terms from the worker:

- LeanFinder: `inverse image t exact finite locally constant cohomology essential image`:
  eight adjacent condensed/locally-constant results, no exact statement.
- Loogle: `Functor.IsTriangulated, ObjectProperty.map`: no results (first identifier
  unrecognized); no match claimed from this failure.
- The search wrapper's Mathlib grep for `cohomolog.*inverse|inverse.*cohomolog|essential.*constructible`:
  no hits. Direct rg also searched Mathlib, upstream WeilConjectures, side Sheaf and
  the exact 51-module framework for bounded constructibility/pullback in both orders,
  interval preservation, the realization equivalence and FIN helper notions.
- I opened the nearby upstream pro-etale `DerivedCategory.boundedConstructible` and
  condensed `boundedConstructible_leftDerivedUpperStar_obj`: the former uses a different
  recorded constructibility predicate/fixed-ring presentation; the latter assumes
  finite-type separated schemes over a field and condensed coefficients. Neither is
  this node. The existing etale result similarly has the other constructibility
  predicate and is not an exact pro-etale ringed-coefficient match.
- LeanSearch: `inverse image functor preserves bounded constructibility and cohomological amplitude`:
  service unavailable (Internal Server Error), recorded as unavailable.

Mismatch found and repaired: the required comparison proof-dependency import was
missing. Restoring it exposed the legacy/reorganized notation collision. I repaired
the recorded comparison dependency as above and restored the import. The item's
natural statement and all theorem signatures are unchanged; no statement_change or
citer correction is needed. All four node primary `lean.statement` strings were
checked verbatim against their module signatures. The only source changes beyond
this import are in the comparison dependency needed to make that import usable.

The item also records the already landed comparison node in `stmt_deps`, as permitted
by the landed-dependency rule, so its repaired interface is explicitly part of this
delivery. The original complete-coefficient dependency addition is retained. Neither
addition changes the natural statement. The comparison node's existing `lean.statement`
was normalized to the verbatim multi-line signature; its mathematical signature is unchanged.


Validation: the prescribed two-file scompile.py pass succeeded with no errors or warnings.
Both files compiled separately in sandbox and library form; library times were
13.0 seconds (comparison) and 20.9 seconds (pullback), within the 60-second limit.
Both primary lean.statement strings match their file signatures verbatim; all Lean
lines satisfy the 100-character limit. The prescribed deliver2.py --no-push then printed OK: commit 31a787b8fd
passes preflight and compiles; nothing was pushed. The staged set is exactly
the two node records, two modules and this report.

## Repair of return L (immutable head c80ffa5685b1)

The return reported only `FileNotFoundError(2, 'No such file or directory')` during
the independent file-only compilation and named no missing source file. I checked
the complete delivery inventory: both recorded Lean files exist at their exact
`lean.file` paths, both belong to the corresponding node records, and the report
and node JSON files are present. I then reran the prescribed compilation from this
sandbox with both modules in dependency order:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q43
lem-weil-pbc-pullback-preserves-bounded-constructible
lean/Sheaf/AlgebraicGeometry/ComparisonPullbackCoherence.lean
lean/Sheaf/AlgebraicGeometry/PullbackBoundedConstructible.lean`

It completed with no errors or warnings. The prescribed
`deliver2.py ... --no-push` dry run was rerun from this sandbox as well and printed
`OK (dry run)`: the staged files compile and pass preflight. No mathematical,
statement, dependency, or Lean-source change was required for this filesystem-only
failure.

## Earlier second reading (a previous round; superseded)

I independently opened the immutable item node, its source-place metadata (blueprint
order 1303; Stacks Tags 09AK, 09AL and 09B5), the two delivery modules, and the
recorded signatures of every statement dependency. The item says: (1) an adic
coefficient datum supplies a commutative Noetherian ring, finitely generated ideal,
torsion quotient and perfect positive quotients; (2) every positive quotient is finite;
(3) a fixed positive quotient is represented by a finite discrete coefficient ring;
(4) (V'), (V), and an arbitrary morphism (g:V'\to V) are introduced; (5) the
derived inverse image restricts to the bounded-constructible pro-etale categories;
(6) that restriction is exact triangulated; and (7) every object with cohomology in
[a,b] is sent to an object with cohomology in the same interval.

The Lean rendering of item (1) is `(A : Type v) [CommRing A]
(d : Scheme.CompleteCoefficientDatum A)`. I opened `CompleteCoefficientDatum`: its
fields are exactly `ideal`, `noetherian`, `finitelyGenerated`, `quotientTorsion`, and
`quotientPerfect`, with no added completeness or flatness assumption. Verdict: match.
The Lean rendering of item (2) is `[∀ m : ℕ, Finite (A ⧸ d.ideal ^ (m + 1))]`.
The rendering of item (3) is `(n : ℕ)`, `(Λ : Type (u + 1))`, `[CommRing Λ]`,
`[Finite Λ]`, `[TopologicalSpace Λ]`, `[DiscreteTopology Λ]`, and
`_e : Λ ≃+* A ⧸ d.ideal ^ (n + 1)`. This is the positive-index normalization
(P_{n+1}), so it covers exactly all (P_m) with (m\geq1), including (P_1),
without introducing a (P_0) case. Verdict: match.

The Lean rendering of item (4) is `{V' V : Scheme.{u}} (g : V' ⟶ V)`; there is no
properness, finite-type, Noetherian-scheme, dimension, characteristic, or FIN
hypothesis on either scheme or on `g`. Verdict: match. Item (5) is rendered by
`finiteCoefficientBoundedConstructiblePullback g Λ`, whose source and target are
`FiniteCoefficientBoundedConstructibleDerivedCategory V Λ` and its `V'` analogue.
Its definition is the `ObjectProperty.lift` of the inclusion followed by the
published `finiteCoefficientDerivedPullback`; it acts on all ambient morphisms.
Verdict: same restriction and same categories.

The Lean rendering of item (6) is the first conjunct
`(finiteCoefficientBoundedConstructiblePullback g Λ).IsTriangulated`. The supporting
module declarations provide the triangulated closure property, the exact derived
pullback, and the inherited `CommShift ℤ`; no weaker preservation predicate is used.
Verdict: match. Item (7) is the second conjunct, with quantifiers
`∀ (K ...) (a b : ℤ)`, the premise
`∀ i, (i < a ∨ b < i) → IsZero (homologyFunctor ... i).obj K.obj`, and the same
vanishing conclusion after pullback in the `V'` category. The quantifier order and
strict endpoint tests are unchanged. Verdict: match.

I checked the dependency modules as well. `ProEtaleFiniteModules` supplies the full
essential-image definition of bounded constructibility and its full subcategory;
`ProEtaleFiniteCoefficientDirectImage` supplies the canonical finite-coefficient
inverse image and its exact derived descent; `CompleteCoefficientDatum` supplies the
coefficient packaging; and the repaired `ComparisonPullbackCoherence` module
constructs the etale/pro-etale comparison from the base-change restriction and its
adjunction mate, retaining identity, composite, and chosen-cartesian-square clauses.
Each module uses the recorded notion rather than a private duplicate, and all proof
bodies remain named `sorry` theorems with source and blueprint docstrings.

Edge cases checked: identity and arbitrary morphisms, empty schemes, empty
stratifications, zero complexes, zero coefficient ring, unit ideal and zero quotient,
`n = 0` (the positive quotient (P_1)), unrestricted characteristic, independent
coefficient and scheme universes, negative endpoints, `a = b`, and `b < a`. The
reversed interval correctly asks for vanishing in every degree. No case requires a
nonempty scheme, nonzero object, or `a ≤ b`.

For the one-definition check I repeated searches with `msearch.py` LeanFinder query
`inverse image t exact finite locally constant cohomology essential image`, Loogle
query `Functor.IsTriangulated, ObjectProperty.map`, and Mathlib/source `rg` queries
for `boundedConstructible`, `constructible.*pullback`, `inverse.*cohomolog`, and
`essential.*constructible` in Mathlib, upstream WeilConjectures, and side `Sheaf`.
The results were adjacent site-pullback or condensed/etale notions, with no exact
item declaration. LeanSearch was unavailable (Internal Server Error), so it was not
used as evidence for a match. The recorded dependency declarations were opened and
used directly.

The mismatch I found was the stale comparison dependency interface: its legacy
`Comparison.LowerStar` import collided with the reorganized finite-coefficient API.
The delivery repairs that dependency by using the compatible API and constructing the
canonical comparison maps directly; the item's theorem signature and all mathematical
hypotheses and clauses are unchanged. I also confirmed that the item and repaired
dependency `lean.statement` strings are verbatim signatures from their files. The
required `scompile.py` compilation of both sibling modules completed cleanly.


## Second reading by Q43

I read the immutable item node, its blueprint/source note, the complete Lean
signature, and each dependency record. The node's statement decomposes as follows:

1. The coefficient datum is a commutative ring `A` with
   `Scheme.CompleteCoefficientDatum A`; its fields provide the Noetherian ring,
   finitely generated ideal, torsion `A/I`, and perfect positive quotients.
   Lean renders this as `(A : Type v) [CommRing A] (d :
   Scheme.CompleteCoefficientDatum A)`.
2. Every positive quotient is finite. Lean renders this as
   `[∀ m : ℕ, Finite (A ⧸ d.ideal ^ (m + 1))]`.
3. A fixed positive quotient is the finite discrete commutative coefficient ring
   `Λ`, represented by `_e : Λ ≃+* A ⧸ d.ideal ^ (n + 1)`, with `n : ℕ` and
   `Λ : Type (u + 1)`.
4. `V'`, `V`, and an arbitrary scheme morphism `g : V' ⟶ V` are introduced;
   Lean has `{V' V : Scheme.{u}} (g : V' ⟶ V)` and adds no geometric hypothesis.
5. `Lg* = g⁻¹` restricts to the bounded constructible pro-etale categories;
   Lean renders this by `finiteCoefficientBoundedConstructiblePullback g Λ`,
   the `ObjectProperty.lift` of the recorded ambient derived pullback.
6. The restriction is exact triangulated; Lean states
   `(finiteCoefficientBoundedConstructiblePullback g Λ).IsTriangulated`.
7. For every object and `a b : ℤ`, vanishing of homology when
   `i < a ∨ b < i` is preserved after pullback, with the same quantifier order
   and the corresponding `FiniteCoefficientModules V` and `V'` homology functors.

Every item above matches the node. The coefficient datum is the recorded structure,
and the FIN dependency's extra Noetherian finite-dimensional base `T` is contextual;
it is not imposed on the arbitrary `V`, `V'`, or `g`. The pullback uses the recorded
finite-coefficient inverse image and derived localization, and the bounded
constructible category is the recorded finite-stratification essential image.
The comparison dependency is the repaired canonical comparison (restriction along
the same chosen fibre products and its adjunction mate), retaining identity,
composition, and chosen-Cartesian-square coherence. No definition is duplicated and
all postponed arguments remain named `sorry` theorems with source and blueprint
docstrings.

Edge cases checked: identity and arbitrary morphisms; empty schemes and empty
stratifications; zero complexes and zero coefficient rings; unit ideals and zero
quotients; `n = 0` selecting `P_1`; unrestricted characteristic; independent scheme
and coefficient universes; negative or equal endpoints; and `b < a`, which correctly
requires vanishing in every degree. No nonempty scheme, nonzero object, or `a ≤ b`
hypothesis is introduced.

Independent searches used LeanFinder (`inverse image t exact finite locally constant
cohomology essential image`), Loogle (`Functor.IsTriangulated, ObjectProperty.map`),
the prescribed Mathlib/source `rg` searches for bounded constructibility and inverse
cohomology, and the recorded LeanSearch query. They found only adjacent site,
condensed, or etale declarations; LeanSearch was unavailable. Thus no existing exact
target declaration was found.

The mismatch found in the worker delivery was the stale comparison dependency
interface/import. I repaired that dependency by constructing its canonical comparison
from the actual base-change restriction and adjunction mate, and recorded the reason
in its `lean.note`. The item statement, theorem signature, hypotheses, conclusions,
and all edge cases were unchanged. The item and comparison `lean.statement` fields
were checked verbatim against their theorem signatures. No statement correction or
new independent definition node was needed.
