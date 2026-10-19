## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ComparisonTorInterval.lean` states
`AlgebraicGeometry.ProEtale.comparison_torAmplitudeIn_iff`.  It introduces a finite
commutative coefficient ring `A : Type (u + 1)`, a scheme `T : Scheme.{u}`, integers
`a b` with the interval hypothesis `_hab : a ≤ b`, and an object `K` of the bounded-below
ordinary derived category `DerivedCategory.Plus (Sheaf T.smallEtaleTopology
(ModuleCat.{u + 1} A))`.  The conclusion is an iff: `K.obj` has étale Tor amplitude in
`[a,b]` exactly when its canonical derived comparison pullback
`D(ν^*(T)[ModuleCat.{u + 1} A]).obj K.obj` has pro-étale Tor amplitude in `[a,b]`.
The two predicates are the ordinary `Etale.DerivedCategory.torAmplitudeIn` and
`ProEtale.DerivedCategory.torAmplitudeIn`, so the derived categories and tensor tests are
those supplied by the recorded definitions.

The hypotheses and clauses render in Lean as follows: finiteness is `[Finite A]`,
commutativity is `[CommRing A]`, the scheme is `(T : Scheme.{u})`, interval ordering is
`(_hab : a ≤ b)`, and bounded-below membership is the type of `K` in
`DerivedCategory.Plus`.  The forward and reverse clauses are the two directions of the
single displayed `↔`; the pullback is the canonical `D(ν^*)` functor from the site
comparison framework.

Statement dependencies used are `Sheaf.AlgebraicGeometry.DerivedCategories` (the ordinary
étale derived-category encoding) and
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` (the canonical comparison morphism and
module inverse image).  Proof-dependency modules imported are
`Sheaf.Paper.FiniteTorAmplitudeProEtaleModule`,
`WeilConjectures.SixFunctors.ProEtale.Comparison.Flat`,
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`,
`Sheaf.Algebra.Homology.DerivedTensor`, and
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`; the generic derived comparison
notation and pro-étale Tor predicate come from the published WeilConjectures modules.

Edge cases checked: `a = b` is allowed; negative and zero endpoints are allowed; no
nonemptiness or positivity condition is imposed on the interval beyond `a ≤ b`; finite
coefficient rings include the zero ring; arbitrary schemes, including the empty scheme,
are covered; and `K` is any bounded-below object, with no constructibility or invertible
exponent hypothesis added.

Searches for an existing declaration: `msearch.py ... leanfinder "site comparison preserves
and detects Tor amplitude intervals in derived categories"` returned only generic
T-structure declarations; `msearch.py ... loogle "DerivedCategory.torAmplitudeIn,
comparisonUpperStar, mapDerivedCategory"` returned no hit; `msearch.py ... grep
"comparison_torAmplitudeIn_iff" WeilConjectures` returned no hit.  Repository `rg` found
only the one-way `torAmplitudeIn_mapDerivedCategory` and a converse with additional
hypotheses in `WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison`; neither is the
node's iff statement.  No existing project declaration has this statement.

No new nodes or dependency repairs were needed.  No `STATEMENT-DISPUTED` flag applies.

## Earlier second reading (a previous round; superseded)

The node and module were read independently.  The Lean signature contains exactly the
finite-ring hypothesis, the scheme, ordered integer interval, and bounded-below object
specified by the node.  Its left clause is étale Tor amplitude of `K.obj`; its right clause
is the same interval for the canonical `ν_T^*` derived pullback on the full pro-étale site.
No constructibility, exponent, characteristic, or extra scheme hypothesis appears, and no
clause is omitted or strengthened.

## Second reading by Q34

I independently opened the current DAG node, its sandbox copy, the Lean module,
all six statement-dependency records and their actual source signatures. The original
worker report above records the earlier signature; the repairs and final mapping below
supersede its claims about the predicates, coefficient presentation and proof imports.
No `statement_change` is present or needed: the mathematical node statement is unchanged.

The node's objects, hypotheses and conclusions, in order, are:

| Node item | Final Lean rendering | Verdict |
| --- | --- | --- |
| An arbitrary scheme T | `(T : Scheme.{u})` | Exact; no scheme property instance. |
| A finite commutative ring A | `(A : Type u) [CommRing A] [Finite A]` | Exact; includes the zero ring and every characteristic. |
| Ordinary etale derived category | `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))`, underlying the type of K | This is the recorded `Etale.DerivedCategoryModule` presentation from `DerivedCategories` and upstream `Etale.Derived.Coefficients`. |
| K belongs to D+ | `(K : DerivedCategory.Plus (...))`, with `K.obj` its underlying derived object | Exact cohomological bounded-below condition; no upper bound or constructibility assumption. |
| Full small pro-etale site and ordinary D | Target of `(finiteCoefficientIntrinsicRealization T A).mapDerivedCategory`, definitionally `Scheme.proEtaleDerivedCategory T A` | Exact recorded intrinsic constant-ring `SheafOfModules` category on `Scheme.ProEt.topology T`. |
| Comparison inverse image, termwise on derived categories | `((siteComparisonDerivedPullbackPlus T (ULift.{u + 1, u} A)).obj K).obj`, followed by the canonical realization | Uses the recorded Q18 abbreviation for exact `comparisonUpperStar.mapDerivedCategoryPlus`; realization extends the constant scalar action by module sheafification. No arbitrary inverse image, map or abstract choice is substituted. |
| Integers a <= b | `(a b : ℤ) (_hab : a ≤ b)` | Exact, including equal endpoints. Moving independent binders before K changes no quantification. |
| Etale Tor amplitude in [a,b] | `Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1, u} A) T a b K.obj` | Uses exactly the bounded predicate listed by `def-kun-tor-amplitude`: every etale module sheaf F, every integer q outside the interval, `IsZero` of cohomology of the recorded derived tensor with F[0]. |
| Pro-etale Tor amplitude in the same interval | `Scheme.HasProEtaleTorAmplitude T A ((finiteCoefficientIntrinsicRealization T A).mapDerivedCategory.obj ((siteComparisonDerivedPullbackPlus T (ULift.{u + 1, u} A)).obj K).obj) a b` | Uses exactly `def-weil-proetale-tor-amplitude`, with all intrinsic module sheaves M in degree zero and all outside degrees. Its ordered-interval conjunct is already supplied by `_hab`. |
| Both implications | The displayed `↔` | Preservation and reflection, for the same K, pullback and endpoints. |
| Every test module, including nonclassical pro-etale modules | Universal F in `hasTorAmplitudeIn`; universal M in `HasProEtaleTorAmplitude` | Exact. The output has etale origin, but the test modules have no such restriction. |

Dependency inspection: `DerivedCategory.Plus` is the full subcategory for the standard
t-structure's `plus` property. `siteComparisonDerivedPullbackPlus` is the existing
termwise exact functor, not a derived scalar pullback with an extra hypothesis. I read
`ProEtaleSiteComparison` (its module adjunction is `comparisonAdjunction`),
`ComparisonDerivedPullbackFixed`, `EtaleTorAmplitude` and the upstream
`Etale.Derived.Coefficients.hasTorAmplitudeIn`, `ProEtaleDerivedCategory`,
`ProEtaleTorAmplitude`, and `ProEtaleFiniteModuleIntrinsicComparison` in full at the
relevant declarations. The last module's `finiteCoefficientIntrinsicRealization`
retains the fixed-scalar presheaf and applies module sheafification along the
constant-scalar unit; its named exactness theorem supplies additivity and finite-limit
and finite-colimit preservation. Thus the term in the conclusion belongs to the
precise recorded category, with its recorded `HasDerivedCategory.standard` instance.
The already landed `def-weil-pbc-proetale-modules` is added to `stmt_deps` to cite that
canonical realization. There is no new definition or dependency module in this delivery.

Sources checked: the historical blueprint statement and both historical and current
`lem-exc-comparison-tor-interval.proof.md` arguments; `proetale.tex` at
`lemma-fully-faithful` (099T) and `lemma-relative-comparison` (099V), which assume only
that X is a scheme; and `sites-cohomology.tex` at `definition-tor-amplitude` (08FZ),
`lemma-last-one-flat` (08G0), and `lemma-tor-amplitude` (08G1), which apply to any ringed
site and an ordered integer interval. They add no Noetherian, characteristic,
constructibility, or invertibility hypothesis. The source theorem
`flat_comparisonUpperStar_obj` has a Noetherian ring instance, but every finite
commutative coefficient ring has it; the delivered signature does not assume one.

Edge cases: a=b (including [0,0]), negative endpoints, the zero complex, the empty
scheme and the zero coefficient ring all remain allowed. There is no index family or
integer n parameter to constrain. There is no assumption of nonemptiness, nontriviality,
invertible exponent, finite type, quasi-compactness or quasi-separatedness. The scheme
universe u is arbitrary; the small site's objects remain in u+1 and morphisms in u,
with module values in u+1. The intrinsic recorded category uses coefficients
`A : Type u` and their canonical `ULift.{u + 1, u} A`; the etale category uses precisely
that same lift. This follows the dependency's existing size convention and does not
equate site universes. Every finite ring has a small finite model, and canonical
scalar transport identifies its modules with those over the lift; no coefficient case
is removed. Every K in the stated ordinary D+ is quantified, without choosing a model.

Independent searches (2026-10-16):

- `msearch.py Q34 lem-exc-comparison-tor-interval leansearch "Etale proetale inverse image equivalence of Tor amplitude in interval for any finite commutative ring"` returned eight formally-etale ring/algebra results, no comparison theorem.
- `msearch.py Q34 lem-exc-comparison-tor-interval leanfinder "Conservative inverse image reflects finite Tor dimension of complexes of module sheaves"` returned general sheaf-module finite-presentation/exactness and derived t-structure results, no matching theorem.
- `msearch.py Q34 lem-exc-comparison-tor-interval loogle '"torAmplitudeIn"'` returned zero hits.
- `rg` on pinned Mathlib for `torAmplitude|TorAmplitude|tor.dimension|TorDimension` found no relevant declaration. Searches on upstream `WeilConjectures` and project `lean/Sheaf` for Tor-amplitude and comparison vocabulary located the two Tor encodings, canonical intrinsic realization and the existing comparison statements. I opened `ProEtale.Derived.HomComparison.torAmplitudeIn_mapDerivedCategory` and `torAmplitudeIn_of_mapDerivedCategory`: the former only preserves amplitude, while the latter adds invertible exponent and bounded constructibility. I also opened `Sheaf.Paper.ComparisonTorAmplitude`'s preservation and reflection signatures: they use particular padic quotient coefficients, finite-field data and constructibility hypotheses. Neither supplies this arbitrary-finite-ring iff. The requested full declaration name has no upstream or Mathlib declaration.

Mismatches found and repaired:

1. The original right side used `ProEtale.DerivedCategory.torAmplitudeIn` on fixed-scalar
   sheaves, rather than the current recorded intrinsic predicate/category. It expressed
   the mathematical condition in an alternative presentation, but did not use the
   dependency's interface. Replaced it by `Scheme.HasProEtaleTorAmplitude` after the
   existing canonical exact realization; adopted that interface's common coefficient
   lift. No fresh Tor predicate or category was defined.
2. The original left side used the upstream t-structure Tor abbreviation. Replaced it
   by the exact recorded `hasTorAmplitudeIn`, whose defining universal tensor and
   cohomology test I checked. This retains the same mathematical condition.
3. The original statement bypassed the recorded `def-sf-comparison-derived-pullback`
   declaration. It now explicitly uses `siteComparisonDerivedPullbackPlus`, followed
   by the canonical realization required by the pro-etale category.
4. The original short proof docstring omitted the coefficient-ring test, upper smart
   truncation, lower flat cokernel construction, K-flat justifications and the unbounded
   tensor comparison required by the current six-step DAG proof. Expanded it step by
   step, naming the exact DAG inputs and explaining the canonical presentation change.
   Removed unrelated proof imports and imported the actual recorded proof inputs.
5. Updated `lean.statement` verbatim from the final theorem signature and recorded the
   presentation change in `lean.note`. All other mathematical node fields remain intact.

The final module contains one theorem with proof exactly `by sorry`, no new definitions,
no proved theorem, no file-local instance/notation, and `autoImplicit false`. All variables
and the single universe are explicitly bound. Source and blueprint docstrings are present;
all Lean lines are at most 100 characters. No mathematical statement dispute remains.

Validation: `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q34 lem-exc-comparison-tor-interval lean/Sheaf/AlgebraicGeometry/ComparisonTorInterval.lean` passed locally through the authorized isolated wrapper (sandbox 12.3 s, library check 40.8 s), with no errors or warnings.
