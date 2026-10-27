## Worker report

The module Sheaf.Paper.RealizationCompletedMate states
AlgebraicGeometry.Scheme.realizationCompletedMate, with one sorry and no new definitions.
It states the derived-category equality of the actual ordered strict-tower exchange
with the ordinary ambient mate conjugated by the two specified completion units.
The node's statement and all its other fields are unchanged.

Hypothesis and clause correspondence:

- Prime ell is `(l : ℕ) [Fact l.Prime]`. Finite E/Q_l is `(E : Type (u + 1))
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The recorded
  `pbcPadicCoefficientDatum l E` uses the actual `Padic.coefficientExtensionIntegers`
  and its recorded uniformizer. Its absolute value is the spectral extension of the
  p-adic absolute value. Thus there is no independently chosen coefficient ring,
  norm, quotient system, or completion here.
- The base field is `k : Type u`, `[Field k]`, `[Fact (ringChar k).Prime]` and
  `[Fact (ringChar k ≠ l)]`; prime characteristic is positive.
- The four schemes over k are `X Y X' Y' : Over (Spec (.of k))`. Each has explicit
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` assumptions on its
  structure map. The former two are the finite-type condition. Arrows in Over are
  morphisms over this same base. Each underlying scheme explicitly has
  `IsNoetherian`, a finite topological Krull-dimension bound `_h...dim`, and local
  invertibility `∀ x, IsUnit (l : ...presheaf.stalk x)` as `_h...inv`.
- The chosen Cartesian square is `sq : ChosenCartesianSquare g'.left f'.left
  f.left g.left`. Properness is `[IsProper f.left]`. No properness of g or extra
  base-change property is assumed.
- The completed coefficient ring is the recorded inverse limit of finite quotient
  continuous-function ring sheaves. All categories are on the small pro-etale site
  with object universe u+1 and morphism universe u. The actual integers live in
  Type (u+1); no site-universe identification is imposed.
- `K : PbcBoundedConstructibleComplete X.left (pbcPadicCoefficientDatum l E)` is
  exactly the full three-clause integral category. Its underlying object is `K.obj`.
  Its property includes intrinsic completeness, uniformly bounded constructible
  reductions, and existence of compatible etale-origin witnesses. No preferred
  witness is selected by this statement. For every retained witness the recorded
  `completedBaseChangeMap` unfolds to the same `completedExchange`, since its
  witness and completeness arguments do not enter its defining composite.
- M is `d.pull g.left` applied to `(d.push f.left).obj K.obj`; the ordinary output
  N is `(d.push f'.left).obj ((d.pull g'.left).obj K.obj)`, where d is the recorded
  p-adic datum (written out in Lean, without a let binder).
- e is `(d.integralExchange sq).app K.obj`. The existing declaration specializes
  `proEtaleAmbientRingedExchange` to the canonical completed coefficient maps;
  its natural transformation is the unit-square-counit mate, before completeness.
- The existential `γ` and `γ'` are isomorphisms whose homs are required equal to
  `d.ordinaryToCompleted g.left ((d.push f.left).obj K.obj)` and
  `d.ordinaryToCompleted g'.left K.obj`, respectively. This is precisely
  invertibility of the two specified maps, not existence of arbitrary endpoint
  isomorphisms. Equality of an iso's hom fixes its inverse as well.
- The last conjunct says `d.completedExchange sq K.obj = γ.inv ≫
  (d.integralExchange sq).app K.obj ≫ (d.push f'.left).map γ'.hom`.
  Lean composes left-to-right, so this is exactly the printed mathematical formula.
  `completedExchange` expands to Rlim(h), Rlim(v'), and the inverse of the specified
  direct-image/Rlim comparison, in that order. The full derived morphisms are
  equated; no per-degree weakening and no invertibility of exchange or e is stated.
- The rational category and E-valued continuous-function sheaf introduced in the
  prose supply context, but neither occurs in the equation or its hypotheses on K.
  No extra rationalized object or realization hypothesis was added. The existing
  `PbcRationalCategory` is raw scalar localization, not a Karoubi envelope.

Dependency declarations read and used:

- Sheaf.Paper.IntegralUniformCoefficient: `pbcPadicCoefficientDatum`, together with
  `PbcBoundedConstructibleComplete` from its public dependency
  Sheaf.Paper.BoundedConstructibleComplete, is the category underlying its recorded
  `pbcBoundedConstructibleComplete`. We use that underlying full subcategory because
  the node states local invertibility directly, whereas the convenience abbreviation
  takes a global-sections invertibility proof. This does not redefine the category.
- Sheaf.Paper.PbcRationalCategory: `PbcRationalCategory` and
  `PbcRationalDerivedCategory` were read; rationalization is not an operation in the
  present integral conclusion. It is already public through IntegralUniformCoefficient.
- Sheaf.AlgebraicGeometry.ChosenCartesianSquare: `ChosenCartesianSquare` and its
  chosen pullback iso and projection equations, publicly imported by the exchange.
- Sheaf.Paper.CondensedAmbientExchange: its recorded `condensedAmbientExchange` is
  for internal modules over a condensed ring, not the integral ring-sheaf category
  in this node. Its public retained general ring-sheaf interface is already available
  through CompletedBaseChangeMap / FourCorners. We use
  `AdicCoefficientDatum.integralExchange`, the existing specialization of exactly
  `proEtaleAmbientRingedExchange`, and do not duplicate either interface.
- Sheaf.Paper.PbcQbarCompletedPullback: the recorded `pbcQbarCompletedPull` acts on
  Qbar pairs. Its public retained strict-tower interface is
  Sheaf.Paper.CompletedPullback, from which we use `AdicCoefficientDatum.pull`,
  `push`, `completedPull` and `ordinaryToCompleted`. This is the integral interface
  the node requires, already available through CompletedBaseChangeMap.
- Sheaf.Paper.CompletedBaseChangeMap: `AdicCoefficientDatum.completedExchange` and
  `completedBaseChangeMap`, with their actual formula and witness-insensitive wrapper.
- Proof imports: Sheaf.Paper.OrdinaryCompletedIntegralPullback
  (`WeilConjectures.ordinaryCompletedIntegralPullback`) and
  Sheaf.Paper.CompletedExchangeUnit (`AdicCoefficientDatum.completedExchange_unit`).
  The latter supplies the ambient unit equation but not invertibility of the units,
  so it is not an exact existing match for this item. The three new stage-1 proof
  children have no Lean records yet and are described, not replaced, in the docstring.

Sources opened: the current blueprint's thm-weil-pbc-finite-extension statement and
integral-lattice proof paragraph; Bhatt--Scholze PDF, Proposition 6.8.14(2) and
Remark 6.8.15 (via pdftotext); local Stacks sites-cohomology.tex,
remark-base-change, lemma-Rf-commutes-with-Rlim, equation-projection-formula-map.
The source explicitly distinguishes naive and coefficient-tensor pullback.
The strict augmentation comparison remains the node's stated additional refinement.

Searches (results saved by msearch.py in searches.jsonl):

- LeanFinder: "Ordered completed pro etale base change exchange equals ordinary
  adjunction mate conjugated by completion units" returned eight general condensed,
  module-adjunction and adic-completion results; none states this comparison.
- Loogle: `CategoryTheory.mateEquiv, CategoryTheory.IsIso`, no matches.
- Mathlib grep through msearch.py: `completedExchange|completedBaseChange|completion.*[Mm]ate`
  in CategoryTheory, no matches.
- LeanSearch: "Completed derived base change exchange equals ordinary exchange
  conjugated by completion units", eight ordinary algebraic base-change/adic results;
  none matches.
- Project rg over lean/WeilConjectures and lean/Sheaf for the node id, completed mate,
  ordinaryToCompleted, completion units and completedExchange_unit found the existing
  maps, unit equation, identity completeness results and coherence results, but no
  theorem with both isomorphism conclusions and this specified equality.

Edge cases checked: zero K; identity square; arbitrary retained compatible witnesses;
empty schemes (all pointwise invertibility conditions remain vacuous as they should);
positive quotient indexing n+1 (no erroneous n=0 quotient); ramified extensions
(uniformizer and l generate different ideals but are not identified); no inversion
of e, v' or exchange; no arbitrary isomorphism chosen for the actual units. The
existential iso formulation avoids assuming the very IsIso facts the theorem states.

The resolved stage-1 repair note was read. Its re-split is present in the live node
(three proof children and a short assembly), and is preserved verbatim. No stage-2
interface repair was requested by that note. There are no statement corrections,
new nodes, dependency repairs, or disputed statements in this delivery.

Validation: scompile.py compiled the module cleanly in module mode, 4.5 s for the
library file, with no errors or warnings. Every variable and universe is explicit.

## Second reading by Q93

Self-check only: the dispatcher explicitly forbids starting another agent, so this
section does not claim an independent worker read. I reopened the node and the final
file. All four Noetherian, dimension, local-invertibility, separated and finite-type
conditions are present. Positive characteristic prime-to-l and properness are present.
The integral category is the recorded category on the actual integers, not its
rationalization or a replacement constant-coefficient category. Both iso hom equations
fix the completion units, and the final conjunct uses their inverse/forward directions
in the required order. The strict exchange is the actual published ordered composite,
not a mate substituted by definition. Compatible witnesses need no new assumption
because K already has them and the published map is independent of the retained data.
No mismatch was found and no statement field was changed.
