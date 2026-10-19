## Worker report

The delivery states `CategoryTheory.fibrant_pullback_mapping_invariance` in
`Sheaf.CategoryTheory.FibrantPullbackMappingInvariance`. Its only proof is `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The copied node changes only in `lean`.

Source read: Lurie, Higher Topos Theory, Remark A.2.4.5, PDF page 833
(printed page 816), https://people.math.harvard.edu/~lurie/papers/HTT.pdf.
The remark explicitly permits fibrant objects instead of right properness for the
homotopy-pullback criterion. The six-step mapping-space argument is the supporting
argument recorded in the node, and is reproduced in the theorem's docstring.

Hypotheses and clauses, with the node and module open:

- The model category is `(M : Type u) [Category.{v} M] [ModelCategory M]`.
  `[HasLimits M] [HasColimits M]` retain the completeness and cocompleteness convention
  stated in `lem-coef-simplicial-model-nerve-localization`. The two
  `MorphismProperty.HasFunctorialFactorization` instances retain its functorial weak
  factorization systems for cofibrations/trivial fibrations and trivial
  cofibrations/fibrations. The model-category class supplies retract closure,
  two-out-of-three, and the lifting-characterized classes. These are the dependency's
  convention, not a replacement by a restricted class of model categories.
- `[SimplicialCategory M]`, `(_tensor : SimplicialTensorCotensor M)` and
  `(_sm7 : SimplicialModelLocalization.SatisfiesSM7 M)` are precisely the existing
  enriched tensor/cotensor data and SM7 mapping-space axiom. Their types and docstrings
  were read in the dependency's source and `SimplicialTensorCotensor.lean`.
- Every object is cofibrant: `(_allCofibrant : ∀ X : M, IsCofibrant X)`.
- The specified fibrant objects are `(U U' E : M)` with the three
  `[IsFibrant ...]` instances. The arrow `a : U ⟶ U'` has `[WeakEquivalence a]`, and
  `b : E ⟶ U'` has `[Fibration b]`. No properness instance or hypothesis is present.
- The strict pullback is Mathlib's `pullback a b`, with exactly the requested
  projection `pullback.snd a b : pullback a b ⟶ E`. Neither object nor map is replaced
  by a homotopy pullback or by an unspecified equivalent object.
- Fibrancy of D is the first conjunct `IsFibrant (pullback a b)`.
- For every bifibrant T: `∀ T : M, IsCofibrant T → IsFibrant T → ...`.
  The two explicit `SSet.KanComplex` conjuncts say that both enriched mapping sets are
  Kan, including empty ones. `SSet.Enhanced.IsWeakHomotopyEquivalence` is applied to
  `eHomWhiskerLeft SSet T (pullback.snd a b)`, the existing enriched postcomposition
  map, not to an unrelated map between the same mapping objects. The weak-equivalence
  predicate is the existing realization-based predicate, including components and
  all positive homotopy groups at every basepoint.
- C is exactly `SimplicialNerve (SimplicialModelLocalization.Bif M)`.
  The last conjunct supplies an edge `e` of C and applies the existing
  `SSet.Enhanced.IsEquivalenceEdge` to it. The endpoint equations require its underlying
  objects to be exactly D and E. The `HEq` requires its entire enriched map from 0 to 1
  to be `SSet.const (homEquiv' D E (pullback.snd a b))`, with the displayed thickening
  Hom as domain. This fixes the represented arrow, not just its component or endpoints.
  In dimension one the other nonempty thickening Homs are the two identity Homs;
  their maps are forced by the enriched-functor unit law, and the reverse Hom is empty.
  Thus the endpoint equations and whole-map equation characterize the unique edge of h.
  The existential proves existence of this exact edge together with its equivalence;
  it does not assume a chosen edge or merely assert equivalence of D and E as objects.
- The object universe u and morphism/mapping universe v are independently bound.
  The coherent nerve lives in their containing universe `max u v`; no equality or
  restriction on the two universe variables is added.

Dependency declarations used:

- `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`:
  `CategoryTheory.SimplicialModelLocalization.SatisfiesSM7`, `.Bif`, and the proof input
  `CategoryTheory.simplicial_model_nerve_localization`. Its full statement and docstring
  were read, as were `cornerMap`, `IsOrdinaryNerveMap`, and its mapping comparison.
- `Sheaf.CategoryTheory.SimplicialTensorCotensor`:
  `CategoryTheory.SimplicialTensorCotensor`, the existing enriched representing objects.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence` and `.IsEquivalenceEdge`.
- The stated proof inputs are imported directly:
  `Sheaf.CategoryTheory.FiniteReedyLocalization` (coherent localization),
  `Sheaf.AlgebraicTopology.RealizationFiniteLimits` (realization of the enriched
  composition homotopies), and
  `Sheaf.AlgebraicTopology.KanQuillenModelRightProperCore` (right properness only of
  simplicial sets). The other proof-input modules above are public imports because
  their definitions also occur in the statement.

Edge cases checked before writing: a identity gives the identity pullback projection;
with b identity the projection identifies with a, an arbitrary weak equivalence between
fibrant objects. When both are identities the final edge is the identity edge. Empty
mapping complexes are allowed by the Kan predicate and by the component-bijection
condition; no basepoint or inhabitance is assumed. Initial, terminal and zero objects
where present impose no further condition. The theorem does not assume a to be a
fibration. Distinct object and morphism universes remain allowed. There is no statement
dispute.

Searches performed with `msearch.py Q103 lem-coef-fibrant-pullback-mapping-invariance`:

- LeanFinder: "In a simplicial model category with all objects cofibrant, pullback along
  a fibration of a weak equivalence between fibrant objects induces weak homotopy
  equivalences on enriched mapping spaces". Eight hits: homotopy relations and classes,
  Whitehead inverse, bifibrant-object weak-equivalence transport, and trivial-fibration
  pullback instances. None gives the enriched mapping-space and coherent-edge statement.
- Loogle: `"WeakEquivalence", "Fibration"`. Twelve hits on trivial classes, stability,
  factorization and pullback instances. The pullback instance needs the map being
  pulled back to be a trivial fibration; the present a is only a weak equivalence.
- Mathlib grep through msearch:
  `pullback.*[Ww]eakEquivalence|[Ww]eakEquivalence.*pullback|rightProper`, restricted to
  `AlgebraicTopology/ModelCategory`. Six hits in PathObject, Instances and JoyalTrick.
  Read the relevant pullback instances in Instances.lean, which require a fibration
  as well as weak equivalence on the pulled-back arrow. They do not match.
- LeanSearch: "Pullback of a weak equivalence between fibrant objects in a simplicial
  model category induces weak homotopy equivalences on simplicial mapping spaces".
  Eight hits: full-subcategory weak-equivalence transport, path objects, a trivial
  fibration pullback instance, and finite simplicial pullbacks. None is the item.
- `rg` of `WeilConjectures/` and `lean/Sheaf` for fibrant pullback / pullback mapping
  invariance and the item id found no matching declaration. The required item-id
  search of upstream sources also found none. Exact proposed declaration/module-name
  searches of Mathlib, upstream sources, `lean/Sheaf` and `dag/lean_names_upstream.json`
  found no name collision. Related project nodes concern rectification or more general
  localization constructions, not this precise pullback statement.

Validation: the first scompile.py run compiled the file without errors or warnings
(about five seconds for the library file, under the default 60-second limit).
The final delivery wrapper recompiles the final file and runs server preflight.

## Second reading by Q103

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
