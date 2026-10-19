## Worker report

The delivery states `HomotopicalAlgebra.strict_diagram_evaluation_conservative` in
`Sheaf.CategoryTheory.StrictDiagramEvaluationConservative`. Its only proof is `sorry`.
There are no new definitions, dependency repairs, new nodes, or statement corrections.
The additional landed interface node in `stmt_deps` supplies the localization notion.
The natural-language statement and proof of the assigned node are unchanged.

### Hypotheses and clauses

- The small universe is `u`; `M : Type v` and `[Category.{u} M]` give the ordinary category
  with small Hom sets. `v` is independent of `u`, and the ambient simplicial universe is
  `max u v t`, with independent additional enlargement `t`.
- All small limits and colimits are `[HasLimitsOfSize.{u, u} M]` and
  `[HasColimitsOfSize.{u, u} M]`. These include initial and terminal objects. The chosen
  Mathlib initial object represents the statement's `0`; replacing it by any other initial
  object does not change cofibrancy, since the lifting classes respect isomorphisms.
- The classes C, F, W are the data of `[CategoryWithCofibrations M]`,
  `[CategoryWithFibrations M]`, `[CategoryWithWeakEquivalences M]`. They are arbitrary
  specified morphism classes, not an assumed model structure.
- W's retract closure and two-out-of-three are exactly
  `[(weakEquivalences M).IsStableUnderRetracts]` and
  `[(weakEquivalences M).HasTwoOutOfThreeProperty]`.
- The two `[MorphismProperty.IsWeakFactorizationSystem ...]` hypotheses use
  `(cofibrations M, trivialFibrations M)` and
  `(trivialCofibrations M, fibrations M)`. Mathlib defines the trivial classes by
  intersection with W. The WFS class asserts factorization and both exact lifting-class
  characterizations, rather than just existence of lifts in one direction.
- The two `[MorphismProperty.HasFunctorialFactorization ...]` hypotheses retain
  functorial factorizations for precisely those two pairs.
- `CofibrantObject M` is Mathlib's full subcategory of objects satisfying
  `IsCofibrant`, which is `Cofibration (initial.to X)`; thus it is exactly M_c.
- `(I : Type u) [Category.{u} I]` is an arbitrary small ordinary category. No finiteness,
  nonemptiness, degree function, or direct/inverse-category hypothesis occurs.
- `((weakEquivalences M).inverseImage CofibrantObject.ι)` restricts W to M_c.
  Its `.functorCategory I` is exactly W_I: a natural transformation belongs precisely
  when each of its components, under the inclusion into M, belongs to W.
- `qB`, `hqB` present B as the coherent localization of the enlarged nerve of M_c;
  `qA`, `hqA` present A as the coherent localization of the enlarged nerve of strict
  functors `I ⥤ CofibrantObject M`. `FiniteReedy.IsLocalization` includes quasicategory
  structure, inversion of W, and equivalence on the entire coherent functor category
  onto the full subcategory of W-inverting functors for every test quasicategory.
  It does not use an ordinary localization or only cores as a replacement.
- `FiniteReedy.largeNerve` is the nerve with degreewise actual `ULift` simplex data.
  The explicit maximum universe parameters align these lifts for strict evaluation;
  they impose no equality between the small, object, or additional ambient universes.
- The first conclusion supplies an induced comparison
  `E : A ⟶ (ihom (FiniteReedy.largeNerve ... I)).obj B`, normalized by
  `AreNaturallyEquivalent (qA ≫ E) (FiniteReedy.comparison ... qB)`.
  The right side is the actual curried strict evaluation followed by localization.
  This clause states the existence implicit in “induces” and prevents a vacuous
  assertion about extensions. It makes no choice of an object from an unproved theorem.
- For every comparison with this coherent normalization, its evaluation at `i` is
  `E ≫ evaluation (FiniteReedy.largeNerve ... I) B
  (ULift.up (ComposableArrows.mk₀ i))`. Thus the functors used to test arrows are the
  localized evaluations, not arbitrary maps. Normalization up to coherent equivalence
  is the invariant universal-property meaning of an induced functor.
- The first conjunct for every such E quantifies `a : A _⦋1⦌`, assumes
  `IsEquivalenceEdge B` of its image under each evaluation, and concludes
  `IsEquivalenceEdge A a`. The quantifier is over arbitrary edges in A, not just images
  of strict natural transformations.
- The final conjunct is explicitly conservativity: `IsEquivalenceEdge` of `E.app _ a`
  in the internal hom implies `IsEquivalenceEdge A a`. The pointwise equivalence
  criterion in the imported enhanced functor calculus identifies this with the previous
  conjunct, as in the node's “equivalently” clause.
- There is no model structure on `M^I`, simplicial enrichment, combinatoriality,
  properness, saturation assumption, or nonempty-index assumption in the signature.

### Dependencies and source inspection

Read the assigned node in full, including its ten proof steps. Read its original statement
prerequisite `def-cbc-enhanced-diagrams-cones` and the source of its recorded declarations
in `Sheaf.CategoryTheory.EnhancedDiagramsCones`. The statement directly uses
`SSet.Enhanced.IsEquivalenceEdge`, `evaluation`, and `AreNaturallyEquivalent`;
the localization definition uses `fullSubcomplex`, `diagramVertex` and
`IsFunctorEquivalence`. These are the dependency's existing notions, with their full
simplicial inverse-triangle and coherent natural-equivalence data.

Added the already landed definition node `def-coef-coherent-localization-interface` to
`stmt_deps`, as permitted by brief-stage2 section 5. Read that whole node and its recorded
source in `Sheaf.CategoryTheory.FiniteReedyLocalization`, especially `largeNerve`,
`Inverts`, `localDiagrams`, and `IsLocalization`. The same source supplies
`strictEvaluation` and `comparison`, which retain every simplex of strict diagrams and
transformations. No finite-Reedy theorem or finite-Reedy hypotheses are used. Citing the
separate interface node avoids making the statement depend on a downstream theorem.

The only stated proof dependency is `lem-cbc-enhanced-functor-cone-calculus`, whose module
`Sheaf.CategoryTheory.EnhancedFunctorConeCalculus` is imported without `public` and whose
`ComponentwiseEquivalence` signature was read. The remaining proof dependencies have no recorded project Lean modules: the
lifting-class closure, good-homotopy test and map-surjectivity nodes use their existing
Mathlib matches, already available through the model-category imports; the
localization/homotopy-category node remains unstated and is not imported. The theorem docstring carries
all ten proof steps, including the replacement of raw pullbacks, finite-word fraction
induction, homotopy-category comparison for the actual arrow, inverse representation,
two good-cylinder homotopies, the explicit arrow retract, and the empty-category case.

Mathlib declarations inspected include `CofibrantObject`, its inclusion `ι`,
`IsCofibrant`, `MorphismProperty.IsWeakFactorizationSystem`,
`MorphismProperty.HasFunctorialFactorization`, and `ComposableArrows.mk₀`.
The source theorem's conservativity paragraph was read online in Cisinski,
[Higher Categories and Homotopical Algebra](https://cisinski.app.uni-regensburg.de/CatLR.pdf),
PDF page 425 / printed p. 410, between (the project server) and (the project server). The node spells out the
ordinary-model-category specialization and the fraction and saturation subargument;
that supplied proof route is retained, not replaced by the stronger rectification theorem.

### Edge cases

- Empty I: there is no `Nonempty I` or selected index. The evaluation hypothesis is
  vacuous; strict diagrams form the terminal category, so the localization has only
  invertible arrows. Both detection and conservativity retain this case.
- Terminal I: strict evaluation is the identity on the cofibrant part up to the standard
  nerve identification; the induced comparison is an equivalence, consistent with detection.
- Degenerate/identity edges are included among the arbitrary `A _⦋1⦌` edges.
- No object of M is required as extra data; initial/terminal objects follow from the
  existing small (co)limit assumptions.
- Object universe v can differ from the Hom/index universe u. No `u = v`, finite-index,
  small-object-set assumption on M, or fixed ambient enlargement was introduced.
- Distinct choices of localizations and of induced comparison are allowed: qA/qB are
  arbitrary presentations with the full universal property, and the result quantifies
  every coherently normalized E.

### Searches

Ran the prescribed `msearch.py` searches (the wrapper also recorded `searches.jsonl`):

- LeanFinder, “Evaluation functors jointly reflect equivalences in the infinity
  localization of strict diagrams of cofibrant objects of a model category”: eight hits
  on `CofibrantObject.factorsThroughLocalization`, `localizerMorphism` and ordinary
  localization equivalences. None states detection in a coherent strict-diagram localization.
- Loogle, `MorphismProperty.IsWeakFactorizationSystem,
  MorphismProperty.HasFunctorialFactorization`: zero hits, unknown identifier in the
  search service. Direct Mathlib source lookup found and checked both actual declarations.
- Mathlib grep, `evaluation.*(conserv|reflect)|localization.*conserv`, under
  `AlgebraicTopology`: eight hits about jointly reflecting ordinary limits/colimits in
  simplicial sets, none about this theorem.
- LeanSearch, “Functor category model category localization evaluation reflects
  equivalences”: eight ordinary localization and equivalence results, including
  `Functor.IsLocalization.mk`, `Localization.lift`, and ordinary cofibrant homotopy
  localization. None supplies the entire quasicategory detection statement.
- `rg` over the project and upstream sources for localization, weak factorization,
  `IsLocalization`, strict-diagram evaluation and conservativity found the existing
  FiniteReedy helper interface and the downstream FreeDiagram proof's reference to this
  still-missing lemma. It found no declaration of this lemma. The exact declaration name
  `strict_diagram_evaluation_conservative` has no collision in Mathlib/project/upstream names.
- The prescribed upstream grep for the exact DAG id returned no attachment.
  DAG/source search found `def-coef-coherent-localization-interface` already carrying
  the localization helpers, so no duplicate definition node was made.

No statement fault or STATEMENT-DISPUTED remains.

### Validation

`scompile.py Q33 lem-coef-strict-diagram-evaluation-conservative` compiled the file
in both sandbox and library modes cleanly, with no errors or warnings. An initial
universe elaboration error was repaired by using the explicit universes of the existing
comparison and aligning its degreewise lifts; no universe equality assumption was added.
The module has one public theorem, no local notation/private data, and no auxiliary proofs.
The node's Lean signature is copied verbatim from the final source, and its other fields
are unchanged except for the permitted addition of the landed interface definition to
`stmt_deps`.

## Earlier second reading (a previous round; superseded)

I read `dag/nodes/sec-six-functors/lem-coef-strict-diagram-evaluation-conservative.json`,
the Cisinski source place named there, and the declarations of both statement dependencies.
The item-by-item match is as follows.

1. The node's ordinary category \(\mathcal M\), universe \(\mathcal U\), and small Hom
   sets are rendered by `M : Type v` and `[Category.{u} M]`; the independent object and
   Hom universes are retained. Verdict: matches.
2. The node's all-small limits and colimits are rendered by
   `[HasLimitsOfSize.{u, u} M]` and `[HasColimitsOfSize.{u, u} M]`. Verdict: matches,
   including initial and terminal objects.
3. The three arbitrary classes \(C,F,W\) are rendered by the three
   `CategoryWith*` instances. Verdict: matches; no model-structure class is added.
4. Retract closure and two-out-of-three for \(W\) are rendered by
   `IsStableUnderRetracts` and `HasTwoOutOfThreeProperty`. Verdict: matches exactly.
5. The two weak factorization systems are rendered by the two
   `IsWeakFactorizationSystem` instances on `(cofibrations, trivialFibrations)` and
   `(trivialCofibrations, fibrations)`. Verdict: matches the node's factorization and
   lifting-class characterization; the Mathlib trivial classes are the required
   intersections with `W`.
6. The two functorial factorizations are rendered by the two
   `HasFunctorialFactorization` instances for those same pairs. Verdict: matches.
7. The initial object and cofibrant subcategory \(\mathcal M_c\) are rendered through
   Mathlib's `CofibrantObject M` in the localization source. Verdict: matches the node's
   `0 \to X` cofibration definition.
8. The arbitrary small index category is rendered by `(I : Type u) [Category.{u} I]`.
   Verdict: matches; no finiteness, nonemptiness, degree, or Reedy assumption appears.
9. The localized weak-equivalence classes are rendered by
   `((weakEquivalences M).inverseImage CofibrantObject.ι)` and its
   `.functorCategory I`. Verdict: matches componentwise `W_I`.
10. The presentations `qB`, `hqB`, `qA`, and `hqA` use the existing
    `FiniteReedy.largeNerve` and `FiniteReedy.IsLocalization`. Verdict: matches the
    enlarged nerve and entire coherent-functor universal property; the explicit universe
    parameters preserve all independent universes.
11. The first conclusion is rendered by the existential `E` and
    `AreNaturallyEquivalent (qA ≫ E) (FiniteReedy.comparison ...)`. Verdict: matches the
    induced strict-evaluation comparison and its coherent normalization.
12. The detection clause is rendered for every `a : A _⦋1⦌`, with every index evaluation
    using `evaluation ... (ULift.up (ComposableArrows.mk₀ i))`, and concludes
    `IsEquivalenceEdge A a`. Verdict: matches the node's quantifier order and all-index
    hypothesis.
13. The final clause is rendered by the internal-hom `IsEquivalenceEdge` hypothesis on
    `E.app _ a` implying `IsEquivalenceEdge A a`. Verdict: matches the stated equivalent
    conservativity clause.
14. The explicit absence of a diagram model structure, enrichment, combinatoriality,
    properness, and nonempty-index hypothesis is preserved. Verdict: matches.

Edge cases checked: empty `I` (vacuous evaluations and terminal strict diagram category),
terminal and singleton `I`, identity and degenerate edges, zero/initial and terminal
objects, arbitrary `W` including isomorphisms, and independent `u`, `v`, and `t`. None is
excluded by the Lean binders or the explicit `ULift` universe transports.

I searched Mathlib and the project/upstream sources with LeanFinder, Loogle, LeanSearch,
and `rg` for strict-diagram localization, evaluation conservativity, and the exact
declaration name. The hits concern ordinary localization or simplicial evaluation and do
not state this theorem. The dependency declarations were opened directly: enhanced
equivalence edges/evaluation/natural equivalence come from
`Sheaf.CategoryTheory.EnhancedDiagramsCones`, while `largeNerve`, `comparison`, and
`IsLocalization` come from `Sheaf.CategoryTheory.FiniteReedyLocalization`. No duplicate
definition or existing theorem was found.

One bookkeeping mismatch was found: the base node's `stmt_deps` listed only
`def-cbc-enhanced-diagrams-cones`, although the signature directly uses the landed
`FiniteReedy` localization interface. I retained the worker's authorized repair by adding
`def-coef-coherent-localization-interface` to the sandbox node's `stmt_deps`; no statement,
proof, source, or dependency declaration was otherwise changed. The theorem source has
one `sorry` proof, no hollow definition, no unbound variables, and all declaration and
module docstrings carry the source place and `(blueprint: lem-coef-strict-diagram-evaluation-conservative)`.
The required `scompile.py` check passed for the module in sandbox and library modes with no
errors or warnings.

### Resumed worker verification (2026-10-17 UTC)

Reopened the original and sandbox nodes, all statement dependencies and the used
declarations with their docstrings. The earlier independent second-reading section is
preserved above; this resumed worker did not initiate another reader or deliver the branch.
The only node deltas remain `lean` and the permitted landed interface addition to
`stmt_deps`. The signature is unchanged and the record date is refreshed in UTC.
Re-ran the prescribed LeanFinder, Loogle, Mathlib grep and upstream/project searches;
there is still no exact existing theorem. Re-ran `scompile.py`: sandbox and library
compiles both passed without errors or warnings (2.2 s and 2.4 s respectively).

## Second reading by Q33

Independent reading on 2026-10-17 of the base and sandbox node, the delivered module,
all statement dependency records, their actual source declarations, and the node's ten
proof steps. There is no repair note for this item. The earlier reading above is not the
basis for this verdict.

### Objects, hypotheses, and conclusion, item by item

1. Ordinary category M with U-small Hom sets: `(M : Type v) [Category.{u} M]`.
   Verdict: exact; object universe v and small universe u are independent.
2. All U-small limits and colimits: `[HasLimitsOfSize.{u, u} M]` and
   `[HasColimitsOfSize.{u, u} M]`. Verdict: exact; these also supply the initial and
   terminal objects used below, without a separately selected object hypothesis.
3. The specified classes C, F, W: `[CategoryWithCofibrations M]`,
   `[CategoryWithFibrations M]`, `[CategoryWithWeakEquivalences M]`.
   Verdict: exact; these instances merely specify classes, not a diagram model structure.
4. W retract closed: `[(weakEquivalences M).IsStableUnderRetracts]`.
   Verdict: exact arrow-retract closure.
5. W two-out-of-three: `[(weakEquivalences M).HasTwoOutOfThreeProperty]`.
   Verdict: exact.
6. Weak factorization system `(C, F intersect W)`:
   `IsWeakFactorizationSystem (cofibrations M) (trivialFibrations M)`.
   Verdict: exact. Mathlib's trivialFibrations is `fibrations M ⊓ weakEquivalences M`;
   the WFS class contains both lifting-class equalities and factorization.
7. Weak factorization system `(C intersect W, F)`:
   `IsWeakFactorizationSystem (trivialCofibrations M) (fibrations M)`.
   Verdict: exact; trivialCofibrations is `cofibrations M ⊓ weakEquivalences M`.
8. Functorial factorizations for both pairs: the two `HasFunctorialFactorization`
   instances on exactly these pairs. Verdict: exact; the existing class asserts a
   nonempty functorial factorization datum, with no added enrichment assumption.
9. Initial object 0 and full cofibrant part M_c: `CofibrantObject M`.
   Verdict: exact. Read Bifibrant.lean and IsCofibrant.lean: the full subcategory's
   predicate is `Cofibration (initial.to X)`. An arbitrary initial choice is immaterial
   because WFS lifting classes respect isomorphisms.
10. Any U-small ordinary index category: `(I : Type u) [Category.{u} I]`.
    Verdict: exact; no nonemptiness, finiteness, or Reedy degree is assumed.
11. W restricted to M_c and objectwise W_I on strict diagrams:
    `((weakEquivalences M).inverseImage CofibrantObject.ι)` and its `.functorCategory I`.
    Verdict: exact. Read the latter definition: it tests every `f.app i` under W.
12. Enlarged nerves and arbitrary coherent localization presentations B and A_I:
    `(B A : SSet.{max u v t})`, `qB`, `hqB`, `qA`, `hqA`.
    Verdict: exact. Read `largeNerve`, `Inverts`, `localDiagrams`, `IsLocalization`:
    simplices are actual ULift data; localization includes quasicategory structure,
    inversion, and equivalence after actual precomposition on the entire coherent
    functor category, onto the full subcategory of inverting functors. It is not an
    ordinary localization or an equivalence only on cores. The independent ambient
    enlargement t and explicit maxima preserve the differing object and Hom universes.
13. Induced evaluation functors and canonical comparison:
    `∃ E : A ⟶ (ihom (FiniteReedy.largeNerve ... I)).obj B` with
    `AreNaturallyEquivalent (qA ≫ E) (FiniteReedy.comparison ... qB)`.
    Verdict: exact expression of the induced map's existence. Read `strictEvaluation`
    and `comparison`: it is curried strict evaluation followed by qB, not an arbitrary
    comparison. Read `AreNaturallyEquivalent`: it specifies an equivalence edge with
    the two required endpoints in the entire functor simplicial set.
14. Detection of every localized arrow by every localized evaluation: for every
    normalized E and every `a : A _⦋1⦌`, the premise tests
    `IsEquivalenceEdge B ((evaluation ... (ULift.up (ComposableArrows.mk₀ i))).app _
    (E.app _ a))` for every `i : I`; the conclusion is `IsEquivalenceEdge A a`.
    Verdict: exact objects, quantifier order, and implication. The arbitrary edge a
    need not come from a strict transformation. Restricting normalization at i gives
    precisely the induced localized evaluation, up to coherent natural equivalence.
15. Equivalent conservativity clause: the last conjunct says
    `IsEquivalenceEdge ((ihom ...).obj B) (E.app _ a) → IsEquivalenceEdge A a`
    for every a. Verdict: exact. `ComponentwiseEquivalence` in the nonpublic proof import
    tests all vertices; every vertex of this lifted nerve is an ordinary object i.
16. No diagram model structure, simplicial enrichment, combinatoriality, properness,
    or saturation hypothesis: none occurs in the signature. Verdict: exact; saturation
    is proved in the node's componentwise homotopy-and-retract argument, not assumed.

### Source and dependencies

Opened [Cisinski's source](https://cisinski.app.uni-regensburg.de/CatLR.pdf), printed
pp. 408--410 (PDF pp. 423--425): Definition 7.9.4, Example 7.9.6, Remark 7.9.7,
Theorem 7.9.8, and specifically the paragraph between (the project server) and (the project server).
The source treats hereditary categories with weak equivalences; this node spells out
an ordinary model-category specialization. Its proof supplies the fraction calculus
and saturation input from the stated weak factorization systems. The Lean retains
exactly that specialization and just the conservativity conclusion, not the stronger
rectification conclusion of the whole theorem. There is no Stacks source for this item.

Read both statement dependency nodes and their signatures. The already landed
`def-coef-coherent-localization-interface` records the actual IsLocalization predicate
in FiniteReedyLocalization; the module name does not import finite-Reedy hypotheses
into this theorem. Retained the authorized addition of that node to stmt_deps.
The other dependency, `def-cbc-enhanced-diagrams-cones`, supplies the existing
IsEquivalenceEdge, evaluation, fullSubcomplex, AreNaturallyEquivalent, and
IsFunctorEquivalence. These definitions contain real data and the required coherent
inverse-triangle witnesses. There is no duplicated notion or unusable interface.
Read the recorded enhanced-functor-calculus statement and ComponentwiseEquivalence;
its module is correctly a nonpublic proof import. The other proof dependencies have
only Mathlib matches or no recorded module, as listed in the worker report. No new
node, dependency module, or statement_change is part of this delivery.

### Edge cases and searches

Empty I is permitted: there is no selected index or Nonempty assumption. The universal
premise then becomes vacuous, and the node's terminal diagram category argument gives
invertibility of every localized edge. Terminal I recovers evaluation of the cofibrant
part. Initial, terminal, and zero objects (when a zero object exists), identity edges,
and degenerate edges are covered. An empty M cannot satisfy the stated completeness
assumptions. There are no schemes, rings, degrees n, or characteristics in this item.
Universes u, v, t are explicitly bound and independent; all ambient nerves and internal
homs have the common maximum universe, without an additional equality assumption.
The predicates hqA/hqB quantify all test quasicategories in that chosen enlarged universe,
as in the recorded localization interface. No arbitrary comparison is tested without
its required coherent normalization.

Ran fresh prescribed searches with different wording from the worker's:

- LeanFinder: "Joint conservativity of derived point evaluations on the localization
  of objectwise cofibrant functors at componentwise weak equivalences": 8 results,
  all ordinary cofibrant-category localization interfaces, none this theorem.
- Loogle: `"CofibrantObject", "evaluation"`: 0 results.
- LeanSearch: "The localized evaluations of a functor category of cofibrant objects
  jointly detect equivalences": 8 results on ordinary localization or reflection of
  limits and colimits. None states the coherent-localization detection assertion.
- Mathlib grep: `functorCategory.*[Ll]ocal|[Ee]valuation.*[Rr]eflect`: 25 results on
  ordinary functor-category limits and colimits, not this assertion.
- Direct rg searches in project CategoryTheory sources, upstream WeilConjectures,
  and dag/lean_names_upstream.json for strict diagrams with conservativity/reflection,
  the exact declaration, and the DAG id: only the downstream FreeDiagramHomotopyDensity
  proof-plan reference. No existing declaration or name collision was found.
- Opened Mathlib's WFS, functorial factorization, componentwise morphism property,
  full cofibrant subcategory, and initial-map cofibrancy definitions directly rather
  than inferring their meaning from search result names.

### Findings and validation

No new mathematical or Lean mismatch was found. The sandbox node differs from the base
only in lean and the permitted landed-interface addition to stmt_deps. No statement or
module repair was needed. This reading changes only the report by adding this independently
checked section; the worker report is preserved.

Verified by exact string comparison that lean.statement equals the theorem signature
from `theorem` to before `:=`. Every Lean line is at most 100 characters. autoImplicit
is false, all variables and universes are bound, and there are no local notations,
private copies, new definitions, or auxiliary proofs. The one theorem has exactly one
sorry. Both source/blueprint docstrings are present; the theorem docstring carries the
node's ten proof steps, including pullback replacement, finite-word fractions, the
actual localized arrow, both cylinder homotopies, the arrow retract, and empty I.
