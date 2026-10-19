## Worker report

This repairs returned head 329948ab8383. The delivered declaration is
`SSet.Enhanced.Nonsymmetric.operadicLocalizationOperationCriterion`, in
`lean/Sheaf/CategoryTheory/OperadicLocalizationOperationCriterion.lean`.
The theorem has `sorry`; `colorFiberMap` has actual pullback-lift data. Against
current shared main only `lean` and `stmt_deps` change. The latter gains the
already landed `lem-coef-operadic-operation-segal-product`. The item's statement,
proof and proof dependencies are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* Small infinity categories are `M O : SSet.{u}` with explicit quasicategory
  instances. All ordinary targets `P` use the same arbitrary small universe `u`.
* `m` and `o` map to `monoidalSimplexBase.{u}`. `hM : IsGeneralizedOperad m` and
  `hO : IsOperad o` give the recorded nonsymmetric generalized and ordinary
  operad axioms, including inner fibrations, inert lifts, Segal comparisons and
  relative-limit axioms.
* `M_[0]` being a space is already the Kan-zero-fiber conjunct of `hM`.
  `hO1 : KanComplex (fiber o (monoidalBaseVertex 1))` is exactly the separate
  one-fiber hypothesis for `O`.
* `hf : IsLaxMonoidalInfinityFunctor m o f` expresses inert preservation and
  includes the base equation `f ≫ o = m`.
* `hcolor : IsFunctorEquivalence (colorFiberMap f hf.1 1)` is the equivalence on
  the actual canonical color-fiber map, defined by the pullback lift.
* A color is `x : M _⦋0⦌` with `m.app _ x = monoidalBaseVertex 1`.
* The operation spaces use existing `operations m x` and
  `operations o (f.app _ x)`. Unfolding `operationSubcomplex`, their objects are
  active arrows into the specified output, with `IsActive` preserving both
  ordinal endpoints. Their higher simplices are coherent comma simplices whose
  source lies in `(core M) ⊓ constantOrdinalSubcomplex m`. Thus every source edge
  is an equivalence and its entire base simplex is constant. Arity-changing
  triangles are excluded, while all permitted higher coherence remains.
* The hypothesis on the induced operation comparison is now
  `∃ e, IsOperationMap m o f x e ∧ IsFunctorEquivalence e`. The first conjunct is
  the equation
  `e ≫ operationArrows o (f.app _ x) =
  operationArrows m x ≫ (ihom Δ[1]).map f`.
  This fixes postcomposition by this particular `f` on all coherent arrow
  simplices. It excludes an unrelated equivalence between the two spaces.
* The conclusion is `∀ P p, IsOperad p →
  IsFunctorEquivalence (restriction p f hf)`. The recorded `restriction` is
  literal precomposition on full marked relative diagrams, including their
  coherent transformations. Precomposition commutes with postcomposition in `P`
  in every degree, giving the claimed naturality. Restricting its quasi-inverse
  and inverse transformations to cores gives the mapping-space universal property
  and the ordinary operadic replacement consequence stated in the node.

The dependency declarations were opened with their full definitions/docstrings:

* `Sheaf.CategoryTheory.CompleteAlgebroid`: the conventions and universe choices
  recorded at `SSet.Enhanced.Algebroid.completeCategory`.
* `Sheaf.CategoryTheory.OperadicAlgebraPresentability`: `IsGeneralizedOperad`,
  `IsOperad`, `algebras`, `markedRestriction` and `restriction` in
  `SSet.Enhanced.Nonsymmetric`; the recorded main theorem is
  `operadic_algebra_presentability`. In particular, the zero-fiber condition is
  part of `IsGeneralizedOperad`, and transformations in `restriction` are general.
* `Sheaf.CategoryTheory.OperadicOperationSegalProduct`: `IsActive`,
  `operationAmbient`, `operationAmbientSource`, `constantOrdinalSubcomplex`,
  `operationSubcomplex`, `operations`, `operationArrows` and `IsOperationMap`,
  all in `SSet.Enhanced.Nonsymmetric`. These are the landed helpers recorded by
  `lem-coef-operadic-operation-segal-product`; no duplicate is introduced.
* `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `commaSubcomplex`, `core`,
  `IsEquivalenceEdge`, `IsFunctorEquivalence` and the coherent transformation
  definitions. `core` tests every edge for an inverse with two inverse triangles.

Recorded proof-dependency imports include `EnhancedDiagramsCones` and
`OperadicWeakApproximation`, the latter supplying `IsWeakApproximation`.
The active-lift criterion and weak-approximation algebra theorem still have no
recorded Lean module on current main; their proof-only imports cannot yet be
added. The theorem docstring now follows all five DAG proof steps.

Edge cases checked: nullary sources are allowed by `IsActive` with `n = 0`;
no positive-arity or nonempty-input assumption appears. An active source change
between arity two and arity one, which the old full subcomplex could retain, has a
nonconstant ordinal edge and is excluded. A noninvertible source edge even within
one arity is excluded by `core`. Identity/degenerate changes and all permitted
higher simplices are retained. Empty operation spaces are allowed without an
inhabitance assumption. For `f = id`, a nonidentity permutation of discrete
operations fails `IsOperationMap`, so an arbitrary equivalence cannot substitute
for the induced map. Empty color fibers are allowed exactly as in the node.

Searches repeated on 2026-10-17:

* `msearch.py ... leanfinder`, query "A map of generalized nonsymmetric infinity
  operads that is an equivalence on color spaces and on canonical fixed arity
  active operation spaces induces equivalences of operadic algebra infinity
  categories": eight hits about simplicial opposite equivalences, the skeletal
  simplex equivalence and simplicial-category structures; none is this criterion.
* `msearch.py ... loogle`, query
  `SSet.Quasicategory, CategoryTheory.Localization`: zero hits, with unknown
  identifier `CategoryTheory.Localization`; that result alone proves no absence.
* `msearch.py ... grep`, query `operad|active.*operation|operation.*space`,
  directory `AlgebraicTopology`: zero hits.
* `rg` in upstream `WeilConjectures/` and project `lean/Sheaf/` for the item id,
  `operadicLocalizationOperationCriterion`, `activeOperationSpace`,
  `def IsOperationMap` and `def operationSubcomplex`: no upstream criterion;
  the project search found the landed `OperadicOperationSegalProduct` definitions
  and prose references in `ManyObjectOperadAccessibility`. Those landed
  definitions are reused, replacing the proposed duplicate node.

Source checked: Gepner--Haugseng,
[Erratum E and Appendix A.6](https://arxiv.org/html/1312.3178), especially E.0.1,
E.0.2 and A.6.5. The corrected slice restricts source changes, agreeing under the
stated groupoidal-fiber hypotheses with equivalences over ordinal identities.
The natural-language item statement needs no correction. There is no
STATEMENT-DISPUTED flag.

## Repairs of the returned review

H3/H12: removed the proposed `OperadicActiveOperationSpace.lean` and its new node.
Its full subcomplex on active objects retained forbidden source changes. The
already landed `operations` imposes the correct source restrictions in every
simplicial degree; its owning node is added to `stmt_deps`. `hops` now also
requires the whole `IsOperationMap` equation before asserting equivalence.

H8: the undocstringed `activeDiagram` is removed with the duplicate module.
The replacement helpers are existing landed declarations with source/blueprint
docstrings. Both remaining delivered declarations have source/blueprint docstrings;
the theorem's docstring now gives all five proof steps.

H11: the following section is a fresh concrete rereading of the node, delivered
file and imported definitions, with findings and repairs. It is the dispatched
worker's self-check; the maintainer performs the independent immutable review.

## Second reading by Q09

I reopened the unchanged node and the repaired Lean file and unfolded the actual
imported operation-space and comparison definitions.

1. The generalized source, ordinary target and inert-preserving map match `hM`,
   `hO` and `hf`; `hf` also contains the base equation. The Kan-zero-fiber
   condition is in `hM`, the separate Kan-one-fiber condition is `hO1`, and the
   color equivalence uses the actual pullback map `colorFiberMap`.
2. Operation objects are exactly the active-arrow vertices in
   `operationSubcomplex`. Its source pullback imposes `core` and
   `constantOrdinalSubcomplex`. This repairs the previous mismatch: a full
   subcomplex on active objects did not restrict the triangles between them.
   No discrete replacement or groupoid completion discards coherence.
3. The old existential equivalence failed to say "induced by f". The new
   `IsOperationMap m o f x e` fixes postcomposition on the complete arrow family.
   The comma source is evaluation of this family, so the equation fixes that
   component too. Subcomplex inclusions are injective; hence it uniquely
   characterizes the actual map on all simplices. This repairs the arbitrary-map
   fault without adding a mathematical assumption.
4. The conclusion uses the recorded `restriction`, whose transformations are not
   restricted to equivalences. It therefore states equivalence of the entire
   algebra categories. Naturality follows from its precomposition formula;
   passing its inverse data to cores supplies the mapping-space consequence.
5. Nullary inputs, empty spaces, degenerate changes, noninvertible fixed-arity
   edges and arity-changing edges were checked as above. The arbitrary universe
   `u` excludes no small universe of the node; `autoImplicit false` binds all
   variables explicitly.
6. The proposed new node duplicated a now-landed construction and is removed with
   its module. The two copied dependency nodes were identical to current main
   and are removed from the packet. Only `lean` and the permitted addition to
   `stmt_deps` differ from current main. The signature is copied verbatim, all
   Lean lines fit within 100 characters, and the theorem alone has `sorry`.

## Validation

The previous attempts were blocked by a read-only transitive dependency:
`SpaceValuedStraightening.Diagrams` was computable while depending on
noncomputable `smallSpaces`. Those attempts did not push. The initial dry run
of this retry still used an older snapshot and reproduced that failure; current
server source now contains its noncomputability fix. No live source was edited
by this worker.

Fresh `scompile.py Q09 lem-coef-operadic-localization-operation-criterion` on
the delivered module passed: it compiled the current operation-Segal dependency,
the sandbox probe and the library module separately, with no errors or warnings.
The sandbox probe took 8.7 seconds and the library module took 3.8 seconds, each
within the unchanged 60-second limit.

## Retained-packet self-check on 2026-10-17

The first prescribed dry run of this retry again stopped in an older overlay
snapshot, `b9afcd2d61e7f9f2d7f44030199fe94629e8d5c9354be11a3404dcf2f3683889`,
with `SpaceValuedStraightening.lean:64:7` reporting
`lean.dependsOnNoncomputable` for `Diagrams`. Reading the current server source
through `scompile.py --source Sheaf.CategoryTheory.SpaceValuedStraightening`
now shows `noncomputable abbrev Diagrams`; the shared source agrees. A fresh
prescribed compilation therefore tests the updated dependency rather than
changing a read-only module in this delivery. The earlier failed-attempt
results are historical.

I reread the saved theorem against the current node and the actual imported
definitions. `hM` includes the Kan zero fiber; `hO1` supplies the target Kan one
fiber; `hf` supplies the base equation and preservation of cocartesian inert
edges; `colorFiberMap` is the actual pullback map. The operation subcomplex
intersects active objects with the preimage of both the source core and the
constant-ordinal subcomplex. A source edge changing arity fails the latter,
and a noninvertible source edge fails the former. `IsOperationMap` fixes the
entire postcomposed arrow family, including higher simplices; source evaluation
of that family determines the comma source coordinate. Thus the existential
map in `hops` is the canonical comparison, rather than an arbitrary equivalence.
`restriction` is precomposition on all coherent transformations, giving the
full categorical conclusion and its naturality; its core gives the mapping-space
consequence. The imported definition `IsActive` permits nullary operations.
Empty color and operation spaces remain allowed.

The module docstring and both declaration docstrings identify the source and
blueprint node; the theorem docstring contains all five proof steps. The
removed `activeDiagram` and duplicate operation-space module remain absent.
Comparison with current shared main finds changes only in `lean` and the
authorized addition of the landed operation-Segal node to `stmt_deps`. The
recorded signature equals the source signature verbatim, every Lean line has
at most 100 characters, and the only `sorry` is the main theorem proof.
The source was also reopened online at
[Gepner--Haugseng, Erratum E and Appendix A.6](https://arxiv.org/html/1312.3178):
the erratum restricts the source-change maps as above and A.6.5 concludes an
equivalence of the entire algebra categories. No additional mathematical
repair was needed beyond the retained H3/H12, H8 and H11 repairs.
