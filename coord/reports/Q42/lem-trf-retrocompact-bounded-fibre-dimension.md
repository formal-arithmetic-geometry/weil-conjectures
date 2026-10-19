## Worker report

Q42, stage 2, lem-trf-retrocompact-bounded-fibre-dimension.
This repairs the returned immutable head 4b8ba1ddd509. The supplied sandbox contained
only dispatcher markers, with no retained module, node copy or report. This delivery
supplies the missing theorem, its node binding, actual scompile evidence and the
required reading section. It starts from the current published node, including its
seven-step expanded proof. No mathematical statement, dependency or proof is changed.

The module `Sheaf.AlgebraicGeometry.RetrocompactBoundedFibreDimension` states
`AlgebraicGeometry.isOpen_and_isRetrocompact_localFibreDimension_le` with a single
`sorry` proof. There are no definitions, auxiliary theorems or new nodes.

Clause-by-clause correspondence:

- Schemes X and S: `{X S : Scheme.{u}}`, with `universe u` explicitly bound.
- The morphism f from X to S: `(f : X ⟶ S)`.
- Local finite presentation: `[LocallyOfFinitePresentation f]`. Its affine-local
  signature in Mathlib was read; it is the declaration recorded on
  `def-sbc-locally-finite-presentation`. This adds no quasi-compactness or
  quasi-separatedness condition.
- An integer n at least zero: `(n : ℕ)`, which ranges over exactly those integers.
  The comparison casts it to `WithBot ℕ∞`, the dimension's existing codomain.
- The scheme-theoretic fibre over f(x) and its point corresponding to x:
  `f.asFiber x : f.fiber (f x)`. Mathlib defines `fiber` as the pullback along
  `S.fromSpecResidueField`; `asFiber` uses the inverse of `fiberHomeo` and
  `fiberι_asFiber` identifies its image with x. This is not the stalk's Krull dimension.
- The local dimension and its bound:
  `topologicalKrullDimAt (f.asFiber x) ≤ (n : WithBot ℕ∞)`. The recorded upstream
  definition is the infimum of the dimensions of all open neighbourhoods of this
  fibre point, exactly the minimum in the node.
- The set U_n: `{x : X | topologicalKrullDimAt (f.asFiber x) ≤ (n : WithBot ℕ∞)}`.
  The same expression appears in both conclusions.
- U_n open in X: the first conjunct `IsOpen {x : X | ...}`.
- U_n retrocompact in X: the second conjunct `IsRetrocompact {x : X | ...}`.
  Mathlib's definition quantifies over every compact open W in X and asserts
  compactness of U_n intersect W. No compactness of the whole U_n is substituted.

Statement dependency declarations, with signatures and docstrings read:

- `def-sbc-locally-finite-presentation`: module
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-pc-scheme-fibre`: module `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField`;
  its existing `asFiber` supplies the canonical point without another definition.
- `def-kun-topological-dimension-at-point`: module
  `WeilConjectures.Mathlib.Topology.KrullDimension`, `topologicalKrullDimAt`.
- `def-weil-constructible-subset`: its Mathlib match names
  `Mathlib.Topology.Constructible`. That file's `IsRetrocompact` is precisely the
  retrocompactness clause needed here; the Boolean-algebra definition of constructible
  subsets itself is not needed in this statement.

Proof imports follow the node's recorded declarations. The module includes
`Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen` for
`AlgebraicGeometry.isOpen_localFibreDimension_le`,
`Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange` for
`AlgebraicGeometry.fibre_dimension_after_base_change`, and
`WeilConjectures.Algebra.LimitFinitePresentation` for
`Algebra.exists_limit_finite_presentation`.
The last source was obtained with `scompile.py --source`, because the older local
upstream source does not contain it. The remaining proof dependencies are supplied
by the existing Mathlib modules on finite presentation/type, affine schemes,
pullbacks, Noetherian rings/schemes/spaces, and quasi-compact/quasi-separated morphisms;
no dependency interface is replaced. The docstring follows all seven proof steps,
including the finite-cover argument and the Noetherian integer model.

Edge cases checked against the statement and Tags 02FZ/02G0:

- X empty: the locus is empty and both predicates apply. There is no point or
  nonempty-fibre premise to exclude it. An empty target likewise forces an empty
  source whenever f exists.
- n = 0: included by the natural-number binder, selecting precisely local
  zero-dimensional fibres; no positivity assumption is imposed.
- An identity morphism: every fibre has one point and dimension zero, so the locus
  is all of X for each n. This is open and retrocompact even for noncompact X.
- Empty locus and whole-source locus are included. Infinite dimensions do not
  satisfy a finite bound in `WithBot ℕ∞`; the ambient dimension type is not truncated.
- No Noetherian, finite-dimensional, separated, quasi-separated, proper, flat or
  quasi-compact hypothesis on X, S or f is introduced. The affine Noetherian schemes
  in the proof are approximating models, not assumptions of the theorem.
- The scheme universe u is arbitrary. There is no independent test-scheme universe,
  index-size restriction or auto-bound variable.

Searches made with the prescribed wrapper (raw records in sandbox searches.jsonl):

- LeanFinder: "For a locally finitely presented morphism of schemes the locus of
  points where local fibre dimension is at most n is open and retrocompact".
  Eight hits, headed by LocallyOfFinitePresentation and open-map/quasi-finiteness
  results; none gives this locus theorem. Digest ac51a42c8011baf8.
- Loogle: `IsRetrocompact`. Twelve hits: the predicate and basic closure,
  compactness and constructibility lemmas; none is a fibre-dimension theorem.
  Digest af6fd3ef6aa80e0e.
- LeanSearch: "The bounded local fibre dimension locus of a locally finitely
  presented scheme morphism is open and retrocompact". Eight hits including
  basic-open retrocompactness and local finite presentation; no theorem for this
  locus. Digest 119cef6038a749ff.
- Wrapper grep in Mathlib/AlgebraicGeometry:
  `topologicalKrullDimAt|[Ff]iber.*[Dd]imension|[Dd]imension.*[Ff]iber`, zero hits.
  Digest 4f53cda18c2baa0c.
- Direct rg in upstream WeilConjectures and published lean/Sheaf, for the item id,
  candidate declaration names, and retrocompactness together with dimension:
  no existing declaration of the conjunction or retrocompactness theorem.
  The project's `LocalFibreDimensionOpen.lean` supplies just openness under local
  finite type, and `FibreDimensionAfterBaseChange.lean` supplies invariance, so
  neither is an exact existing match. The broader local-dimension search also
  finds related flat and smooth dimension results, with different hypotheses
  and conclusions. No new definition is needed.

Validation: ran the required command
`scompile.py Q42 lem-trf-retrocompact-bounded-fibre-dimension
lean/Sheaf/AlgebraicGeometry/RetrocompactBoundedFibreDimension.lean`.
It returned exit code 0: sandbox check 5.1 s, library check 9.2 s, with no diagnostics.
The complete wrapper output is retained in sandbox `scratchpad/compile.log`.
All declaration signatures, universes and the 100-character line limit were checked.

Attribution finding in the return: `lean.by` is Q42, its module author is Q42 and
this report names Q42 and the exact item. The inherited `created` field describes
stage-1 provenance (Q66 created this subsidiary node while splitting
`lem-trf-pure-relative-dimension-finite-stage`); it is not the stage-2 worker binding.
Existing-node stage-2 ownership and deliver2 permit changes only to `lean`, so that
historical provenance is retained. No new node with Q66 or another item is submitted.
The maintainer can correct historical provenance separately if its stage-1 attribution
was itself erroneous; it is not used as this delivery's authorship.

No STATEMENT-DISPUTED finding, mathematical node fault, missing notion or statement
correction is needed.

## Second reading by Q42

This section is an explicit author re-reading, not an independent second worker:
the current dispatcher brief forbids starting other agents and assigns independent
review to the maintainer. With the current node and final module open, I compared
each clause again. X, S and f are the same scheme objects and morphism; the only
morphism hypothesis is local finite presentation; n covers every nonnegative integer;
`asFiber` selects the point in the actual scheme-theoretic fibre; the existing local
topological dimension is bounded by that n; and the two conjuncts assert openness
and retrocompactness of exactly that locus in X. No clause was added or dropped.

Compared with the returned head's findings, the concrete changes are the missing
Lean declaration and exact signature binding, clean scompile evidence, this explicit
reading heading and clause audit, and the Q42/item identification in the stage-2
metadata and report. The inherited stage-1 created record has the distinct provenance
meaning described above. There are no dependency/new-node modules to audit, no
statement change and no unresolved mathematical mismatch. The maintainer's fresh
independent reading remains the independent review.
