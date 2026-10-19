## Worker report

The corrected item follows blueprint main-20261015, order 1376. It states
`AlgebraicGeometry.Etale.hypercohomology_convergence_statement` in
`Sheaf.AlgebraicGeometry.HypercohomologyConvergenceStatement`; its proof is `sorry` as
required for stage 2.

The hypotheses render clause by clause as follows. `X X' Y Y' : Scheme.{u}` and
`f : X ⟶ Y`, `f' : X' ⟶ Y'`, `g : Y' ⟶ Y`, `g' : X' ⟶ X`, together with
`sq : ChosenCartesianSquare g' f' f g`, give the chosen cartesian square. `K` is the
bounded-below cochain complex of abelian sheaves on the small étale site of `X`; `L` is
its derived object and `e : DerivedCategory.Q.obj K.obj ≅ L.obj` identifies them.
`hT` states torsion for every cohomology sheaf of `L`. `a : ℤ`, `ha`, and `hterms` give
the derived and termwise lower bounds below `a`.

The first sequence is
`hypercohomologyCouple (hypercohomologyFirstFunctor f) K`; the second is
`hypercohomologyCouple (hypercohomologySecondFunctor f' g') K`. In each half-plane
clause, every `pageCouple r` term is `IsZero` when `p < 0 ∨ q < a`. In each finite
diagonal clause, `p + q = n` and a nonzero term imply `a ≤ q ∧ q ≤ n`. The two
filtration clauses state `(hypercohomologyFiltration ... K n).IsFinite` for every `n`.
The two existential blocks provide `LimitSubobjects`, degreewise `AlphaColimit`s, their
object equalities with the actual derived homology abutments, `ConvergesTo`, equality of
the cocone maps with `hypercohomologyAbutmentMap`, and equality of every induced image
filtration step with the actual filtration `.step p`. Thus the page index `r` is the
natural-number index whose page is `E_(r+2)`, and the convergence data include the
associated-graded and inverse-limit conditions in `ConvergesTo`.

The dependency declarations are used directly from the landed module
`Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`:
`CategoryTheory.hypercohomologyCouple F K`,
`CategoryTheory.hypercohomologyFiltration F K n`,
`CategoryTheory.hypercohomologyAbutmentMap F K n q`, and
`AlgebraicGeometry.Etale.hypercohomologyFirstFunctor` /
`AlgebraicGeometry.Etale.hypercohomologySecondFunctor`.
I read the full source and docstrings, including the retained
`AlgebraicGeometry.Etale.hypercohomologyFiltrations_spec` and its canonical
base-change comparison clauses. The exact couple has the explicit functor and complex
parameters, and the filtration is the recorded `PBCDecreasingFiltration` with `.step`.
Exact-couple pages and `ConvergesTo` come from
`WeilConjectures.CategoryTheory.ExactCouple` and
`WeilConjectures.CategoryTheory.ExactCoupleConvergence`;
`ChosenCartesianSquare` comes from `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`.
The canonical dependency source is included unchanged for compilation; its lean-only repair record documents the stale compiled interface exposed by this actual consumer.

Edge cases checked: `r = 0` is the initial `E₂` page; `p = 0` and `q = a` remain allowed;
if `n < a` there is no nonzero diagonal term; `n = 0` and arbitrary integer `a` are
allowed; zero complexes, zero sheaves, empty schemes, and every characteristic remain
included. No properness, nonemptiness, Noetherian, or coefficient finiteness assumption
was added. The zero abutment is allowed, so top and bottom filtration steps may coincide.
The sheaf universe uses `AddCommGrpCat.{u + 1}` as in the dependency and no equality of
site object and morphism universes is imposed.

Searches retained from the interrupted attempt (`searches.jsonl`), checked with
source/name searches during this continuation:

- LeanFinder: `half-plane convergence exact couple spectral sequence filtration abutment`:
  eight cochain-complex support/exactness hits, no convergence theorem.
- Loogle: `SpectralSequence.AbutsTo, E₂CohomologicalSpectralSequenceNat`:
  no hits; the first identifier is unknown.
- LeanSearch: `hypercohomology half plane spectral sequence convergence finite filtration`:
  eight unrelated filtration/upper-half-plane results, no match.
- Mathlib grep: `ExactCouple|AbutsTo|DecreasingFiltration` and
  `ExactCouple|AbutsTo|pageInfinity` in `Algebra/Homology`: no hits.
- `rg` in upstream `WeilConjectures` for the item ID and convergence names found
  the FormalSteps docstring only; project `lean/Sheaf` contained the withdrawn old
  three-theorem module and consumers. The source wrapper reports the corrected
  `HypercohomologyConvergenceStatement` unavailable in the published library.
- Reading the available earlier Q33 delivery identified the source-based corrected
  statement and complete citer audit; these have been retained and validated here.

The canonical convergence module uses the existing `PBCDecreasingFiltration` encoding
from `WeilConjectures.CategoryTheory.PBCFiltration`. The recorded generic filtration
node currently points to the mathematically equivalent `DecreasingFiltration` encoding;
no new filtration definition or replacement record is introduced. Reading the source
wrapper confirmed the full signatures of `BigradedExactCouple`, `pageCouple`, the
cycle/boundary tower, `AlphaColimit`, `LimitSubobjects`, `ConvergesTo`, and the filtration
operations. `IsFinite` includes a whole step and a zero step, so it implies both
exhaustivity and separatedness for these decreasing filtrations.

## Statement corrected

The old statement is preserved verbatim in `statement_change.old_statement`: it
uses three couples, explicit stabilization bounds, and a raw exact-couple
filtration presentation. Its all-bidegree formula at `p = 0`, `q = a - 2`
gives `r₀ = max(q - a + 2, p + 1) = 1`, naming `E₁` despite defining only
`Eᵣ` for `r ≥ 2`. The current blueprint main-20261015, order 1376, avoids
that undefined page and states half-plane and finite convergence directly. The current
blueprint has two canonical sequences and the half-plane, finite-diagonal, and finite
convergence clauses. The correction therefore makes the chosen square, representative,
derived object, page indexing, and canonical abutment data explicit so the source
statement is typable, while retaining every current conclusion. The `statement_change`
record audits every current citer: `lem-zl-sheaves-to-complexes` does not hold
because it requires separate compact-support convergence; `lem-weil-pbc-injective-acyclicity-bounded-below`,
`thm-weil-pbc-bounded-below`, `sbc-thm-bounded-derived-smooth-base-change`, and
`lem-kun-0f09` continue to use the finite convergence consequences. No citer was edited.

## Dependency modules

`def-weil-pbc-hypercohomology-filtrations` owns
`Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`. Its complete source is byte-identical
to the current shared source: real D/E terms, truncation inclusions, boundary maps,
canonical image filtrations, all three derived functors, and the full
`hypercohomologyFiltrations_spec` are retained. The published compiled interface omits
F and K on `hypercohomologyCouple` and returns `DecreasingFiltration` from
`hypercohomologyFiltration`, whereas the convergence interface takes
`PBCDecreasingFiltration`. The standalone item compile reproduced `Function expected`
and invalid `.step` errors. Compiling the canonical dependency source first repairs
that interface without a second construction or mathematical change. Its lean-only
record explains this consumer-validated §1(B) repair.

The dependency specification includes the square and bounded representative hypotheses,
the E2 identifications, finite bounds and convergence for all three functors, the
truncation-couple bridge equations, canonical termwise inverse-image comparison,
canonical maps on every page, differential compatibility, and transport of the actual
image filtration. Its definitions contain real data; its named theorem proofs are
`sorry` with the owning node's blueprint and stepwise proof docstrings.

## Validation

The prescribed `scompile.py NE lemma-weil-pbc-hypercohomology-convergence` compiled
both files separately in dependency order with no errors or warnings. The standalone
consumer failure above establishes why the unchanged canonical source must be included
in the private overlay. No global build or live-source edit was performed.

The earlier sandbox lacked the item node and report: the first required dry run
reported zero item node files. The saved old three-theorem module followed the older
blueprint expansion. The corrected two-sequence statement and its existing correction
record were recovered from the earlier Q33 delivery, checked against the current source
and the then-current six citers, and assigned to NE for this delivery. The earlier report's independent
second-reading claim was not carried forward: this dispatcher authorizes direct worker
delivery and the maintainer performs the independent review.

## Repair self-check (2026-10-17)

The first prescribed dry run of the saved packet passed: commit `5ad525db2b`,
with both Lean files compiled separately. The returned immutable head's two
failures are addressed by the explicit `F` and `K` binders on
`hypercohomologyCouple` and the `PBCDecreasingFiltration` result of
`hypercohomologyFiltration`. The retained dependency module and its node are
now identical to current main (the N6 repair), so the wrapper correctly stages
only this item's module, node, and report; it still compiles both saved files.
The earlier dependency-repair discussion above describes why that interface
was needed, rather than a further change to the now-landed dependency.

I reopened the current blueprint statement and proof at order 1376, the complete
retained dependency module, the chosen-square declaration, and the published
exact-couple, convergence, and filtration sources through `scompile.py --source`.
The hypothesis and conclusion correspondence in the worker report still holds.
The actual canonical cocone-map and transported-image equations are retained.
The natural-number page index starts at E2. The zero and boundary cases listed
above remain included. The initial DAG scan found six direct citers. During delivery, the concurrent
repair of `lem-zl-composition-weight-bound` removed its direct citation in favor
of `lem-zl-compact-support-leray-filtration`. The refreshed audit therefore lists
exactly five direct citers, with only `lem-zl-sheaves-to-complexes` marked
`holds: false`. The other search matches mention the item only indirectly,
outside their dependency lists. No citer is edited in this delivery.
The node's recorded signature now preserves the source whitespace verbatim.
The theorem remains a stage-2 `sorry`; no proof or definition was changed.

The push-time preflight caught this concurrent citer change after the successful
dry run. I read the updated weight-composition node, removed only its stale audit
entry, and refreshed this report; the Lean statement and its source correction
are unchanged. The five current citers are `lem-zl-sheaves-to-complexes`,
`lem-weil-pbc-injective-acyclicity-bounded-below`, `thm-weil-pbc-bounded-below`,
`sbc-thm-bounded-derived-smooth-base-change`, and `lem-kun-0f09`.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer fix (maintainer review, 2026-10-18)

The delivered statement is correct against the recorded side dependency, but the per-file
compile (`tools/nt_compile.py`, also used by `lean_file.sh` at landing) resolves
`Sheaf.AlgebraicGeometry.HypercohomologyFiltrations` to the live published module. That
module is not listed in `coord/stage2-source-overrides.json`. In it,
`hypercohomologyFiltration` is a `DecreasingFiltration` with no `.step`, and
`(hypercohomologyCouple F K).D p q` is not definitionally the truncation homology. The
standalone compile therefore failed at the `.step` and cocone-map clauses; this caused the
earlier file-only returns. The reviewer restated the same conclusion through the recorded
declarations that both interfaces share:

- the abutment filtration steps are `imageSubobject (hypercohomologyAbutmentMap F K n (n - p))`,
  which is how `hypercohomologyFiltration` defines its steps;
- finiteness is `IsFinite` of the couple's image filtration `imageFiltration n (A n)`. Because
  this filtration is transported by an isomorphism onto the actual filtration, this is the same
  condition as finiteness of the actual filtration (a whole step and a zero step, hence
  exhaustive and separated);
- the identification `D^{p,n-p} = Hⁿ(F τ≤(n-p) K)` is an explicit equality `hD`. It replaces
  the earlier `congrArg`/`by omega` cast that relied on unfolding the couple. The cocone maps
  are still exactly the recorded `hypercohomologyAbutmentMap`s.

The hypotheses, the half-plane and diagonal clauses, and `ConvergesTo` are unchanged. The
module compiles with no diagnostics standalone against the live library, and again with the
landed side `HypercohomologyFiltrations` source in the overlay.
