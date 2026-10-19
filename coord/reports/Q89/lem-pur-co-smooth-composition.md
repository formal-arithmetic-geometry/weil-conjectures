## Worker report

The delivery states `AlgebraicGeometry.ProEtale.cohomologicallySmooth_comp` in
`Sheaf.Paper.CohomologicalSmoothComposition`. The only proof is `by sorry`.
The source is the current main-20261015 blueprint, sec-six-functors-basics,
sk-prop-cohsm/lem-pur-co-smooth-composition.md, order 2337. Its statement agrees
with the DAG statement; no source or DAG statement correction is made.

Hypotheses and clauses, with the file and dependency signatures read together:

- The fixed purity setting is `P : WeilConjectures.PurityFiniteSetting.{u}`.
  Its field datum supplies the finite field and its algebraic closure, its
  coefficient datum supplies the prime different from the characteristic, and
  `extension`, `finiteExtension`, `level`, `level_pos` supply the finite
  coefficient quotient A_{E,n}, with n at least one. `P.Coefficient` is the
  recorded size lift of that quotient, not a new coefficient ring.
- The three schemes over the fixed algebraically closed field are
  `{X Y Z : Scheme.{u}}` and the three `Over (Spec (.of P.field.k))` binders.
  Locally finite type plus quasi-compactness on each structure map renders the
  convention that these are finite-type k-schemes.
- The composable maps are `(f : X ⟶ Y) (g : Y ⟶ Z)`; their `IsOver` instances
  render k-morphisms. `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`
  for each map are precisely the separated finite-type domain of the recorded
  cohomological-smoothness definition, not additional smoothness assumptions.
- The source hypotheses that both maps are cohomologically smooth are
  `hf : IsCohomologicallySmoothCompared P f` and
  `hg : IsCohomologicallySmoothCompared P g`. This is the CURRENT declaration
  recorded on def-pur-co-smoothness, including all three canonical clauses.
- The first conclusion is `IsCohomologicallySmoothCompared P (f ≫ g)`.
  Category-theoretic `f ≫ g` denotes the source's gf.
- The second conclusion is `Nonempty` of the isomorphism from the relative
  dualizing object of `f ≫ g` to the pro-etale `derivedTensor` of the relative
  dualizing object of f with `L((f)^*[ModuleCat.{u + 1} P.Coefficient])` applied
  to that of g. The order of the factors is exactly omega_f tensor Lf* omega_g.
  All three objects use `comparedDualizing`, the recorded canonical comparison
  pullback of the etale exceptional inverse image of the coefficient unit.
  Each explicit HasCompactification argument is supplied by the dependency's
  `P.comparedCompactification` applied to the corresponding target structure
  map. This is the existing Nagata construction, not an added hypothesis or an
  arbitrary object. No equality of unrelated compactifications is asserted.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`
  and `WeilConjectures.PurityFiniteSetting.Coefficient` (def-pur-conventions).
- `Sheaf.Paper.CohomologicalSmoothnessComparison`:
  `AlgebraicGeometry.ProEtale.IsCohomologicallySmoothCompared`,
  `AlgebraicGeometry.ProEtale.comparedDualizing`, and
  `WeilConjectures.PurityFiniteSetting.comparedCompactification`
  (def-pur-co-smoothness). The full signatures and docstrings were read.
- The derived tensor and derived inverse image are the published pro-etale
  declarations already imported by that dependency. No private copies are made.
  The canonical etale tensor and base-change mates underlying the repaired
  predicate were also read with `scompile.py --source` on
  `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps`.

The module includes the compatible proof-dependency imports for exceptional
inverse image, Tor-amplitude pullback, finite-coefficient tensor closure,
etale compact-support comparisons, scalar pullback, pullback composition,
derived pullback/tensor/Hom, finite-level compact-support exchange, ringed
exchange/tensor coherence, and finite-torsion compact supports. Importing the
entire older proof closure was separately tested through scompile.py and fails
before elaboration in `Sheaf.Paper.ProEtaleProperOpenComparison`, because both
ordinary Derived.Comparison and FiniteCoefficient.Derived.Comparison declare
`derivedComparisonAdjunctionPlus`. The wrapper labels this
`INFRASTRUCTURE RETRY (stale live olean)`. Accordingly the legacy proof-only
imports requiring that mixed closure, including ExchangeProjection and old
open-extension comparisons, are omitted under the prompt's duplicate-import
repair instruction to import only the needed side. The canonical maps needed
for this statement come from the current recorded dependency; its canonical
etale API is retained. The natural-language proof still records all seven DAG
steps, including the canonical-map identifications.

Edge cases checked: empty schemes, identity maps, dimension zero, and positive
finite coefficient level. No ordinary smoothness, relative dimension,
properness, nonemptiness, or orientation hypothesis is imposed. The conclusion
uses the same object and site universes as the dependency. Nagata is applied
only to separated finite-type maps with finite-type targets over a field.
Every universe and variable is explicitly bound; autoImplicit is disabled.

Searches retained from the packet and checked against the current sources:

- msearch.py leanfinder, query "composition cohomologically smooth morphisms
  dualizing complex tensor pullback": eight ordinary smooth-composition and
  base-change hits; no statement of this theorem.
- msearch.py loogle, query "IsCohomologicallySmooth, dualizingComplex,
  derivedTensor": zero hits (the old predicate name is unknown to Loogle).
- msearch.py grep, query "cohomological.*smooth|dualizingComplex", subdirectory
  WeilConjectures: zero hits. The saved tool records are in searches.jsonl.
- Current rg on WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json
  for `cohomologicallySmooth_comp|IsCohomologicallySmoothCompared|IsCohomologicallySmooth`:
  only the old and repaired predicate and etale-locality consumers; no exact
  composition theorem. The ordinary etale dualizing-composition theorem has
  ordinary smoothness hypotheses and is not an exact match.

No STATEMENT-DISPUTED issue, new node, or dependency module is introduced.
The item JSON changes only `lean`; its signature is copied verbatim from the
Lean file, normalized for the preflight signature extractor and excluding `:=`.

## Saved-packet repair (2026-10-17)

The required first dry run reproduced the duplicate `upperStarIsoLowerStarInv`
in the old CohomologicalSmoothness import closure. Checking the CURRENT DAG
rather than only the saved report revealed Q97's landed dependency repair:
def-pur-co-smoothness now records CohomologicalSmoothnessComparison. Reusing
that exact interface removes the broken import and supplies the same canonical
notion. The dualizing endpoints now use its `comparedDualizing`, with Nagata
compactifications supplied internally, resolving the saved packet's additional
HasCompactification elaboration concern without extra mathematical hypotheses.
Both cohomological-smoothness hypotheses remain explicit. The seven-step proof
docstring and the node's informal statement and proof are retained.

The original saved report is retained in scratchpad/prior-report.md for history.
No second reading is claimed; a separate worker performs it after this packet.

## Validation

The repaired file passed scompile.py both as a sandbox module and at its
recorded library path, with the compatible proof imports included. There were
no compiler diagnostics. The self-check verified both essential hypotheses,
the source clause correspondence, one sorry-only proof, explicit binders,
100-character Lean lines, and that only lean changes in the item JSON.
The first repaired dry run found two packaging issues: its signature extractor
excludes :=, and it requires the second-reading heading before the independent
reader runs. The record now follows that extractor and the heading below states
the actual pending status. No mathematical change was required.

## Earlier second reading (a previous round; superseded)

Pending: the dispatcher assigns a separate second reader after READY. This
packet contains the worker's self-check only; no independent reading is claimed.

## Second reading by Q89

I opened the node statement, its source blueprint text, the Lean module, and the
recorded declarations in `def-pur-conventions` and `def-pur-co-smoothness`.
The item-by-item comparison is:

- The fixed purity data is rendered by `P : WeilConjectures.PurityFiniteSetting.{u}`;
  its coefficient, finite level, and characteristic conventions are inherited from
  `P`, with the required positive level. Verdict: exact fixed setting.
- The objects are `{X Y Z : Scheme.{u}}`, each equipped with
  `Over (Spec (.of P.field.k))`. Their structure maps have the six
  `LocallyOfFiniteType` and `QuasiCompact` instances. Verdict: these are precisely
  the finite-type k-scheme assumptions required by the dependency predicate.
- The composable arrows are `f : X ⟶ Y` and `g : Y ⟶ Z`, with `IsOver` instances.
  Each has `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`. Verdict:
  exact separated finite-type hypotheses; no smoothness, properness, dimension, or
  nonemptiness assumption was added.
- The hypotheses are `hf : IsCohomologicallySmoothCompared P f` and
  `hg : IsCohomologicallySmoothCompared P g`. Verdict: both source hypotheses are
  present and use the current three-clause canonical comparison predicate.
- The first conclusion is `IsCohomologicallySmoothCompared P (f ≫ g)`, where
  categorical composition is the source's `gf`. Verdict: exact.
- The second conclusion is `Nonempty` of an isomorphism from
  `comparedDualizing P (f ≫ g)` to the derived tensor of
  `comparedDualizing P f` with `L((f)^*[ModuleCat.{u + 1} P.Coefficient])` applied
  to `comparedDualizing P g`. Verdict: exact `omega_f ⊗^L Lf^* omega_g` order,
  coefficient category, site universe, and canonical compactification choices.

The empty-scheme and identity-map cases remain admitted by the scheme and morphism
binders; zero objects are allowed in the derived categories; the coefficient level
is positive as required (`P.level_pos`), so the source's `n = 0` exclusion is
preserved; the coefficient prime remains distinct from the field characteristic;
and no universe is independently restricted. No repair was needed.

For the one-definition check I ran `rg` over the source checkout and this project's
`lean/Sheaf`, finding only the ordinary smooth composition result, the repaired
predicate, and its locality consumers, with no exact composition declaration. I
also ran `python3 /home/ubuntu/weil-launcher-nt/msearch.py Q89
lem-pur-co-smooth-composition grep "cohomologically.*smooth"`; it returned zero
hits. The saved LeanFinder/Loogle searches were checked and likewise found no exact
match. The dependency module and its canonical comparison declarations were opened;
no private copy or new node is needed.

No mismatch was found, so no Lean or node statement was changed. The module was
compiled with `scompile.py` and produced no diagnostics (the proof remains the
single permitted `sorry`).
