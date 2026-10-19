## Worker report

The module `Sheaf.AlgebraicGeometry.NagataRelativeGluingDatumDescends` states
`AlgebraicGeometry.nagataRelativeGluingDatum_descends`, with its whole proof `sorry`.
It recovers the fixed raw diagram, rather than asserting finite-stage gluing axioms.
The item and all of its existing fields except `lean` are unchanged. No new nodes or
dependency repairs are needed.

Hypotheses and clauses, matched to Lean:

- The constructed raw datum is `R : NagataRelativeGluingDatum D c hc i₀ f`, using
  the recorded dependency's declaration without making a second definition.
- Its inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`, on a nonempty directed preorder;
  `c : Cone D` and `hc : IsLimit c` fix its limit, and the affine-transition instance
  is quantified over every transition. The recorded interface accepts preorders,
  including the posets of the node; antisymmetry is not needed.
- The fixed qcqs base stage is `i₀`, with `CompactSpace` and `QuasiSeparatedSpace`
  on `D.obj (op i₀)`. The limit has those same properties, as required to form the
  recorded datum (they follow mathematically from the affine limit projection).
- The finite-presentation morphism is `f : X ⟶ c.pt`, with
  `LocallyOfFinitePresentation f`, `QuasiCompact f`, and `QuasiSeparated f`.
  The datum retains the chosen finite presentation, covers and lifts; there is no
  quantification over new choices and no independence assertion.
- "Every chart ... base changes to its named counterpart": the first conjunct
  quantifies over every `j : Σ a, R.base.base.chartIndex a`. `IsPullback` has the named
  open chart as its upper-left object, raw chart as upper-right, limit base as
  lower-left, raw-stage base as lower-right. Its top map is the fixed inverse chart
  comparison followed by the canonical cone projection, transported through
  `rawChart_eq`. The left map is the named chart inclusion followed by `f`;
  the right map is the raw chart's structure morphism and the bottom map is the
  limit projection. Thus this asserts recovery over the base with the canonical
  comparison, rather than merely an abstract scheme isomorphism.
- "Every ... overlap open": the middle conjunct quantifies over every chart pair
  `j k` and every `l : R.base.base.overlapIndex j k`. The two equations pull
  `rawLeftOpen` and `rawRightOpen` back along their respective canonical chart
  cone projections to `R.opens.leftOpen` and `R.opens.rightOpen`. The latter are
  the named opens via `R.opens.leftOpen_eq` and `rightOpen_eq`, under the same
  fixed chart comparisons used in the first conjunct.
- "Every ... overlap map": the last conjunct has the same exhaustive indices.
  Its two equations compare the raw forward/backward maps with respectively
  `(R.overlaps.overlapIso j k l).hom` and `.inv`. The canonical overlap cone
  projections supply both sides' base-change comparisons. The limit isomorphism
  is the named one by `overlapIso_canonical`, expressed via the two named basic
  opens and `R.base.base.basicAgree`. Since all these maps are over their bases,
  the projection equations express equality after base change, by pullback
  uniqueness, exactly as in `nagataMorphismDescends`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.NagataRelativeGluingDatumDescent`:
  `AlgebraicGeometry.NagataRelativeGluingDatum` and its recorded component
  structures/projections (the only statement dependency). Read the full module,
  including its canonical chart, overlap and transport equations.
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`:
  `AlgebraicGeometry.baseChangeCone` and `baseChangeDiagram`; read their full
  definitions: pullbacks, canonical pullback maps, and cone projections.
- Proof imports include the recorded
  `Sheaf.Order.DirectedFiniteUpperBound.le_directedFiniteUpperBound` (declaration
  actually at root namespace: `le_directedFiniteUpperBound`),
  `Sheaf.AlgebraicGeometry.NagataAffineFpDescends`:
  `AlgebraicGeometry.nagata_affine_fp_descends`,
  `Sheaf.AlgebraicGeometry.NagataQCOpenDescentSpec`:
  `AlgebraicGeometry.nagataQCOpenDescent_spec`, and
  `Sheaf.AlgebraicGeometry.NagataMorphismDescends`:
  `AlgebraicGeometry.nagataMorphismDescends`. Their statements and proof docstrings
  were read; all are proof-only imports.
- The remaining Mathlib proof-dependency modules are imported explicitly:
  `CategoryTheory.Limits.Shapes.Pullback.HasPullback` (`pullback`, its projections),
  `AlgebraicGeometry.Pullbacks` (`pullbackSpecIso`), and the affine, qcqs,
  quasi-compactness, finite-presentation and affine-cover-criterion modules listed
  in the node's Mathlib matches. `CategoryTheory.IsPullback` has exactly the four
  maps described above; its full signature and square orientation were checked.

Edge cases checked: empty chart and overlap index types yield vacuous component
claims, as needed for the empty scheme. No nonempty-chart or overlap hypothesis
is imposed. Self-overlaps are included. Both directions are included separately,
without requiring them to be inverses at the raw stage. Arbitrary fixed lifts,
identity transitions and coinciding stages are covered. `u` is explicit, with the
same index/scheme universe as the recorded dependency. No coefficients or
characteristic restrictions are introduced. All variables and universes are bound.

Searches (2026-10-15):

- `msearch.py ... leanfinder`, query "Charts overlap opens and both overlap maps
  of a finite stage raw gluing datum recover their named counterparts under base
  change": eight hits, on generic topological/scheme gluing, including
  `Scheme.Pullback.gluing_t` and `Scheme.Cover.ι_glueMorphisms`; no exact statement.
- `msearch.py ... loogle`, query `CategoryTheory.IsPullback, AlgebraicGeometry.Scheme`:
  twelve hits about generic scheme pullbacks/open immersions; no fixed raw datum.
- `msearch.py ... grep`, query `NagataRelativeGluingDatum|rawLeftOpen|gluing.*descend`
  in Mathlib `AlgebraicGeometry`: zero hits.
- `msearch.py ... leansearch`, query "A finite stage raw relative gluing datum
  recovers charts overlap opens and overlap morphisms after base change": service
  unavailable (Internal Server Error); no verdict assigned to this search.
- `rg -n 'NagataRelativeGluingDatum|rawLeftOpen|relative-gluing-datum-descends'`
  over upstream `WeilConjectures` and project `lean/Sheaf`: project definition and
  downstream consumers only; no upstream or project theorem matching this item.
- `grep -rn 'lemma-nagata-relative-gluing-datum-descends'` over upstream
  `WeilConjectures`: zero hits. Search for the chosen theorem name in upstream,
  project and `dag/lean_names_upstream.json` also returned zero hits.

Validation: the delivered module compiled cleanly with `scompile.py` on the server
(5.2 seconds, nice 19, two threads, 60-second per-file limit). No local compiler
was run. The theorem's docstring gives all five proof steps from the node,
including the finite-presentation checks for both overlap-map descents.

## Second reading by NG

Independent second reading, 2026-10-15. I read the item node and its five proof
steps, the dependency node def-nagata-relative-gluing-datum-descent and its entire
recorded module, RelativeFiniteAffinePresentation, and Stacks limits.tex,
lemma-descend-finite-presentation (Tag 01ZM), including the hypotheses and the
proof of (1). The source's stages i₂, i₃ and i₄ recover respectively affine
charts, overlap opens, and the overlap identity maps. Finite-stage gluing
relations are imposed later at i₅. This item correctly stops before that step.
There is no statement_change and no new node or dependency module in this delivery.

Object/hypothesis/conclusion checklist (the implicit context of the item's short
statement is supplied by its definition dependency):

1. Nonempty directed index set and inverse system with affine transitions:
   `{I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]`,
   `D : Iᵒᵖ ⥤ Scheme.{u}`, and the transition `IsAffineHom` instance.
   Verdict: matches the recorded interface and includes every directed poset.
   Using a preorder does not discard a source case or require antisymmetry in
   any of these comparisons.
2. The specified limit S: `c : Cone D` and `hc : IsLimit c`.
   Verdict: a specified limit cone, with its actual canonical projections;
   the statement does not substitute arbitrary maps to stages.
3. Fixed qcqs stage: `i₀` and its `CompactSpace`/`QuasiSeparatedSpace` instances.
   Verdict: exactly the dependency node's assumptions. Stacks assumes all
   stages qcqs; the node uses the cofinal tail above one qcqs stage instead.
   On that tail affine transitions imply qcqs. The two instances on `c.pt`
   are the dependency's size/topology interface, with no extra mathematical
   restriction: the projection to i₀ is affine and implies both properties.
4. Finite-presentation morphism X → S: `{X : Scheme.{u}}`, `f`, and
   `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`.
   Verdict: finite presentation, without separatedness, Noetherianity, or
   an affine assumption on X or S.
5. The fixed presentation, chosen lifts and selected raw stage:
   `R : NagataRelativeGluingDatum D c hc i₀ f`.
   Verdict: uses the dependency's data, not a private reconstruction. I checked
   `NagataRawAlgebraData`, `NagataRawChartData`, both open choices and their
   transport equations, `NagataRawOverlapData`, paired morphism choices,
   `NagataRawMorphismTransport`, and `NagataRawFiniteStageData`. These retain
   precisely the fixed choices described by the dependency node. In particular
   the auxiliary linear order is record data, not an additional order instance.
6. Every raw chart recovers its named chart: first conjunct, `∀ j` over
   `Σ a, R.base.base.chartIndex a`, with `IsPullback`.
   Verdict: the top map is the inverse fixed `chartComparison` followed by
   the canonical chart cone projection and `rawChart_eq` transport. The left
   map is the named chart inclusion followed by f; the right and bottom maps
   are the raw chart structure map and `c.π.app (op R.raw.stage)`. The square
   asserts the correct comparison over S. I checked the orientation against
   `baseChangeCone` and `baseChangeDiagram`, whose definitions use pullbacks
   and `pullback.map` with identity on the chart factor.
7. Every raw overlap open recovers its named open: second conjunct, all `j k l`,
   with the two inverse-image equalities for `rawLeftOpen` and `rawRightOpen`.
   Verdict: both sides, including distinct chart stages, are present. The
   equalities live in the limit chart pullbacks. The dependency's `leftOpen_eq`
   and `rightOpen_eq` identify their right sides with the named basic opens
   via the very same fixed chart comparisons used in clause 6. This is the
   required recovery, with no loss from the chosen coordinates.
8. Every raw overlap map recovers its named counterpart: third conjunct, all
   `j k l`, with separate equations for `forwardRaw` and `backwardRaw`.
   Verdict: the source projection followed by the raw map equals respectively
   `overlapIso.hom` or `.inv` followed by the target projection. The maps are
   typed over the raw base, and the limit maps are over S by `leftLimit_eq`,
   `rightLimit_eq` and `overlapIso_canonical`. Thus these equations characterize
   equality after base change by pullback uniqueness; a second base-projection
   equation would be redundant. `overlapIso_canonical` identifies the map with
   the identity between the two named basic opens, through `basicAgree`.
   There is no finite-stage inverse, cocycle, or choice-independence assertion.

Edge cases: the index set cannot be empty in the source and is explicitly
nonempty here (also witnessed by i₀). The finite chart and overlap families may
be empty; RelativeFiniteAffinePresentation has only `Finite`, not `Nonempty`,
fields for them. Universal component assertions are then vacuous as appropriate
for the empty scheme. Empty individual overlaps, zero rings and presentations
with zero generators or relations are not excluded. Identity transitions,
self-overlaps, repeated stages, and non-strict inequalities all type correctly.
There is no field or characteristic assumption. All schemes and the directed
index use the explicit universe u required by the existing dependency; every
source set-sized example can be placed in a common universe. No free universe
or automatically introduced variable occurs in the signature.

Independent searches with different wording:

- LeanFinder via msearch.py: “Inverse limits of schemes finite presentation
  descend affine charts and overlap morphisms recovery base change”: eight
  results, including generic `Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`
  and its auxiliaries; none concerns the fixed raw datum.
- Loogle via msearch.py: `"pullback", "iso"`: twelve generic pullback comparison
  results; none states this recovery theorem.
- grep via msearch.py: `overlap.*(recover|descend)|raw.*gluing`: zero hits.
- Direct rg over Mathlib AlgebraicGeometry for gluing/descent combinations,
  over the upstream WeilConjectures tree, and over the project's lean/Sheaf
  for `NagataRelativeGluingDatum`, `rawLeftOpen` and the proposed theorem name:
  the project has the definition and its consumers, but no existing theorem;
  neither Mathlib nor upstream has this fixed datum. The upstream names table
  also has no chosen theorem-name hit.
- I inspected upstream `Scheme.exists_isPullback_of_finitePresentation` in
  AffineTransitionLimit.lean: its conclusion is an existential finite-stage
  model for X, not recovery of all components of the fixed raw diagram.
  It is not an exact match for this node.
- LeanSearch via msearch.py: “The base change to the inverse limit of each
  fixed descended chart, overlap open and overlap morphism agrees with the
  original gluing diagram”: unavailable, Internal Server Error. No search
  verdict is assigned to that service failure.

No mismatch was found. The module and node record are retained unchanged; only
this independent reading is appended. The module's docstring gives the source
and blueprint id and all five proof steps, including finite presentation of
both overlap models before applying morphism descent. Its single theorem has
whole proof `sorry`; no definition or proof is added in this delivery.
The node's lean.statement was checked programmatically to equal the full file
signature verbatim, and every line is at most 100 characters.

Validation: scompile.py NG lemma-nagata-relative-gluing-datum-descends on the
single delivered module succeeded on the server, 6.6 seconds for the library
file, with no error or warning (nice 19, two threads, 60 seconds per file).
No local compiler or global build was used.
