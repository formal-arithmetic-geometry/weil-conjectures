## Worker report

I repaired the returned packet by adding the Lean statement module
`Sheaf.CategoryTheory.LocalizationMonomorphicPushout` and its theorem
`SSet.Enhanced.localizationAtEdges_monomorphic_pushout`. The theorem is stated
with arbitrary simplicial sets in universe `u`, a strictly commuting map of the
two spans, degreewise injectivity only for `u₀` and `v₀`, the three edge
collections and their localization hypotheses, the two image inclusions, and
Mathlib's degreewise pushouts with their induced map. Its conclusion is exactly
`IsLocalizationAtEdges` at the union of the two image collections. The source
and theorem docstrings cite Kerodon 01N7 and 01FJ and include all seven DAG proof
steps. The theorem is the sole `sorry`; no definition is hollow.

I removed the two stage-1 helper node files from this stage-2 repair packet:
the stage-2 return requires only the item module and item Lean record, while the
helpers were artifacts of the rejected stage-1 split and have no Lean records.
The item JSON changes only its `lean` record for delivery; its statement and
stage-1 proof metadata remain available in the retained copy for review.

I checked the signature against the natural-language item clause by clause:
`h₀` and `h₁` are the strict commuting squares, `hu₀` and `hv₀` quantify over
all simplicial degrees, and no hypotheses mention quasicategories or injectivity
of `u₁`, `v₁`, `p₀₁`, `p₀`, or `p₁`. The marked-edge hypotheses use the actual
edge maps at `Opposite.op ⦋1⦌`; the conclusion uses the actual pushout inclusions
`j₀` and `j₁`. Empty spans, empty edge sets, identity maps, degenerate marked
edges, and non-injective right legs are all admitted by the type.

The existing definition `SSet.Enhanced.IsLocalizationAtEdges` was read in
`Sheaf/CategoryTheory/UniversallyLocalizingSimplicialMap.lean`, and the existing
pushout-localization sibling was used only to check the `pushout.map` argument
order. The module imports only `Sheaf.*` and `Mathlib.*`, uses `autoImplicit
false`, and has one theorem proof ending in `by sorry`, as required for a
stage-2 statement packet.

## Second reading by Q13

Independent maintainer second reading of immutable commit
`4431d69c49cc83912063c39e95f98f39250fb60a`, 2026-10-17. This replaces the original
self-rereading paragraph with an independent clause-by-clause review. Verdict: FIX,
with the complete replacement module and Lean record supplied by the maintainer.

| Node clause | Lean rendering | Finding |
| --- | --- | --- |
| Six arbitrary small simplicial sets | `X₀₁ X₀ X₁ Y₀₁ Y₀ Y₁ : SSet.{u}` | Exact; no quasicategory instances |
| Two spans | `u₀`, `u₁`, `v₀`, `v₁` | Correct sources and targets |
| Three vertical maps | `p₀₁`, `p₀`, `p₁` | No injectivity imposed |
| Strict commuting squares | `h₀`, `h₁` | Correct composition order |
| Only the zero legs degreewise injective | `hu₀`, `hv₀`, all `SimplexCategoryᵒᵖ` | Exact |
| Three collections of edges | `V₀₁`, `V₀`, `V₁`, degree one | Arbitrary sets, including empty |
| Three specified localizations | `h₀₁`, `hV₀`, `hV₁` | Recorded `IsLocalizationAtEdges.{u,v}` |
| Two compatibility inclusions | `hV₀₁₀`, `hV₀₁₁` | Actual degree-one image inclusions |
| Degreewise pushouts and their induced map | Mathlib `pushout`, `pushout.map` | Canonical, pointwise presheaf colimits |
| Localization at the union of the images | `IsLocalizationAtEdges` at images under `pushout.inl` and `pushout.inr` | Full functor equivalence, not merely cores |
| No other injectivity or quasicategory hypotheses | All remaining binders inspected | Exact |

Source read online: Kerodon Proposition 6.3.5.3 (01N7), hypotheses (a)--(d) and
(1) implies (2); Example 4.5.5.12 (01FJ) supplies both categorical pushout faces.
Proposition 6.3.1.13(2) (01MS) confirms the localization predicate. These are
Kerodon tags, not Stacks tags. No source-based statement correction is needed.

Both statement dependencies were read in the snapshot, with their complete Lean
records. Their recorded sources were read in the read-only Q13 clone:
`Sheaf.CategoryTheory.EnhancedDiagramsCones` and
`Sheaf.CategoryTheory.UniversallyLocalizingSimplicialMap`.
The exact declarations checked were `IsEquivalenceEdge`, `fullSubcomplex`,
`AreNaturallyEquivalent`, `IsFunctorEquivalence`, `edgeInvertingDiagrams`,
`IsLocalizationAtEdges`, and `IsUniversallyLocalizing`. Edge-inverting diagrams
reuse `CategoryTheory.EnrichedMarkedRealization.invertingDiagrams`; they are not
redefined here. The factorization equation is equality with actual precomposition,
and its equivalence has a coherent quasi-inverse. Test categories live in
`SSet.{max u v}` after degreewise `ULift`; both `u` and `v` remain free. In particular
there is no silent universe equality or vacuous small test universe.

The five proof interfaces were also opened and checked: `isofibration_exponentiation`
(restriction clause), `isofibration_pullback_limit` and its constant-path
`pullbackCoreComparison`, `pointwise_equivalences`, `mapping_composition` and its
`MappingCompositionStatement`, and `infinity_terminal_pullback_criterion` with its
changing-diagram naturality and equivalence-invariance clauses. They support the
four DAG proof steps. Their modules are now imported for the deferred proof.
No missing helper, new node, dependency repair, arbitrary comparison map, hollow
construction, or pro-etale substitute is involved.

Edge cases checked: empty overlap (disjoint union), empty edge collections,
empty simplicial sets whenever the span maps exist, identity maps, degenerate
marked edges, and noninjective right legs or vertical maps. None is excluded.
For empty collections the conclusion remains a localization at the empty union.
The full-subcategory horn argument uses that an inner horn contains every vertex;
the lifted target remains edge-inverting by pointwise equivalences and cancellation.
All six small objects may be put in a common universe; tests use the containing
universe `max u v`, with no finiteness or nonemptiness assumption.

Independent searches, 2026-10-17:

- LeanSearch: “A map between simplicial pushouts along inclusions localizes at the
  union of marked edge images when each span component is a localization”. Hits
  were ring localizations, ordinary model-category localization, and type pushouts.
- LeanFinder: “Localization of simplicial sets compatible with pushouts along
  monomorphisms”. Hits were Quillen horn inclusions and stability of monomorphisms.
- `rg`: searched `IsLocalizationAtEdges`, `localizationAtEdges_monomorphic_pushout`,
  and localization/pushout combinations in the Q13 `lean/Sheaf` tree, the read-only
  slopmaster2 `WeilConjectures` tree, and Mathlib's algebraic-topology tree; also
  checked the upstream name index. No exact existing theorem was found.
  `CommRingCat.isPushout_of_isLocalization` was opened at
  `Mathlib/Algebra/Category/Ring/Constructions.lean:162`; it concerns rings.
  The Quillen framework was opened at
  `Mathlib/AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean:14`;
  it concerns horn fibrations, not this edge-localization universal property.
  `UniversalLocalizationPushout` is a distinct, universally-localizing statement.

Mechanical findings and repairs:

- H9: removed the five conclusion `let`s in accordance with brief-stage2 §2.
  The replacement writes the same `pushout.map`, inclusions and images directly.
- H8: the original theorem docstring had no proof; the module comment alone held
  a seven-part summary of the four DAG steps. The theorem docstring now carries
  all four steps, including the restricted isofibration and explicit quasi-inverse,
  and identifies the dependency nodes used.
- H9: added the five already-stated proof-dependency imports and made the Mathlib
  statement import public, as required by brief-stage2 §3.
- H4/report and H11: the original report omitted search evidence and described a
  self-rereading, rather than a documented independent reading. This independent
  section supplies the searches, full clause matching, edge cases and repairs.
- The original report supplied no item compile command or result. The immutable
  module and corrected module were independently compiled as described below.
  No original compiler failure is inferred from absent evidence.

The original normalized signature exactly equalled its `lean.statement` before
repair. The replacement record contains the normalized signature of the complete
replacement file. The natural-language statement and both dependency records are
unchanged; no §1(C) correction or associated citer audit is necessary.

Compiler evidence, using only the prescribed wrapper:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q13 \
  lem-coef-localization-monomorphic-pushout \
  snapshot/lean/Sheaf/CategoryTheory/LocalizationMonomorphicPushout.lean
```

Exit 0; sandbox `Sheaf/Stage2/Sandbox0.lean` 1.4 s; library
`Sheaf/CategoryTheory/LocalizationMonomorphicPushout.lean` 1.7 s; no diagnostics.

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q13 \
  lem-coef-localization-monomorphic-pushout \
  fixes/LocalizationMonomorphicPushout.lean
```

Exit 0; sandbox `Sheaf/Stage2/Sandbox0.lean` 1.3 s; library
`Sheaf/Stage2/Check.lean` 1.6 s; no diagnostics. The generic library name results
from the merge-compatible basename fix path. The same complete source is checked.
The installed wrapper currently announces server execution; its output confirms
private side-overlay compilation under `/dev/shm/nt-tmp/nt-local-compile-*`, with
60-second file limits. No direct ssh, global build, live-file write, project edit,
claim, delivery, merge, or Git mutation was performed by this review.

The replacement has one theorem with exactly `by sorry`, no definitions, no
unbound variables, no local notation/instances, and maximum line length 85.
The fixes directory contains complete merge-compatible module, Lean-record and
report replacements. Historical worker prose above describes the delivered file;
this independent section records the final corrected form.
