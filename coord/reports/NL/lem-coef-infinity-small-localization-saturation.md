## Worker report

The module `Sheaf.CategoryTheory.InfinitySmallLocalizationSaturation` states
`SSet.Enhanced.infinity_small_localization_saturation`, with its whole proof `sorry`.
It introduces no definitions and proves nothing. The natural-language statement is unchanged.
The docstring carries all five proof steps, including the explicit retract inverse,
the terminal saturated coslice construction, the homotopy-fiber calculation, the
identification of its terminal arrow with the reflector unit, and the two-out-of-three
argument using coherent unit naturality.

Hypotheses and clauses, in statement order:

- The nested small/ambient universes are `u` and `max (u + 1) v`. The containing universe
  `v` is arbitrary, not identified with the small universe. This is the size convention
  supplied through `def-coef-complete-algebroid` and its presentability dependency.
- The infinity category is `(C : SSet.{max (u + 1) v}) [Quasicategory C]`.
  Presentability is `hC : SSet.Presentability.IsPresentable.{u, v} C`.
- The small set of arrows is `(S : Set (C _⦋1⦌)) (hS : Small.{u} S)`.
  This imposes smallness on S, not on all arrows or objects of C.
- The predicate `P : C _⦋0⦌ → Prop` names exactly the local objects: `hP` is the
  equivalence between `P Z` and weak homotopy equivalence of the canonical restriction
  map for every `s ∈ S`. Its source is `Map(C.δ 0 s,Z)` and its target is
  `Map(C.δ 1 s,Z)`; these are B and A respectively. This is a specification of the
  full subcategory in the node, not an additional locality assumption on C.
- `L : C ⟶ (fullSubcomplex C P).toSSet` and
  `adj : CoherentAdjunction L (fullSubcomplex C P).ι` specify the chosen left adjoint
  to the actual full inclusion. They retain the coherent unit, counit, triangle
  identities and universal mapping-space data, as in the recorded adjoints dependency.
  The theorem concerns every such choice; its existence is supplied by that dependency.
- For every edge `f`, the first iff identifies `IsEquivalenceEdge ... (L.app _ f)`
  with weak homotopy equivalence of `canonicalPrecompositionMap` into every `Z`
  satisfying `P Z`. No arbitrary map of spaces replaces precomposition.
- The second iff identifies the same condition on `L.app _ f` with
  `strongSaturation.{u, max (u + 1) v} C S f`. The two iff statements together give
  all three equivalent conditions in the node. The reused saturation is the
  intersection of all classes containing S and equivalences and closed under
  two-out-of-three on triangles, retracts in the coherent arrow category, homotopy
  pushouts, and all small coherent arrow colimits. Each specified closure is present.
- Every unit is the actual component `((evaluation C C X).app _ adj.unitEdge)`;
  the second conjunct asserts its membership in this same strong saturation.
- `HasSmallColimits (arrowCategory C)` asserts existence of small arrow colimits.
  The last conjunct says a coherent arrow cocone is colimiting iff its actual
  postcomposed cocones under evaluation at 0 and 1 are colimiting. The predicate
  `YonedaLimits.ImageCoconeIsColimit` fixes the cocone as `Spaces.mappedCocone`, so
  this clause retains every coherent leg and states computation on source and target.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CompleteAlgebroid`: `SSet.Enhanced.Algebroid.completeCategory`
  and the documented universe convention. Its algebroid construction is imported
  as required by the recorded dependency; no algebroid hypothesis is imposed here.
- `Sheaf.CategoryTheory.PresentableInfinityAdjoints`:
  `SSet.Presentability.presentable_infinity_adjoint_localization`, in particular
  its exact predicate for local objects and its reflector `CoherentAdjunction`.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsPresentable`, `IsSmall`, and `HasSmallColimits`, exported
  by the original dependencies, use the same independent small and ambient universes.
- `Sheaf.CategoryTheory.EnhancedStrongSaturation`:
  `SSet.Enhanced.arrowCategory`, `IsStronglySaturated`, `strongSaturation`.
  The already landed node `def-cbc-enhanced-strong-saturation` is reused through
  its published module and the existing dependency closure; no direct DAG edge is added.
- `Sheaf.CategoryTheory.InfinityReflectionAssembly`:
  `SSet.Enhanced.canonicalPrecompositionMap`, exported by PresentableInfinityAdjoints.
  Its definition uses the canonical mapping-composition class, not a free map.
- `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`:
  `HomotopicalAlgebra.ModelInfinity.CoherentAdjunction`, especially `unitEdge`,
  `unit_src`, `unit_tgt`, and the universal comma objects, exported by the adjoints module.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsEquivalenceEdge`, `fullSubcomplex`, `evaluation`, `coconeCategory`,
  `IsColimiting`, exported by the original dependencies.
- `Sheaf.CategoryTheory.InfinityYonedaPresheafLimits`:
  `SSet.Enhanced.YonedaLimits.ImageCoconeIsColimit` and
  `infinity_yoneda_presheaf_limits`. This already landed proof dependency is added
  to stmt_deps because its exact endpoint-colimit predicate appears in the signature.
- The other three recorded proof dependencies are imported without `public`:
  `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`,
  `Sheaf.CategoryTheory.SmallSaturatedCoslicePresentability`,
  `Sheaf.AlgebraicTopology.ContractibleHomotopyFiberEquivalence`.
  Their theorem signatures and natural-language statements were read; no import is omitted.

Edge cases checked before writing: S empty (every object is local and the reflector
is equivalent to the identity); S consisting only of equivalences (same result);
identity and degenerate edges; arbitrary retracts and pushouts; empty indexing
simplicial set (initial arrow and endpoint initial objects); nonfiltered indexing
shapes; empty mapping spaces (the homotopy-fiber criterion is vacuous over an empty
base and does not require a point). For spaces and S = {empty → point}, the local
objects are the contractible spaces, consistent with the stated restriction test.
The signature imposes no nonemptiness, filteredness, chosen colimits, or additional
universe equality. The full-subcategory predicate is defined by an iff, so no local
object is dropped or added.

Searches for existing declarations:

- `msearch.py leanfinder`, query “Reflective localization of a presentable infinity
  category inverts precisely the strongly saturated closure of a small set of arrows”:
  eight hits, including `OrthogonalReflection.isLocal_isLocal_reflection`,
  `MorphismProperty.isLocallyPresentable_isLocal`, and
  `Localization.LeftBousfield.isLocalization`. These concern ordinary categories
  and Hom-set orthogonality, not coherent mapping spaces. Read the signatures
  and Mathlib `CategoryTheory/Presentable/OrthogonalReflection.lean`.
- `msearch.py loogle`, query `"IsLocal", "Localization"`: twelve hits, all algebraic
  monoid localization; no matching theorem.
- `msearch.py grep`, query
  `strongly.?saturated|strongSaturation|localization.*saturation`, subdirectory
  `CategoryTheory`: zero hits.
- `rg` in upstream `WeilConjectures` for
  `strongSaturation|[Ss]tronglySaturated|small_localization_saturation`: no hits;
  `grep -rn` there for the item id: no hits.
- `rg` in project `lean/Sheaf/CategoryTheory` for the saturation notions found
  `EnhancedStrongSaturation.lean`, the exact reusable definition, plus the
  coslice/arrow-accessibility consumers. It found no theorem stating this item.
- Full proposed declaration-name search in project `lean/Sheaf`, upstream
  `WeilConjectures`, and `dag/lean_names_upstream.json`: no duplicate.

Source checked directly: [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
Definition 5.5.4.5, Remarks 5.5.4.6–7, Proposition 5.5.4.15 and its proof.
The source explicitly gives the three equivalent conditions and explains unit
membership via the naturality square. The saturation definition here includes
retracts and equivalences explicitly, matching the node and the shared definition.

Validation: the prescribed `scompile.py NL lem-coef-infinity-small-localization-saturation`
compiled this complete module cleanly, both the sandbox and the library-path pass,
with no errors or warnings. It also compiled the required current Yoneda overlay.
The only postponed proof is the named theorem, matching this DAG node.
No new nodes, dependency repairs, statement correction, or disputed statement.

Preflight repair: the first dry run rejected an added direct stmt_deps edge to
`def-cbc-enhanced-strong-saturation`. That node has an inherited metadata path
through `lem-coef-sheaf-flat-model`, `lem-coef-dg-derived-quillen-calculus`,
`lem-coef-enhanced-localization-universal`, `lem-coef-enriched-category-tensor-calculus`,
and `lem-coef-algebroid-completion` back to this item. The shared saturation node
cites the sheaf model only for its coherent pushout convention; its Lean definition
is built from enhanced diagrams and presentability and does not import that theorem.
The redundant added edge was removed. At the Lean import level, the definition is
already available through `SmallSaturatedCoslicePresentability`; this does not assert
a direct or transitive DAG edge to the definition node.
The shared declaration and all original DAG dependencies remain in use. No dependency
node was edited. This inherited DAG metadata issue is reported for the maintainer;
it does not require duplicating the definition or a Lean import cycle.

## Second reading by NL

Independent maintainer second reading, 2026-10-17, of immutable delivery
`0df0fddf2603c9ef6a071fd4c05964be972917ab`. The reviewer did not write this delivery.
The required heading identifies the delivery group; this reading replaces the original
placeholder and does not claim a prior group-worker reading.

I read the item node and all three statement-dependency records in the immutable
snapshot, the complete delivered module and report, and the actual shared declarations
in the read-only NL clone. I checked the following correspondence independently:

- The two nested universes are rendered by `u` and `max (u + 1) v`, with both variables
  explicitly bound. `C : SSet` and `[Quasicategory C]` are the infinity category;
  `IsPresentable.{u,v} C` is accessibility plus all small colimits. There is no
  algebroid or monoidal hypothesis on C.
- `S : Set (C _⦋1⦌)` and `Small.{u} S` specify a small collection of actual arrows,
  without imposing smallness on C or on the class of inverted arrows.
- `P` is specified exactly by `hP`. For an edge s, delta 1 is its source A and
  delta 0 its target B. `canonicalPrecompositionMap` therefore has domain Map(B,Z)
  and codomain Map(A,Z). I read its definition and the triangle-characterized
  `MappingCompositionStatement`: its choice fixes the correct homotopy class,
  rather than selecting an arbitrary map with these endpoints.
- `fullSubcomplex C P` keeps all simplices with local vertices. L has this precise
  codomain, and `CoherentAdjunction L ...ι` supplies the actual full inclusion,
  coherent unit/counit, triangle simplices, and universal comma properties.
  Assuming a chosen adjunction is exactly the node's chosen reflector. Its existence
  is separately provided by `presentable_infinity_adjoint_localization`.
- The two iff clauses, for every f, assert equivalence of Lf being invertible,
  the restriction test into every local Z, and membership in `strongSaturation`.
  `IsEquivalenceEdge` uses two actual inverse triangles. The saturation is the
  intersection of classes containing S and equivalences, with all three
  two-out-of-three implications, coherent arrow retracts, homotopy pushouts, and
  every small arrow colimit. None of the required closures is omitted.
- Evaluation of `adj.unitEdge` at X is the unit X -> iLX, by `unit_src` and
  `unit_tgt`; its membership is asserted for every X in the same saturation.
- `HasSmallColimits (arrowCategory C)` and the final iff give existence and
  computation of all small arrow colimits at endpoints 0 and 1.
  `ImageCoconeIsColimit` uses the actual `Spaces.mappedCocone`, preserving the
  coherent legs, rather than merely comparing possible apex objects.

The signature in `lean.statement` is byte-for-byte equal to the file text from
`theorem infinity_small_localization_saturation` up to `:= by`, with trailing
signature whitespace excluded. The node's natural-language statement is unchanged;
there is no statement_change or citer audit to validate. Adding the already recorded
Yoneda node to statement dependencies is authorized by brief-stage2 section 5 and
is appropriate because its image-cocone predicate occurs in the signature.

I read the proof imports' exact signatures as well. The coslice module uses the
shared saturation including retracts, while the prose introduces W without separately
imposing retract closure. These agree by HTT Remark 5.5.4.6; alternatively the entire
terminal-coslice proof can be run directly with G. This is not an extra hypothesis.
The fiber criterion accepts arbitrary universe-sized Kan models, instantiated in
the ambient universe, and does not require a vertex of an empty base. The cone
calculus supplies Kan mapping spaces, full-subcategory quasicategories, the dual
coslice mapping formula, and the componentwise equivalence test.

Source checks: HTT Definition 5.5.4.5 and Remarks 5.5.4.6-7, printed p. 477;
Proposition 5.5.4.15 and its unit-naturality argument, printed p. 482;
Lemma 5.5.5.14, printed p. 491; and the endpoint-colimit assertion of Proposition
5.1.2.2. Gepner-Haugseng arXiv:1312.3178v4, p. 61, Propositions 5.4.2 and 5.4.4,
uses this general theorem. I checked the five proof steps: closure of mapping tests,
terminal saturated coslice, contractible homotopy-fiber identification, comparison
with the reflector unit, and the inverse/naturality argument. No local proof was added.

Edge cases: S empty or consisting of equivalences gives the identity reflection and
only equivalence edges in its saturation; identity and degenerate edges are included.
Empty indexing shapes are permitted, as are nonfiltered shapes. Empty mapping spaces
are permitted, and the fiber test over an empty base is vacuous in the correct way.
In spaces, S = {empty -> point} yields contractible local objects. There is no hidden
nonemptiness, compactness, filteredness, or equality of the ambient and small universes.

Independent searches used LeanFinder for a small collection generating the maps
inverted by a local-object reflector, Loogle for `"Quasicategory", "saturation"`
(no hits), LeanSearch for localization of a presentable quasicategory at edges,
and rg for saturation/localization terminology in upstream, Mathlib and project
sources. Semantic hits are ordinary Category/Hom-set localization, as confirmed by
reading Mathlib's OrthogonalReflection signatures; none is this theorem. The shared
project saturation definition is reused, with no second definition in this delivery.

Compiler reproduction: `python3 /home/ubuntu/weil-launcher-nt/scompile.py NL
lem-coef-infinity-small-localization-saturation
snapshot/lean/Sheaf/CategoryTheory/InfinitySmallLocalizationSaturation.lean`
exited 0. Sandbox check took 5.2 s and library-path check 2.2 s, each under the
60-second limit, with no errors or warnings. The current prescribed wrapper uses
its server-hosted private side overlay; it reported a private `.lbuild` directory.
No direct ssh, global build, live Lean write, repository edit, or Git mutation was
performed by the reviewer.

Findings and corrections: H11 (and the real-reading requirement accompanying H1):
the original second-reading section was a placeholder, now replaced by this reading.
The worker report's garbled HTT numbering is repaired. Its reference to the saturation
being reached through the coslice dependency is clarified as a Lean import path, not
an assertion of a new DAG edge. No mathematical, Lean, or node-record repair is needed.
Both module and theorem docstrings contain source places, blueprint attribution and
all five proof steps. The file contains one theorem with only `sorry`, no definitions,
no private notation, no local instances, and no line over 100 characters. The pro-etale
framework is not used or substituted here.
