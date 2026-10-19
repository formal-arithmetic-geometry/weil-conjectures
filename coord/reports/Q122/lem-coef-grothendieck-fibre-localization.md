## Worker report

Item: lem-coef-grothendieck-fibre-localization. Group Q122, stage 2, 2026-10-17.
Module: `Sheaf.CategoryTheory.GrothendieckFibreLocalization`.
Main declaration: `SSet.Enhanced.GrothendieckFibreLocalization.grothendieck_fibre_localization`.
Only this theorem is postponed, with `sorry`; the other declarations have actual data or define propositions/structures.

The interrupted sandbox contained only four brief markers, no module, node, report, compile log, or delivery receipt. No delivery mutation was repeated. I read the shared node, all ten proof steps, both original statement dependencies and their Lean records, their source declarations, the example CompactObject module/record, the stage contract, delivery-errors H and the repair note. The repair note is resolved stage 1 and concerns splitting proof steps 6 and 7; the current proof already cites their two replacement lemmas. It is not a withdrawn stage-2 interface.

Source checked online: https://arxiv.org/html/1312.3881v4, Theorem 4.21, Corollary 4.22, and Theorem 4.6 / Remark 4.7. The source is covariant. The delivery uses its Cartesian opposite. The node's proof remains unchanged, including its slice-adjunction route in place of the fixed-length reduction. No statement correction is made.

### Representation of the coherent diagram and its comparison

The conclusion uses the intrinsic Cartesian-fibration model of coherent contravariant diagrams. This is a change of presentation, not a restriction to a strict localized diagram: a coherent diagram on NB.op is represented by a Cartesian fibration over NB, and a coherent transformation is represented by a functor over NB preserving Cartesian edges (the source's straightening interpretation). In particular the final quantification is over arbitrary such functors, not over natural transformations of the original ordinary diagram F. All maps are simplicial maps in all degrees, and functor equivalences retain coherent natural inverse equivalences.

`LocalizedTotal F` is the Cartesian representative of the localized diagram. Its total object itself represents E[W_E^-1]. The field `localization : FiniteReedy.IsLocalization ... q` is the full functor-category universal property under N(E), not an equivalence of homotopy categories. Thus it expresses the natural comparison equivalence to the Cartesian total, without choosing a second, unrelated localization. The universal property determines comparison to any other representative, including the projection to NB, and its coherent naturality. The same map q and its fibre restrictions fix the comparison under the original diagram.

The localized diagram's objects are its actual intrinsic fibres, with localization units `fibreUnit`. The `fibre_under` equation says that those units followed by the actual fibre inclusions are precisely N(fibre inclusion) followed by q. The `cartesian_lifts` field says that q sends the original chosen Cartesian arrows to Cartesian arrows. Consequently the transport functor is localized f*, with its coherent diagram data retained in the single simplicial map q and the Cartesian fibration. Neither a family of arbitrary equivalent categories nor a strict functor on merely homotopy categories is substituted here.

### Hypothesis and clause correspondence

- Ordinary B: `{B : Type u} [Category.{v} B]`. Strict contravariant F: `(F : Bᵒᵖ ⥤ Cat.{t, s})`. Functor identity and composition equations are part of Mathlib's functor structure.
- Model structure on each F(b): `[∀ b : B, ModelCategory (F.obj (op b))]`. As required by the recorded model-category conventions, completeness/cocompleteness are the two dependent `HasLimits` and `HasColimits` instance binders. The next two instance binders supply functorial factorizations of (cofibrations, trivial fibrations) and (trivial cofibrations, fibrations). This matches the entire convention of lem-coef-model-infinity-derived-adjunction rather than Mathlib's weaker finite-limit-only ModelCategory class in isolation.
- Every transition preserves all weak equivalences: `preserves_weak` quantifies over arbitrary f, X, Y and a, with only `WeakEquivalence a` as premise. There is no cofibrancy or fibrancy restriction and no Quillen hypothesis.
- Universes: u/v are the independent base object/hom universes; s/t are independent fibre object/hom universes; w is an additional containing universe. All nerves and localizations are in `max u v s t w`. No equality of these universes is imposed. `HasLimits` retains Mathlib's fibre-hom-size convention and is not enlarged to all diagrams in the containing universe.
- E: `Total F` is an abbreviation of existing `SSet.Thomason.Gr Bᵒᵖ F = (Grothendieck (F ⋙ Cat.opFunctor))ᵒᵖ`. An object is op(b,op X), and an arrow's unop has base c→b in B.op and fibre in F(b).op. Its opposite fibre component therefore has exactly direction X→f*Y. Mathlib's Grothendieck composition, reversed, is precisely f*(v) after u, with the functorial equality transports.
- W_E: `totalWeakEquivalences F` is exactly `IsIso a.unop.base ∧ WeakEquivalence a.unop.fiber.unop`. Inverting a base arrow does not change whether it is an isomorphism. Neither all Cartesian arrows nor merely vertical identities are used as W_E.
- N and the map over NB: `FiniteReedy.largeNerve` is the ordinary nerve lifted degreewise. `projection` is the lifted nerve map of Mathlib's forgetful projection followed by double unop. `over_base` is the actual equality q ≫ p = projection F.
- Total localization and comparison equivalence over NB: the theorem produces `L : LocalizedTotal F`; its `quasicategory`, `cartesian`, `localization`, and `over_base` fields give a Cartesian-fibration representative of E[W_E^-1] with its localization unit. `localization` uses the original dependency's full coherent universal property, including mapping spaces of transformations.
- Fibre at b and fibre localization: `fibreUnit b`, `fibre_localization b`, and `fibre_under b` exhibit the strict fibre of the Cartesian fibration as F(b)[W_b^-1], compatibly with the original unit. The `fiber` construction is the previously recorded actual pullback along b; for a Cartesian fibration this represents the intrinsic fibre.
- Transport along f: `liftEdge F f Y` is the lifted nerve of Mathlib's chosen transport arrow (f,id). `cartesian_lifts` requires its q-image to be Cartesian. `fibre_under` fixes its source as the localized f*Y and its target as localized Y. These data characterize localized f* as transport, with all compositional coherences supplied by q and p.
- Mapping-space formula: `MappingFormula L` gives, for every b,c,X,Y, an isomorphism in the existing `FrameSpaceHo` between the coproduct over all `f : b ⟶ c` of `mappingSpace (fiber L.p b) (L.object b X) (L.object b (f*Y))` and `mappingSpace L.total (L.totalObject b X) (L.totalObject c Y)`. `frameSpaceQ` localizes simplicial sets at the recorded realization weak equivalences, so this is exactly equivalence of spaces, not equality/bijection of components. The coproduct is Mathlib's coproduct of simplicial sets.
- Composition and higher coherences: the displayed spaces belong to the single Cartesian quasicategory L.total, whose classifier is the localized diagram described above; q is a simplicial map, not a family of maps of Hom sets. Thus the original ordinary factorization (f,u)=(f,id)∘(id,u) maps to the composite of localized u and the specified Cartesian image of (f,id), including its entire nerve two-simplex and higher compositional simplices. It requires no extra independent arrow-action witness.
- Coherent transformation to arbitrary G: the second conjunct quantifies over arbitrary Cartesian representatives p:P→NB and q:Q→NB, then `(h : P ⟶ Q) (comm : h ≫ q = p)` with `preservesCartesianEdges p q h comm`. This is the intrinsic model of a coherent transformation between the classifying diagrams, and h is its induced map of totals. It includes P=L.total and any coherent G represented by Q, without a strict transformation on F. The implication tests each canonical `rightFibrationFiberMap` for `IsFunctorEquivalence`, and concludes `IsFunctorEquivalence h`. It therefore includes the stated fibrewise-equivalence criterion for the induced map. Existence of the induced map is represented by the transformation itself in this intrinsic model.

### Dependencies and reuse

Read original dependency interfaces:

- `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`: `HomotopicalAlgebra.ModelInfinity.quillenAdjunctionInfinityLocalization`, together with its explicit model assumptions and its use of `HomotopicalAlgebra.FiniteReedy.largeNerve`, `Inverts`, `localDiagrams`, and `IsLocalization`. This delivery imports it publicly and uses those localization and lifted-nerve primitives, not ordinary categorical localization for the total.
- `Sheaf.CategoryTheory.CompleteAlgebroid`: `SSet.Enhanced.Algebroid.completeCategory` and its full-subcomplex definition, with the underlying enhanced simplicial conventions and genuine coherent functor categories. Its source/docstring was read. This delivery imports the module publicly for the node's infinity-category conventions, and does not invent a replacement complete-algebroid notion.

Already landed nodes added to stmt_deps to record reused objects:

- lem-coef-thomason-grothendieck-comparison, module `Sheaf.AlgebraicTopology.ThomasonGrothendieckComparison`: `SSet.Thomason.Gr` is reused as the total category. The underlying Mathlib Grothendieck Hom, composition, forget, inclusion and toTransport declarations were inspected.
- lem-coef-infinity-right-fibration-fibers, module `Sheaf.CategoryTheory.RightFibrationFibers`: `SSet.Enhanced.rightFibrationFiberMap` is the canonical pullback map of fibres used in the final clause. This construction has no right-fibration premise and applies unchanged to Cartesian fibrations.
- lem-coef-marked-relative-cartesian-model, module `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`: `SSet.Marked.Over.relativeFibration false` is the existing Cartesian horn/lift condition. It avoids an unavailable instance for the quasicategory structure on a lifted nerve; it does not assume that structure as an additional hypothesis. The total quasicategory assertion is retained in LocalizedTotal. This predicate has precisely inner-fibration and prescribed-target Cartesian lifting, with no marking requirement added.

Other reused primitives are `SSet.Enhanced.fiber`, `IsCartesianEdge`, `preservesCartesianEdges`, `mappingSpace`, `IsFunctorEquivalence`; and `CategoryTheory.frameLargeNerveMap`, `frameSpaceQ` from the original model-dependency import closure. The latter are explicit canonical lifted nerve maps and the homotopy category of spaces, not private reimplementations.

Proof-only imports are the recorded, already stated EnhancedFunctorConeCalculus, CoherentNerveComparison, HammockInfinityLocalization, KanQuillenRightProper, and SystemLocalizationUniversal modules. The proof-dependency nodes lem-coef-cocartesian-straightening, lem-coef-discrete-base-cocartesian-recognition, and lem-coef-grothendieck-classifier-localization have no Lean record in the current shared snapshot, so there is no module to import for them. No definition from an unstated node is needed to type the intrinsic formulation; their names and role remain in the main theorem's complete ten-step proof docstring for stage 3.

### Edge cases

Empty B: Total F and its localization are empty, the Cartesian condition and fibre assertions are vacuous, and the equivalence criterion compares empty Cartesian total categories. No Nonempty B is required. Empty fibres where allowed by the underlying convention: no object is chosen in any fibre; every formula quantifies over supplied X,Y only. A nonempty base's genuinely complete model categories have their usual initial and terminal objects, as specified in the dependency convention.

A base with no b→c: the coproduct in MappingFormula is empty, as is the total mapping space over this discrete base Hom set. Identity f: the transport edge is the canonical identity-base lift and the fibre-unit compatibility identifies the formula with fibre localization. Nontrivial base isomorphisms: W_E allows them exactly when their fibre component is weak; chosen Cartesian lifts over such arrows are inverted. Noninvertible f with weak u is not in W_E just for that reason. Distinct parallel base arrows remain distinct coproduct summands. Non-Quillen weak-equivalence-preserving transitions are admitted. The transformation h is arbitrary coherent Cartesian functor data, including ones not obtained from strict F-transformations. Independent object and hom universes were retained through the successful compile; no smallness-by-equality shortcut was used.

### Searches actually executed

All four msearch results are saved in the sandbox searches.jsonl:

1. LeanFinder: `localization of Grothendieck construction of relative categories is the Cartesian fibration classified by fiberwise infinity categorical localizations` — 8 hits, ordinary LocalizerMorphism/localization lift results; none state this infinity-categorical theorem.
2. Loogle: `CategoryTheory.Grothendieck, HomotopicalAlgebra.ModelCategory` — 0 hits.
3. Mathlib grep: `Grothendieck|grothendieck`, CategoryTheory — 25 hits, ordinary Grothendieck/fibered-category/site material; reused the actual Mathlib construction after reading it.
4. LeanSearch: `Grothendieck construction localization Cartesian fibration infinity category` — 8 hits, ordinary Grothendieck category structures and ordinary localization. No exact theorem.

Direct rg on `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `lean/Sheaf/CategoryTheory` for Grothendieck fibre/fiber localization found no exact statement. Searching the item id in upstream WeilConjectures found none. Searching `dag/lean_names_upstream.json` for Grothendieck declarations found ordinary sheaf/spectral-sequence results, not this statement. Project search located the already existing Gr construction and Cartesian-fibre helpers; the latter are restricted to equal base/fibre universes, so the module uses Mathlib's same canonical functors directly inside the lifted nerve map to retain independent universes. No second category or composition law is defined. A final collision search for `GrothendieckFibreLocalization|totalWeakEquivalences|LocalizedTotal` in the project, Mathlib, upstream and upstream name index found no existing declaration.

### Validation

`scompile.py Q122 lem-coef-grothendieck-fibre-localization .../GrothendieckFibreLocalization.lean` passed both sandbox and library-path compiles, 5.5 s and 6.3 s, no errors or warnings. The initial diagnostic exposed inference of the lift universe too small, unresolved endpoints of the chosen lift, and the unavailable lifted-nerve quasicategory instance. Repairs supplied all five universe arguments on frameLargeNerveMap, used Mathlib's actual toTransport arrow with its source object explicit, and reused the existing relativeFibration predicate without extra assumptions. No theorem or instance proof was inserted, and no timeout/limit was increased. Every variable and universe is explicit; autoImplicit is false. Every declaration has the source and blueprint docstring, and every line is at most 100 characters.

## Second reading by Q122

Independent maintainer second reading, 2026-10-17, of immutable delivery
6d2c41ef7ffe4f55695e913cc232f3eba1a94b73. This reader did not write the delivery.
This section replaces the worker's explicitly identified self-check; the Worker
report above is preserved verbatim. The original section did not meet the
independence requirement of brief-stage2 section 6 (delivery-errors H11).

I read packet.md, the snapshot item and all five statement-dependency nodes,
the delivered module and its docstrings, the worker report, check-brief2.md,
brief-stage2.md and delivery-errors H. I opened the actual dependency interfaces
in the read-only group clone and the underlying Mathlib Grothendieck construction.
I read Haugseng arXiv:1312.3881v4 online, section 4.2 (including Remark 4.18,
Proposition 4.20, Theorem 4.21 and Corollary 4.22), and Theorem 4.6 / Remark 4.7.
The covariant source becomes the required Cartesian statement by opposites.

Clause-by-clause results:

- B and strict F: the independent Category.{v} B and F : B.op to Cat.{t,s}
  binders express precisely these inputs. There is no cleavage, Quillen,
  properness, combinatoriality or enrichment hypothesis.
- Model structures: ModelCategory, HasLimits, HasColimits and both functorial
  factorization binders match the explicit convention in the model-infinity
  dependency. They are not extra assumptions relative to this node's convention.
- Transitions: preserves_weak applies to every fibre arrow, with no fibrancy or
  cofibrancy condition.
- Ordinary total: Total abbreviates SSet.Thomason.Gr B.op F. I checked
  Grothendieck.Hom, comp, forget, transport, toTransport and the fibre inclusion.
  Reversing base and fibre opposites gives X to f*Y and f*(v) composed with u.
- Weak equivalences: totalWeakEquivalences tests an invertible base and the
  unop fibre component's WeakEquivalence, exactly W_E.
- Nerve and projection: largeNerve is the ordinary nerve lifted degreewise;
  frameLargeNerveMap applies the actual functor on composable strings. projection
  uses forget.op followed by double unop, and over_base is the actual equality.
- Comparison: LocalizedTotal.localization is FiniteReedy.IsLocalization, whose
  restriction functor is an equivalence on full coherent functor categories.
  Thus the Cartesian representative itself is a representative of the total
  localization, with the required comparison under N(E), not a replacement
  assertion merely about ordinary homotopy categories.
- Fibres: fibreUnit, fibre_under and fibre_localization use the actual strict
  pullback fibre and the actual ordinary inclusion. relativeFibration false
  supplies inner lifting and Cartesian lifts with prescribed targets; over NB
  these fibres are intrinsic fibres. No right-fibration restriction is imposed.
- Transport and coherence: liftEdge is the opposite of toTransport, with identity
  fibre component. cartesian_lifts and fibre_under specify localized f* under
  the same simplicial comparison q. The simplices of q retain the strict
  diagram's composition coherences. This characterizes the localized classifier,
  so the intrinsic Cartesian formulation is adequate without a second named
  unstraightening object or an arbitrary choice of diagram.
- Mapping formula: MappingFormula quantifies over every b,c,X,Y and every base
  arrow f; its summand is the mapping space in the actual localized source
  fibre from X to f*Y. frameSpaceQ is localization at realization weak homotopy
  equivalences, so its isomorphism means equivalence of spaces. The Cartesian
  structure and specified lifts also determine the canonical comparison, rather
  than leaving an unrelated abstract mapping-space calculation.
- Arrow action: q carries the whole nerve factorization (f,u)=(f,id)(id,u),
  which gives the localized vertical arrow followed by its Cartesian lift.
- Final clause: arbitrary Cartesian functors over NB are the intrinsic model
  of coherent transformations. rightFibrationFiberMap is the canonical pullback
  map and has no right-fibration premise. The second conjunct applies to these
  functors and tests every actual fibre for IsFunctorEquivalence; it includes
  an arbitrary target G and does not require a strict transformation of F.
- Sizes: u,v,s,t remain independent and w permits a common containing universe.
  Every localized total, fibre and test diagram lives in max u v s t w. Enlarging
  w includes an arbitrary target G. No equality of object and hom universes,
  hidden Nonempty binder or unbound implicit variable occurs.

Edge cases checked: empty base; no arrows b to c (empty mapping coproduct);
identities; distinct parallel arrows; nontrivial base automorphisms;
noninvertible base arrows with weak fibre components (not in W_E);
weak-equivalence-preserving transitions that are not Quillen; terminal and
zero/trivial model categories. Empty fibres are not additionally excluded,
although complete model fibres over a given base object already have terminal
objects by the stated convention.

Reuse and dependency checks: read the recorded declarations in
ModelInfinityDerivedAdjunction, CompleteAlgebroid, ThomasonGrothendieckComparison,
RightFibrationFibers and MarkedRelativeCartesianModel, and the actual
FiniteReedyLocalization, InfinityFibrations, EnhancedDiagramsCones and
CosimplicialFrameMapping primitives used here. Independent rg searches of
Mathlib, upstream WeilConjectures and project Sheaf for both fibre/fiber spellings,
Grothendieck/localization combinations, LocalizedTotal and totalWeakEquivalences
found no duplicate theorem or existing specialized construction. Ordinary
Grothendieck and existing fibre/map notions are reused. The nearby
CartesianGrothendieckColimitFormula helpers have specialized equal universes;
this module instead composes the original general Mathlib functors.
The relative-Grothendieck-localization DAG node is a broader unstated theorem,
not a missing construction needed to type this statement. The three added
statement dependencies already have records. No new node, dependency repair,
statement correction or citer audit is required. The proof-dependency list is
exactly the union of the proof steps' uses.

Pilot gates: all ten listed declarations exist; every declaration has source
and blueprint documentation; the theorem docstring follows all ten node steps.
There is one theorem and its proof is solely sorry. All definitions supply real
data or specify meaningful structures/propositions; no object is chosen from a
hollow existence claim. autoImplicit is false, no line exceeds 100 characters,
and lean.statement is byte-for-byte equal to the module signature before := by.
No pro-etale substitute, global build or live Lean write is involved.

Compiler evidence: the worker recorded clean per-file sandbox/library compiles
of 5.5/6.3 seconds. I independently ran:

    python3 /home/ubuntu/weil-launcher-nt/scompile.py Q122 lem-coef-grothendieck-fibre-localization /home/ubuntu/weil-launcher-nt/reviews-stage2/Q122__lem-coef-grothendieck-fibre-localization__6d2c41ef7ffe/snapshot/lean/Sheaf/CategoryTheory/GrothendieckFibreLocalization.lean

Exit 0; sandbox Sheaf/Stage2/Sandbox0.lean 3.0 s and library
Sheaf/CategoryTheory/GrothendieckFibreLocalization.lean 3.4 s, no errors or warnings.
The installed scompile.py currently routes the side overlay to the server using
nt_srv_compile.py --wire-confirm; this differs from the older local-overlay
implementation described in the brief but provides server confirmation through
the prescribed wrapper. No direct SSH or git command was issued by the reader.

Finding and disposition: H11 reporting defect repaired by this complete report
replacement. Mathematics, signatures, definitions and node records need no
changes. Accept with FIX for this report only.
