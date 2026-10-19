## Worker report

Q49, stage 2, UTC 2026-10-17. Item: lem-trf-oriented-derived-cohomology-continuity.

The module `Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity` states the
node in namespace `AlgebraicGeometry.OrientedDerivedContinuity`. The primary
declaration is `orientedDerivedCohomology_continuity`. It constructs the actual
opposite-slice diagram and its canonical cocone rather than quantifying over an
unspecified comparison map. All theorem proofs are `sorry`; definitions have
real data. Every declaration is recorded in `lean.declarations`, and every
postponed helper law has its source, blueprint id and natural-language proof
in its docstring. The helper laws concern this node's canonical comparison,
not independent replacement theorems for its proof dependencies.

The statement is unchanged. The only addition to `stmt_deps` is the already
published `lem-trf-oriented-point-cohomology`: its `datum`, `Triples`, `topology`
and finite-limit instance supply precisely the two-arrow oriented site needed
here. Its point-comparison theorem is not used. No new nodes, dependency record
repairs or statement corrections are delivered. No statement is disputed.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- Small cofiltered index category: `{I : Type u} [SmallCategory I]
  [IsCofiltered I]`. Its universe is the scheme universe as required by the
  project's size convention, not an independent larger index universe.
- The inverse system of diagrams X_i -> S_i <- Y_i is
  `D : I ⥤ Diagram.{u}` with `Diagram := WalkingCospan ⥤ Scheme.{u}`.
  The objects `.left`, `.one`, `.right` are X_i, S_i, Y_i and the two maps
  `WalkingCospan.Hom.inl`, `.inr` are the named structural arrows. Naturality
  of `D.map a` is precisely the two commuting transition squares.
- Every scheme is quasi-compact: `[∀ i k, CompactSpace ((D.obj i).obj k)]`.
  Every scheme is quasi-separated: the parallel `QuasiSeparatedSpace` binder.
- Both structural arrows are quasi-compact and quasi-separated: the four
  `QuasiCompact`/`QuasiSeparated` binders for `inl` and `inr`.
- All three component transition maps are affine:
  `[∀ {i j} (a : i ⟶ j) k, IsAffineHom ((D.map a).app k)]`.
- The componentwise inverse limits and the induced limiting cospan are
  `(c : Cone D) (_hc : IsLimit c)`. Limits in the functor category are
  componentwise; `c.pt.obj k` is the corresponding limiting scheme and
  `(c.π.app i).app k` its projection. This packages, without strengthening,
  the three limiting cones and their compatible structural arrows.
- P_i and P are `site (D.obj i)` and `site c.pt`. `site` is an abbreviation
  for the published two-arrow `OrientedPointCohomology.datum`; it uses the
  transported small étale sites and the existing three-cover triple topology,
  not a private definition of oriented products.
- The geometric inverse images u_ji^* and u_i^* are `pull (D.map a) Λ`
  and `pull (c.π.app i) Λ`; `star` applies the exact functor termwise and
  localizes it. `baseChange` pulls back all three neighbourhoods, with
  `squareIso` using exactly `etaleBaseChangeComp` and the commuting scheme
  squares. Continuity and exactness are named postponed properties, not
  extra hypotheses of the main theorem.
- The distinguished stage is `(i₀ : I)`. The ring is arbitrary
  `(Λ : Type v) [CommRing Λ]`, with `v` independent of `u`.
- Constant-Λ module sheaves are `Modules d Λ := Sheaf (site d).topology
  (ModuleCat (ULift Λ))`. This is the fixed-coefficient encoding already
  related to modules over the sheafified constant ring by
  `CategoryTheory.constant_ring_module_sheaves` and the published
  `OrientedPointCohomology.fixed` equivalence. The ring lift is to the common
  site universe `max u v + 1`; the canonical ULift ring equivalence identifies
  its module sheaves and linear maps with constant-Λ module sheaves. No bound
  on the size of Λ, torsion, constructibility or dimension is added.
- K ranges over all `DPlus (D.obj i₀) Λ`, where `DPlus` is Mathlib's
  `DerivedCategory.Plus` of that existing module-sheaf category. K is encoded
  as the variable of a functor, so the conclusion quantifies over it and its
  morphisms simultaneously. There is no fixed lower bound common to K.
- `sections` evaluates a sheaf at the final triple; `RGamma` is its existing
  `rightDerivedFunctorPlus`. This is total derived sections on D+, computed
  by bounded-below injective representatives, which are K-injective. The
  existing module-sheaf equivalence supplies enough injectives and the
  published standard derived-category instance. No different derived
  category or ad hoc cohomology is introduced.
- Every integer degree is `(n : ℤ)`. `cohomology d Λ n` is `RGamma d Λ`
  followed by `DerivedCategory.Plus.homologyFunctor _ n`.
- The index is exactly `(Over i₀)ᵒᵖ`, not just the original category or a
  chosen chain. An object is an actual arrow `a : j ⟶ i₀`, and
  `cohomologyDiagram.obj` is `star (D.map a) Λ ⋙ cohomology (D.obj j) Λ n`.
  Its maps are `sliceTransition`, including the slice commutation equality.
- The comparison cocone has point `star (c.π.app i₀) Λ ⋙ cohomology c.pt Λ n`
  and legs `limitLeg`, namely projection pullback followed by the canonical
  composition identification. The main conclusion
  `Nonempty (IsColimit (continuityCocone D c i₀ Λ n))` says that this
  specified cocone is colimiting. Colimits of functors are pointwise, so
  evaluation at each K is exactly the displayed module-valued colimit
  isomorphism, and its inverse is the unique universal comparison inverse.
  This is equivalent to the pointwise comparison being an isomorphism;
  no arbitrary cocone or independently chosen cohomology map occurs.
- Naturality in K is retained by taking the colimit in the functor category
  `DPlus (D.obj i₀) Λ ⥤ ModuleCat _`. All transition and cocone maps are
  natural transformations, not a family of unrelated morphisms.
- Compatibility with restrictions of inverse systems is the named theorem
  `restriction_limitSquare`. It asserts equality of the two canonical maps
  on every stage-to-limit cocone leg for a morphism of diagram systems.
  Its arguments are the distinguished-stage square, stage square and limit
  square with their actual commuting equations. Reindexing is included by
  taking the first-system stage at the image of the second-system index;
  no cofinality assumption is needed for this compatibility. Applying the
  colimit universal property to these leg equalities gives the commuting
  square of the continuity comparisons. The theorem needs no qcqs or
  affineness assumptions because this is functoriality of the maps themselves.
- Adjunction-unit normalization is data, not an invertibility assumption:
  `sectionPullbackApp` evaluates `sheafAdjunctionContinuous.unit` at the
  final triple and restricts along the inverse terminal comparison.
  `derivedPullback` uses the published `rightDerivedFunctorPlusBaseChange`
  on that exact transformation, with identity coefficient transport.
  `cohomologyPullback` takes homology. `baseChangeComp_unique` uniquely
  specifies the three components by the canonical fibre-product composition
  isomorphisms; `baseChangeComp` chooses only this uniquely specified object.
  `directComp` is precomposition and `pullComp` is its adjunction mate,
  constructed with `Adjunction.leftAdjointUniq`. `starComp` is the localized
  mate. `cohomologyPullback_comp`, `sliceTransition_laws`, and
  `limitLeg_naturality` state the corresponding unit/composition laws.

Dependency declarations read and used:

- `def-weil-size-convention` and `def-weil-pbc-scheme-conventions` are
  metatheoretic/convention records. Their Lean content is the explicit
  universes and Mathlib's `Scheme`, `CompactSpace`, `QuasiSeparatedSpace`,
  `QuasiCompact`, `QuasiSeparated` and `IsAffineHom` just listed.
- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.Etale`, `Scheme.smallEtaleTopology`.
- `Sheaf.CategoryTheory.Sites.OrientedProductLargeSites`:
  `CategoryTheory.OrientedProduct.universalWithLargeSites`, its original
  public triple-site constructors and their three generating covering types.
  This is the recorded universal oriented product; the reused published
  `datum` specializes that construction to the two scheme arrows.
- `Sheaf.Paper.OrientedNearbyCycles`:
  `AlgebraicGeometry.OrientedNearbyCycles.EtaleSite`, `etaleTopology`,
  `etaleBaseChange`, `etaleBaseChangeComp`, and their finite-limit and
  continuity interfaces. Their full signatures and docstrings were read.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the transparent alias for
  Mathlib's `SheafOfModules`; the constant-ring specialization is used through
  the existing equivalence, rather than constructing another module category.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, the dependency's Mathlib match; the derived
  sections API provides its standard bounded-below injective realization.
- Added published dependency `Sheaf.TraceFormula.OrientedPointCohomology`:
  `CategoryTheory.OrientedPointCohomology.Triples`, `topology`, `datum`,
  `triples_finiteLimits`, `fixed`, `fixed_enoughInjectives`, `fixed_hasDerived`,
  and `coefficient_hasDerived`. It reuses
  `Sheaf.CategoryTheory.ConstantRingModuleSheaves`:
  `CategoryTheory.constant_ring_module_sheaves`.
- The canonical derived maps use
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange`:
  `CategoryTheory.Functor.rightDerivedFunctorPlusBaseChange`, together with
  Mathlib's `mapDerivedCategoryPlus`, its identity and composition isomorphisms,
  and `rightDerivedFunctorPlus`.

The module imports every recorded module of a proof dependency, without
`public`, as the stage-3 proof plan. The Mathlib proof matches for initiality,
constant diagrams, exact derived functors, cohomology ladders, exact filtered
colimits and the five lemma are imported too. At this reading,
`lem-trf-oriented-triple-limit-descent` and
`lem-sfb-derived-composition-adjunction-normalization` have no recorded module;
they remain proof dependencies, not prerequisites for typing this statement.
Their roles and all eight proof steps are included in the main theorem's
docstring. No proof dependency is silently assumed as a hypothesis.

Edge cases checked:

- I may have parallel arrows and need not be a poset; the actual `Over` slice
  retains the arrows and equations. Cofilteredness already implies nonempty,
  and the named i₀ also prevents an empty instance. No separate nonemptiness
  or directed-poset hypothesis was introduced.
- A single stage and identity transition are included. The transition identity
  is an explicit conjunct of `sliceTransition_laws`. Parallel refinements
  use functor composition and `Over.w`, not a chosen ordering.
- Empty schemes are admitted: qcqs, terminal triples and module-sheaf
  categories still make sense. No inhabited point or nonempty geometric
  fibre assumption is imposed.
- The zero ring and zero complex are included. No faithful coefficient
  action, nonzero object or scalar invertibility occurs.
- n = 0 uses the ordinary unit-derived map; n < 0 is permitted, including
  complexes whose nonzero cohomology starts in negative degree. No assertion
  that every D+ complex vanishes below zero was made.
- Arbitrary coefficient universe v is independent of the scheme universe u.
  The coefficient ULift and enlarged existing small site avoid a universe
  equality assumption or a size restriction on test schemes.
- The limiting scheme diagram is supplied by any genuine limiting cone.
  This includes identity systems and avoids choosing a potentially different
  componentwise-limit construction. `IsLimit` is a universal property, not
  an extra geometric restriction.

Searches for existing declarations (no exact existing statement found):

- `msearch.py` leanfinder, query “Derived global sections of constant module
  sheaves on oriented etale products commute with affine inverse limits”:
  eight hits, headed by `exists_app_map_eq_map_of_isLimit` and
  `exists_appTop_π_eq_of_isLimit`. These concern ordinary affine-transition
  scheme sections, not derived cohomology of oriented products.
- `msearch.py` loogle, query
  `CategoryTheory.Sheaf, CategoryTheory.Limits.IsColimit`: twelve general
  sheafification/free-module-presentation colimit hits, no target statement.
- `msearch.py` grep, query `oriented|vanishing.?topos|cohomology.*limit`,
  subdirectory `CategoryTheory`: zero hits.
- `msearch.py` leansearch, query “Cohomology of oriented products of etale
  topoi commutes with cofiltered limits with affine transition maps”:
  eight ordinary affine-limit/general-colimit hits, no oriented cohomology.
- `rg` in `WeilConjectures/` and project `lean/Sheaf/` for oriented-product,
  cohomology/continuity names and the exact item id found no declaration
  stating the item. The item id in `OrientedProperFibreExchange` is a proof
  citation. Existing `CohomologyContinuity` concerns a weaker special case.
  The DAG and published point-cohomology module supplied the already existing
  two-arrow site instead of a duplicate site definition.
- The four msearch result records, including exact queries and hit names,
  are retained in the sandbox `searches.jsonl`.

Verification: the required `scompile.py Q49
lem-trf-oriented-derived-cohomology-continuity` compiled both its private
sandbox view and the final library-path file without errors or non-sorry
warnings. The latest version is recompiled by the delivery preflight as well.
No library/global build or direct shared-repository mutation was performed.
The report records this worker's self-audit; independent review belongs to the
maintainer's delivery review, as required by the dispatcher's current brief.

## Second reading by Q49

Independent maintainer reading, 2026-10-18, of immutable delivery
c67014a6c6e104c93b9b056a5944e88650cb5482. The reviewer did not write or previously
second-read this delivery. This section replaces the delivered placeholder; it does
not claim that the original worker performed an independent second reading.

### Sources and dependency interfaces actually read

Read the item JSON and its eight statement-dependency JSON files from the immutable
snapshot, the entire delivered Lean module, and the worker report. Read check-brief2.md,
brief-stage2.md and delivery-errors.md, including H1–H13.

Read ILO Exposé XI, printed pp. 175–181 (PDF pp. 181–187): 1.10(b), localization
(1.b)–(1.c), 2.5 and its finite-cover coherent triple-site construction, and 2.7,
particularly (2.c)–(2.e) and (*) following (2.f). The source works with coherent topoi
and coherent arrows, consistent with the node's qcqs schemes and arrows. This is not
an assertion that the PDF itself states the full general affine-transition theorem:
the node explicitly derives that generalization through finite-cover site continuity.
Read Stacks sites.tex, situation-inverse-limit-sites and lemma-colimit-sites (09YL),
and sites-cohomology.tex, lemma-colim-sites-injective and lemma-colimit (09YP).
Their finite-cover condition is essential and is retained in proof step 2. Read
Stacks derived.tex, definition-K-injective (070H), and Mathlib's corresponding
CochainComplex.IsKInjective class (KInjective.lean:42).

Opened the exact interfaces in the read-only Q49 clone and upstream sources:
OrientedProductUniversal (Triples, generators, topology), OrientedProductLargeSites
(largeTriples, largeGenerators, largeTopology, universalWithLargeSites),
OrientedNearbyCycles (EtaleSite, etaleTopology, etaleBaseChange, siteMorphism and
composition interfaces), OrientedPointCohomology (Triples, topology, datum,
triples_finiteLimits, fixed, fixed_enoughInjectives, fixed_hasDerived and
coefficient_hasDerived), RingedSiteModules.ringedSiteModules and
ConstantRingModuleSheaves.constant_ring_module_sheaves. The small-category
triple construction is usable here because AsSmall enlarges both object and hom
universes to the common containing universe; using it does not silently identify
the original small-etale-site object and morphism universes. The large-site
extension is not substituted for a different topology.

Mathlib Scheme.smallEtaleTopology and ofArrows_mem_smallEtaleTopology_iff retain
all jointly surjective covers. ringedSiteModules is exactly SheafOfModules, not a
second module notion. The fixed-ring sheaf encoding is related to it by the
published constant-ring equivalence retaining sections and the scalar action.
Mathlib rightDerivedFunctorPlus is the total right derived functor on D+, with
its localization unit and injective-representative computation. Read upstream
rightDerivedFunctorPlusBaseChange and its Aux and fac declarations: the map
used here is derived from the specified ordinary transformation and normalized
by the derived unit, not an arbitrary natural transformation.

### Hypotheses and conclusions, clause by clause

1. A small cofiltered category is exactly I : Type u, SmallCategory I and
   IsCofiltered I. The same index universe as Scheme.{u} follows the project's
   explicit index-size convention. No poset, chain or countability restriction.
2. D : I ⥤ (WalkingCospan ⥤ Scheme.{u}) supplies all three component schemes,
   both structural arrows and commuting transition squares. CompactSpace and
   QuasiSeparatedSpace quantify over every stage and all three vertices. The
   four morphism instances impose precisely qcqs on both structural arrows.
   IsAffineHom quantifies over every transition and every component. There is
   no Noetherian, separated, finite-type or field assumption.
3. c : Cone D with IsLimit c expresses the three component limits and their
   compatible limiting arrows, since functor-category limits are pointwise.
   It does not select a different limit or add a geometric assumption.
4. site d abbreviates the recorded two-arrow oriented triple datum. It uses the
   original three covering types and the small etale sites transported through
   AsSmall; it is neither the ordinary fibre product nor a pro-etale substitute.
5. Lambda : Type v with CommRing Lambda is arbitrary, independently of u.
   Modules is the fixed-ring sheaf category for ULift Lambda in max u v + 1;
   the standard ring lift preserves the scalar action. DPlus is the standard
   bounded-below derived category of that category. Quantifying over K through
   the source of a functor includes every bounded-below K and its morphisms,
   with no common imposed lower bound.
6. pull is sheafPullback along the constructed componentwise triple base change;
   pull_properties states exactness rather than assuming it in the main result.
   star is its standard termwise derived functor. sections evaluates at the final
   triple. RGamma is rightDerivedFunctorPlus, computed on bounded-below injective
   complexes, which are K-injective. cohomology takes its integer-degree homology.
7. cohomologyDiagram is indexed by (Over i0).op. Its object at j -> i0 is
   star(D.map a) followed by cohomology at j; its maps include the slice equation.
   continuityCocone has precisely the limit cohomology as point and projection
   pullbacks as legs. Nonempty(IsColimit ...) asserts universality of this
   specified cocone, not existence of a freely chosen comparison. Evaluation
   preserves the pointwise colimit and gives the displayed isomorphism for K.
8. Naturality in K is built into the functor-category cocone. restriction_limitSquare
   gives the legwise commuting square for a stage square and compatible limit
   square; it includes index changes by selecting the corresponding stage.
   Colimit universality gives the resulting comparison square. No cofinality
   assumption is needed for this compatibility.
9. sectionPullbackApp literally evaluates sheafAdjunctionContinuous.unit at the
   terminal triple and uses the inverse terminal comparison. derivedPullback
   derives this transformation using rightDerivedFunctorPlusBaseChange.
   baseChangeComp_unique fixes all three components by etaleBaseChangeComp;
   its choose is therefore determined data. pullComp is the adjunction mate
   defined by leftAdjointUniq. starComp, transition, cohomologyPullback_comp,
   sliceTransition_laws and limitLeg_naturality keep that normalization.
   These are genuine helper constructions and laws of the same canonical
   comparison, not extra assumed mathematical input.

Verdict on every clause: agrees. No source-based statement correction, citer
audit, missing independent prerequisite, or universe repair is needed.

### Proof plan and maintainer gates

The theorem docstring includes all eight DAG steps: initial slice reindexing;
finite-cover triple-site descent and site colimit; degree-zero sheaf cohomology
and negative vanishing; derived units and long exact sequence compatibility;
finite truncation induction with exact filtered colimits and the five lemma;
truncation at the requested degree; scalar forgetting retaining canonical maps;
and naturality and unit normalization. In particular it never uses an infinite
spectral sequence or a uniform cohomological-dimension bound. The two proof
prerequisites without recorded modules are cited as future proof inputs, not
silently added as hypotheses or replaced by hollow constructions.

All nine theorem bodies are exactly sorry. Definitions have actual data; no
sorry occurs inside a definition. The only choice of new data, baseChangeComp,
is specified uniquely by all three components. Instances refer to the named
property theorems or existing instances. Every declaration has a source and
blueprint docstring; each postponed law has a proof plan. All 42 declared names
are recorded. autoImplicit is false, u and v are bound, and no line exceeds 100
characters. The lean.statement string matches the source signature verbatim,
ending before := by. No new definition or dependency-repair module is delivered.

Checked the route-pivot dropped list at origin/newtargets-dag: no direct statement
or proof dependency is listed. The item-specific repair-note path is absent at
that ref. The delivered plan uses ordinary derived functors, injectives and
truncations; it contains no enhanced localization, Quillen rectification,
coherent-section, straightening or operadic step.

### Edge cases, searches and compiler evidence

The empty index category is excluded already by cofilteredness and the fixed i0;
this is not an extra exclusion. The single-stage system, identity maps and
parallel arrows are admitted. Empty schemes require no geometric points. Zero
ring and zero complex are admitted. n is an integer, including n < 0 and K with
negative lower bound. Coefficients can live in an independent larger universe.
The conclusion does not assume torsion, constructibility or finite dimension.

Independently searched project and upstream Lean for oriented/vanishing-topos
continuity and cohomology-limit names. Read the apparent matches
WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity and
Sheaf.AlgebraicGeometry.DerivedCohomologyContinuity: the former gives an ordinary
etale vanishing implication, and the latter ordinary etale continuity with finite
coefficients. Neither is this theorem. LeanSearch query "Derived cohomology of
oriented products commutes with cofiltered limits of schemes with affine
transition maps" returned eight generic affine-limit/colimit results, headed by
AlgebraicGeometry.isAffineHom_π_app. LeanFinder query "oriented product etale
cohomology affine inverse limit continuity" returned eight generic Galois,
affine-limit and continuous-cohomology results. No exact existing statement was
found. The worker additionally records Loogle and the other required searches.

Reproduced the compile on the immutable delivered file using:
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q49
lem-trf-oriented-derived-cohomology-continuity
snapshot/lean/Sheaf/TraceFormula/OrientedDerivedCohomologyContinuity.lean

Exit status 0. The installed prescribed wrapper currently uses server overlay
compilation, despite the older local-overlay wording of the brief. It compiled
Sheaf/Stage2/Sandbox0.lean in 32.6 seconds, then
Sheaf/TraceFormula/OrientedDerivedCohomologyContinuity.lean in 35.5 seconds,
under the default 60-second per-file limit. No errors or warnings were printed.
No lake/global build, direct SSH command, live Lean write or project-clone edit
was performed by this reviewer.

### Finding and correction

H11 (also the real-reading requirement behind H1): the delivered second-reading
section consisted solely of a sentence denying that any reading occurred. Its
heading existed but its content did not constitute the required review. This
complete independent reading replaces that placeholder. The worker report is
preserved. The mathematics, module and node record require no changes.
