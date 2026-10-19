## Worker report

Repair of returned immutable head `42035e9654060b37afd30461bd6648a315d4d9de`.
I read its complete `review.md`, the retained sandbox, and the current shared node
and dependency sources. The current node agrees with the returned non-Lean fields.
The delivery wrapper rebases the repaired packet on the current `newtargets-dag`;
no direct Git command or shared-source edit was made.

The delivery contains one module,
`Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`, with twenty declarations.
The sole postponed theorem is
`SSet.Enhanced.enhanced_functor_cone_calculus`, whose proof is `by sorry`.
Every definition contains actual data or an explicit proposition; there is no choice
of data from an unproved existence assertion. All helpers are owned by this node
and listed in `lean.declarations`, with source and blueprint docstrings.

The source node is an agent-formulated foundation for the opening compactification
choice, rather than a theorem quoted from that compact-support application.
I read the old blueprint unit and the current
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/`
`thm-cbc-finite-level-proetale.md` and `.proof.md`, Scholze Lecture II printed
pp. 13--15, and Kerodon [01L5](https://kerodon.net/tag/01L5),
[02R3](https://kerodon.net/tag/02R3), [01TL](https://kerodon.net/tag/01TL),
and [02HM](https://kerodon.net/tag/02HM). The general comma formula is still
stated as the node's foundation, not attributed to the special coslice result 02R3.
No source/node statement correction is needed: the defects were in its Lean rendering.

Hypotheses and clauses, individually:

- Fixed size convention: `universe u`, `(K C : SSet.{u})`, and
  `[Quasicategory C]`. `K` is an arbitrary simplicial set; no category structure,
  filteredness, inhabitedness, or arrow invertibility is assumed on it.
- Functor quasicategory: `Quasicategory ((ihom K).obj C)` is the first conjunct.
- Every full subcategory is a quasicategory:
  `QuasicategoryMappingSpaceAssertions` quantifies over every quasicategory `Q`
  and vertex predicate `R`, and asserts `Quasicategory (fullSubcomplex Q R).toSSet`.
  In particular it applies to the functor object and all its full subcategories.
- All these mapping spaces are Kan: the same predicate quantifies over all pairs
  of vertices of `Q` and of each `fullSubcomplex Q R`.
- The core of any quasicategory is Kan: `KanComplex (core Q).toSSet` in that predicate.
- Componentwise equivalences: `ComponentwiseEquivalence K C` quantifies over every
  transformation edge and uses the dependency's actual `evaluation K C k` and
  `IsEquivalenceEdge` on both sides of its iff.
- Every functor equivalence induces mapping-space equivalences:
  `FunctorEquivalenceMappingSpaces` quantifies over arbitrary quasicategories and
  their functors, and applies weak equivalence to the actual `mappingSpaceMap`.
- For every diagram: `∀ F : K ⟶ C`, with the existing `coneCategory F` and
  `coconeCategory F`, asserts that both coherent comma pullbacks are quasicategories.
- Cone mapping formula: `ConeMappingSpaceFormula F` uses the actual cone apex map,
  the canonical span described below, and the explicit diagram-fiber identification.
- Limiting cone test: for every cone `μ`,
  `IsLimiting F μ ↔ ConeLimitCriterion μ`; this tests the right leg of that same
  canonical composition span for every `x : C _⦋0⦌`.
- Dual mapping formula: `CoconeMappingSpaceFormula F` uses `towards = false` in
  the same constructions. Its transport arrows run from `μ` to the variable cocone,
  its base arrow is `apex μ → x`, and its right leg is the target cocone. Thus it
  models `a ↦ Δ(a) ∘ μ`, with diagram mapping space `Map(F,Δx)`.
- Colimiting cocone test: for every cocone `μ`,
  `IsColimiting F μ ↔ CoconeColimitCriterion μ`, with the same right-leg test.
- Terminal full subcategory: for every quasicategory `Q`, existence of a terminal
  vertex implies both `KanComplex (fullSubcomplex Q (IsTerminal Q)).toSSet`
  and `IsContractible` of that very full subcategory.
- Initial full subcategory: the identical pair of conclusions for `IsInitial Q`,
  guarded by existence of an initial vertex. Neither conclusion is only about a core.

Canonical span and comparison, repairing the substantive mapping-formula defect:

For the cone apex map `p : P → C`, fixed cone `μ` over `y`, and test apex `x`, put
`R = (calculusFiber p x).toSSet` and
`T = (calculusTransport p true x μ).toSSet`.
An n-simplex of `T` is an actual `Δ[n] × Δ[1] → P` with target the constant simplex
at `μ` and source apex the constant simplex at `x`. Consequently all its composition
squares and their higher compatibilities are the ones already present in the
recorded comma pullback. At vertices these are exactly
`λ ≃ μ ∘ Δ(a)`, not an arbitrary relation between unrelated maps.

The span is `U_C(x,y) ←a— T —r→ R`, using the existing arrow mapping model `U`.
`r = calculusTransportValue p true x μ` is constructed by moving-endpoint
evaluation and a genuine subcomplex lift. The left leg is characterized by
`a ≫ arrowMappingSpaceInclusion = T.ι ≫ (ihom Δ[1]).map p` and asserted to
be a weak equivalence. This equation fixes its action in every degree, and the
monomorphic arrow inclusion makes the map unique. There is no arbitrary q, no
selected inverse of a mere existence witness, and no dependence on the choice of λ
in the left leg. Both `T` and `R` are asserted Kan.

`CalculusCommaFiberIdentification` specifies an isomorphism
`v : R → U_Fun(K,C)(Δx,F)` by the equation saying that it forgets only the apex
coordinate, in every simplicial degree. Again the target's monomorphic inclusion
makes it unique. The already-landed `right_pinch_comparison` supplies canonical,
natural homotopy equivalences `j` between the dependency's right-pinched mapping
spaces and all these arrow models, characterized in every degree by
`rightPinchPrism`.

Thus in the dependency's `spaceHomotopyCategory` the displayed composition map is
represented by `j_diagram⁻¹ · v · r · a⁻¹ · j_C`. This notation describes a span
of actual maps with specified invertible left comparisons; no arbitrary simplicial
composition operation or arbitrary replacement map has been introduced. The test
that it be a weak equivalence is precisely the test on the actual `r`, since `a`,
`v`, and both `j` comparisons are equivalences. This is the right-leg predicate
used in the two universal criteria.

For a cone `λ` over `x`, `CalculusTransportFormula` specifies the inclusion
`i : U_P(λ,μ) → T` by equality after the subcomplex inclusion. The comparison
`e : U_P(λ,μ) → homotopyFiber r λ` is specified by
`CalculusComparison`: after the actual path-model inclusion it is exactly
`lift i (const (diagramVertex (const λ)))`. Both coordinates are fixed in every
degree, including all compatibility homotopies. The formula asserts this very map
is a weak equivalence. Its first coordinate is `i`, hence composition with `a`
gives exactly the apex-arrow map; this supplies compatibility over `U_C(x,y)`.

`CalculusComparisonNaturality` explicitly quantifies over all compatible maps
`(a,c,d)` between such spans and their fixed-arrow spaces, with the commuting
square, basepoint equation and inclusion equation, and states equality of the
comparisons after applying `a ⊗ (ihom Δ[1]).map c`. Because the comparisons have
the specified constant-path coordinates, this covers every induced simplicial
functor or pullback map of the coherent comma models. Inverse choices are never
required to be strictly natural. Opposites are used only in the proof argument;
the cocone formula itself is stated with the correct forward arrow spaces.

Dependencies read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `coneCategory`, `coconeCategory`,
  `comma`, `commaSubcomplex`, `constantDiagrams`, `evaluation`, `diagramVertex`,
  `mappingSpace`, `mappingSpaceMap`, `IsEquivalenceEdge`, `IsFunctorEquivalence`,
  `fullSubcomplex`, `core`, `homotopyFiber`, `IsWeakHomotopyEquivalence`,
  `IsContractible`, `IsLimiting`, `IsColimiting`, `IsTerminal`, `IsInitial`, and
  the Kan-space localization convention. I read their complete signatures and
  docstrings in the recorded module.
- `Sheaf.CategoryTheory.RightPinchComparison`: `arrowMappingSpace`,
  `arrowMappingSpaceInclusion`, `rightPinchPrism`, `right_pinch_comparison`.
  Its recorded node `lem-coef-infinity-pinch-comparison` is added to `stmt_deps`
  as an already-landed node, because the statement now uses its canonical arrow
  models. It was already a proof dependency. Its data and theorem are reused.
- `Sheaf.CategoryTheory.ArrowTargetRightFibration`:
  `fixedTargetSource_rightFibration`, imported as the stated proof dependency.
- Mathlib `AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`:
  `SSet.instQuasicategoryObjIhom`, imported as the exact existing proof-dependency
  match. All other generic proof prerequisites currently have no Lean record;
  they are named in the ten-step docstring, and none is stated in this delivery.
- Mathlib's existing `Subcomplex.lift`, Cartesian `lift`, and internal-hom functor
  provide the actual helper constructions. No independent existing notion is copied.

Edge cases checked mathematically against the unfolded new definitions:

1. Review counterexample: `K = Δ[0]`, `C = N(0 → 1)`, `F = 1`, `μ = id₁`.
   At `x = 0`, both `T` and `R` are singletons: they respectively encode the
   unique square from `0 → 1` to `id₁` and the unique cone `0 → 1`.
   Moving-endpoint evaluation is the singleton isomorphism. No identity edge of 1
   is requested to have source 0. At `x = 1` it is again the singleton isomorphism.
   Thus the corrected criterion holds for the limiting cone as required.
2. Dual review counterexample: same shape and category, `F = 0`, `μ = id₀`.
   At `x = 1`, `T` is the unique arrow from `id₀` to `0 → 1`; `R` is the singleton
   cocone space. The right leg is again the singleton isomorphism, so the colimit
   criterion holds, without pretending that `id₀` has target 1.
3. Empty mapping spaces: in the same category take `F = 0`, cone `μ = id₀`,
   and `x = 1`. There is no apex arrow `1 → 0`, so `T` is empty and the cone fiber
   `R` is empty. `r : ∅ → ∅` is allowed and is a weak equivalence. Dually use
   `F = 1`, cocone `id₁`, and `x = 0`. No basepoint is chosen in either empty R.
4. Nonlimiting cone: for `F = 1` and cone `μ = (0 → 1)`, use test apex `x = 1`.
   `T` is empty while `R` is a singleton, so `r` is not a weak equivalence.
   The corrected criterion detects failure instead of merely testing equinumerosity
   of unrelated mapping spaces. The dual detects the noncolimiting cocone.
5. Empty `K`: every diagram transformation space is contractible and the cone and
   cocone categories reduce to the ambient category up to their canonical terminal
   factors. The criteria become terminality and initiality of the apex, respectively.
   No inhabitance assumption is added on K or C.
6. Empty full terminal/initial subcategories trigger no contractibility assertion;
   nonempty ones have both Kan and contractibility asserted on the full subcategory.
7. Higher homotopies: `T` uses full internal-hom simplices, and the comparisons
   are equalities of simplicial maps in their two coordinates, not equations on
   vertex sets. Right pinching is through the existing canonical prism theorem.

Searches made during this repair (in addition to the returned review's searches):

- `msearch.py leansearch`, query `quasicategory right fibration transport mapping
  space cone homotopy fiber composition`: 8 hits, including ordinary `Functor.mapCone`
  and Quillen fibrations, no enhanced comma formula or canonical transport interface.
- `msearch.py loogle`, query `SSet.Quasicategory, SSet.ihom`: no hits;
  Loogle reports unknown identifier `SSet.ihom` (the actual name is the open `ihom`).
- `msearch.py grep`, query `transport|homotopyFiber|[Cc]one|[Cc]omposition` in
  `AlgebraicTopology/Quasicategory`: 2 hits, on bicategory enrichment and truncated
  homotopy-category composition; neither states this result.
- `rg` of the read-only upstream `WeilConjectures`, `lean/Sheaf/CategoryTheory`,
  and `dag/lean_names_upstream.json` for `EnhancedFunctorConeCalculus`,
  `ConeLimitCriterion`, `transportSpan`, coherent-cone/mapping patterns: no upstream
  declaration of this statement. Shared hits are the existing basic definitions,
  the canonical pinch module, and downstream coherent-colimit applications.
- Exact blueprint-id grep of the upstream `WeilConjectures` has no match.
- Focused grep for fiber/transport definitions found `rightFibrationFiberMap`
  (a map between abstract categorical pullbacks) and `joinSliceFiber` (ordered-join
  slices). Their full sources were read; neither defines the comma-transport span
  introduced here. The existing cocone gluing apex projection is a specialization
  of the generic Boolean comma projection; importing its downstream theorem would
  close a dependency cycle, so it is not used as a prerequisite.

The searches are recorded by the wrapper in the sandbox's `searches.jsonl`.
No new definition node, dependency-node restatement, or `statement_change` is needed.
No `STATEMENT-DISPUTED` remains: all reported faults in the previous Lean formulation
have concrete repairs above. All source lines are at most 100 characters, and all
universes and variables are explicit with `autoImplicit false`.

Validation: the prescribed `scompile.py NK lem-cbc-enhanced-functor-cone-calculus`
compiled the module at both sandbox and library paths without diagnostics; the
latest observed times were 2.1 and 2.6 seconds, with an imported dependency compiled
in its private overlay. The endpoint projection initially hit an elaboration
heartbeat limit; using Mathlib's genuine subcomplex lift repaired the definition
without increasing any resource limit. Only the main theorem remains postponed.
`python3 /home/ubuntu/weil-launcher-nt/deliver2.py NK
lem-cbc-enhanced-functor-cone-calculus --no-push` printed
`OK (dry run): commit a4a49b47c6 passes the preflight and compiles; nothing pushed`.
This report update is followed by a final dry run of the complete packet.

## Returned points repaired

- H3 endpoint failures: removed both unrelated basepoint-existence clauses. The
  universal predicates test the real `calculusTransportValue`, for every test apex.
- H3 arbitrary composition maps: replaced them with the canonical transport span
  and uniquely characterized left leg, diagram-fiber isomorphism, inclusion, and
  constant-path comparison. Naturality and compatibility are explicit propositions.
- H3 full subcategory: both full terminal/initial subcategories themselves are
  asserted Kan and weakly contractible under the stated nonemptiness guards.
- H8: every helper has a proper declaration docstring with source place and the
  item's blueprint tag; every helper appears in `lean.declarations`. Obsolete
  `coneEdge` and `coconeEdge` declarations have been removed.
- Report: the false earlier ordinary-nerve claim is withdrawn. The two review
  counterexamples and empty mapping spaces are checked explicitly above.

## Earlier second reading (a previous round; superseded)

The earlier second-reading claim about the returned file was invalidated by the
maintainer's review and is withdrawn. This repaired packet needs the dispatcher's
independent second reader before delivery. The repair worker's checks above do
not claim to be an independent reading. In particular the second reader should
inspect the canonical span, both-coordinate comparison equation, naturality,
diagram-fiber identification, both `0 → 1` examples, the empty fibers, and the
full-subcategory conclusions in the actual Lean definitions.

## Second reading by NK

I reread the node statement, its blueprint source place (this item has no Stacks source), the complete dependency
signatures, and the repaired module. The fixed universe convention is rendered by
`universe u`, `(K C : SSet.{u})`, and `[Quasicategory C]`; no filteredness,
inhabitedness, invertibility, Noetherian, or characteristic hypothesis is added.
The conclusion clauses render as follows: internal-hom quasicategory closure is
`Quasicategory ((ihom K).obj C)`; full-subcategory quasicategory and Kan mapping/core
claims are `QuasicategoryMappingSpaceAssertions`; vertexwise equivalence is
`ComponentwiseEquivalence`; functor-equivalence invariance is
`FunctorEquivalenceMappingSpaces`; coherent cone/cocone quasicategories and the
mapping formulas/limit and colimit criteria occur under `∀ F : K ⟶ C`; and the
terminal/initial full-subcategory Kan and contractibility clauses occur under
`∀ Q [Quasicategory Q]` with the stated existence guards.

The canonical transport formulation matches the node. In particular, the actual
right-pinched mapping space is connected to the asserted arrow-model homotopy fiber
by the existing natural `right_pinch_comparison`. For cones this is the comparison
for `Map_P(l,μ)`, while for cocones it is for `Map_P(μ,l)`. The transport formula
fixes its arrow-model comparison in both coordinates and states compatibility under
all compatible maps of spans. Thus composing the pinch comparison with this specified
comparison gives the node's natural equivalence; an additional existential comparison
from the right-pinched space would add no mathematical content. I briefly tried such
an explicit extra clause, detected its cocone orientation problem, and removed it
before the final checks. The delivered Lean is the repair worker's original statement.
No further mathematical mismatch remains, and no node statement correction, new node,
or dependency-module repair is needed.

Edge cases checked: empty `K` reduces to the ambient terminal/initial tests; empty
mapping fibers permit the unique empty-map weak equivalence and no basepoint choice;
zero-dimensional simplices and `n = 0` are covered by the explicit subcomplex
constructions; terminal/initial contractibility is asserted only under nonemptiness;
and the `0 → 1` cone and cocone examples have the correct transport orientation.
The dual uses `towards = false` and arrow spaces with the source/target reversed.

Searches were repeated with `msearch.py` LeanFinder, Loogle, and grep for
coherent cone mapping formulas and the exact helper names. They returned only primitive
quasicategory/internal-hom or ordinary-category declarations; no existing declaration
matches this node. The existing dependencies `EnhancedDiagramsCones`,
`RightPinchComparison`, and `ArrowTargetRightFibration` were read at their exact
signatures. No additional definition node or dependency repair is needed.

More explicitly, for each diagram and test apex I checked the following objects
against the dependency, without relying on their names: `calculusApex F true/false`
is the first projection from the degreewise comma subcomplex; `calculusFiber p x`
fixes the whole base simplex; `calculusTransport p towards x μ` fixes the entire
other endpoint at μ and the moving endpoint's entire apex at x. The left map `a`
is characterized by equality after `arrowMappingSpaceInclusion`, hence cannot be an
arbitrary weak equivalence. Its right map `r = calculusTransportValue ...` actually
forgets to the moving cone/cocone. `CalculusCommaFiberIdentification` is an isomorphism
fixing the diagram-arrow coordinate, so identifies this fiber with `U_D(Δx,F)` or
`U_D(F,Δx)`. The comparison `e` is fixed after `calculusFiberInclusion` by both
coordinates: the arrow-space inclusion `i` and the constant path at l. This is precisely
the strict-fiber inclusion into the path-model homotopy fiber, with the dependency's
path direction `r(t) → l`. Its naturality is the equality for all compatible `(a,c,d)`
span maps in `CalculusComparisonNaturality`. Finally the criteria test this same r
for every x, rather than unrelated maps or basepoints. Verdict: every clause matches.

I checked the ordinary nerve `N(0 → 1)` directly: for `F=1`, cone `μ=id₁` and x=0,
T and R are singleton and r is their isomorphism; for cone `μ=(0→1)` and x=1,
T is empty but R is singleton, so the criterion correctly fails. The dual fixed-source
tests have μ→l, not l→μ. With `F=0`, `μ=id₀` and x=1 they again give singleton
T and R. Empty ambient C, the empty predicate full subcategory, and empty K add no
inhabitance assumption. There are no ring/scheme/characteristic conditions in this
abstract simplicial statement. All simplicial sets share the dependency's fixed
universe u and all quantified variables are explicitly bound.

Source verification: I read Scholze Lecture II printed pp. 13–15 and the opening
compactification application. This is an agent-formulated foundation; no Stacks
`.tex` source is claimed. [Kerodon 01L5](https://kerodon.net/tag/01L5) supplies the
natural pinch-model comparison, [02HM](https://kerodon.net/tag/02HM) the full
terminal/initial subcategory assertion. [02R3](https://kerodon.net/tag/02R3) is only
the coslice special case, while [01TL](https://kerodon.net/tag/01TL) gives the
cartesian-morphism mapping-space criterion used in the foundation proof route.
None is misidentified here as a quotation of the entire general comma formula.

No definitions contain sorry, no private or file-local notion is introduced, and
the only postponed proof is the item's theorem. Its ten-step docstring records the
node proof, including higher-simplex compatibility and the dual construction. The
node's `lean.statement` is verbatim equal to the theorem signature in the module.
The independent reading adds this report; the delivered Lean statement is unchanged.
