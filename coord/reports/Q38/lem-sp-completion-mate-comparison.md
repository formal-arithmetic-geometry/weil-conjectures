## Worker report

The delivery states `CategoryTheory.AdicSites.completionMateComparison` in
`Sheaf.Paper.CompletionMateComparison`. It imports the now-published prerequisite
`lem-sp-completed-pullback-adjunction` from
`Sheaf.Paper.CompletedPullbackAdjunction`. Its helper functors are in the same
comparison module. Nothing is delivered or pushed by this worker.
The mathematical statement of the item is unchanged; no dependency node is delivered.

The comparison uses actual constant module sheaves, actual strict quotient diagrams,
standard unbounded localizations, canonical derived functors and their normalized
adjunctions. In particular neither exchange, the completion unit, the coefficient
quotients, nor the projection comparison is a freely supplied arrow. Each auxiliary
choice is determined up to the equality used downstream by an explicit unique
universal property or a representative formula. All theorem proofs are postponed as
named theorems with proof docstrings. Definitions contain real data.

Hypothesis and clause correspondence for the item:

- A commutative Noetherian ring is `(A : Type u) [CommRing A]
  [IsNoetherianRing A]`; the ideal is `(I : Ideal A)`.
- `PerfectQuotients A I` requires the degree-zero complex of
  `A ⧸ I ^ (n + 1)` to satisfy the existing `DerivedCategory.IsPerfectRingComplex`
  for every `n : ℕ`. This is precisely the bounded finite-projective condition.
  Reindexing the positive integers by `n+1` retains every quotient, including A/I.
- The four `Site` arguments bundle small categories and their actual topologies.
  `Morphism V U` encodes the topos map from U to V by its set-sheaf adjunction and
  finite-limit-preserving inverse image. Its algebraic lift is the existing
  `ConstantCompletion.InverseImageData`, including all module-operation and constant
  ring compatibilities. This is a presentation of the canonical algebraic lift,
  not an additional geometric restriction.
- `Square f g h k` is the specified isomorphism
  `g.inverse ⋙ k.inverse ≅ f.inverse ⋙ h.inverse`. Thus h is g' and k is f'.
  `moduleSquare` is fixed by the given square on scalar insertions, and
  `derivedSquare` is its exact localization.
- `Site.ring`, `modules`, `derived`, `IsComplete`, `Complete`, `reduction`, `rlim`,
  `completion` and `unit` abbreviate the existing ConstantCompletion construction.
  In particular the complete condition is local derived sheaf Hom vanishing for
  every section of the kernel ideal of A→A/I, and completion is the derived strict
  quotient tower limit with its specified quotient-unit map.
- `modulePull` is algebraic inverse image followed by scalar extension through
  the canonical constant-ring identification. `modulePush` represents its module
  Hom functor; `pull` and `push` are its exact derived and K-injective total right
  derived functors. `adj` derives that same ordinary adjunction.
- `towerModulePull` and `towerModulePush` are actual termwise functors on
  `ℕᵒᵖ ⥤ Mod(A)`. `towerPull`, `towerPush` and `towerAdjunction` derive them
  before evaluating. `reduction` is the derived strict diagram represented by one
  flat-term K-flat complex and all its ordinary quotient tensors and transitions.
  `moduleReductionPullIso` is fixed at every quotient insertion;
  `reductionPullIso` is fixed by its whole-complex K-flat comparison equation.
- B and D are the source and target of `towerExchange sq A`, evaluated at
  `(X.reduction A I).obj K.obj`. `towerModuleSquare` is the termwise original
  module square; `towerExchange` is its derived `mateEquiv` image.
- H is `projectionComparison A I K.obj`: the inverse of the canonical horizontal
  reduction/pullback comparison, followed by horizontal pullback of
  `towerProjection`. `towerProjection` is explicitly the adjunction transpose of
  reduction of the ordinary counit after the canonical tensor/pullback comparison.
  The first conjunct proves `IsIso H` for every complete K.
- The second conjunct gives the finite evaluation of H. `finiteSourceIso` identifies
  evaluated B with restriction of `g* Rf_*` at quotient coefficients.
  `finiteProjectionComparison` uses `finiteProjection`, itself the ordinary finite
  coefficient adjunction transpose of the counit with the same tensor comparison.
  `finiteEvaluationIso`, `finitePullIso`, `finiteRestrictionPullIso` and
  `finiteRestrictionPushIso` are explicitly normalized on tensors or derived
  comparison maps; none is an arbitrary isomorphism.
- s is the natural transformation `comparisonS`, with component `rlim.map H`.
  Completion is definitionally reduction followed by rlim, so the preceding
  completion-identification arrow in the node is the identity here.
- t is `comparisonT`, whose component is `comparisonTComponent`.
  `directLimitIso` is the adjunction conjugate of the identity-component
  constant-tower/pullback comparison, using `deltaAdjunction` normalized by the
  ordinary constant/limit unit and the universal derived-limit comparison on every
  complex. Consequently this is the canonical direct-image/derived-limit map,
  and its K-injective computation has the direct images of the original tower
  projections. The further factor is rlim of direct image of the inverse strict
  reduction/pullback comparison, identifying the target with D.
- `completeSquare` is the adjunction conjugate of `completeRightSquare`, itself
  the restriction of `rightSquare`; the latter is the right-adjoint conjugate of
  the specified ordinary derived square. This fixes the completed composition
  normalization by the ordinary direct-image composition normalization.
  `completeExchange` applies `mateEquiv` to this completed square, independently
  of either tower limit map.
- The third conjunct is exactly the whole natural-transformation equality
  `completeExchange ≫ comparisonT.hom = comparisonS ≫ rlim(towerExchange)`;
  the complete-source inclusion and reduction are shown explicitly as whiskerings.
  It is not an evaluation-detection criterion.
- The fourth conjunct compares evaluation of v with `ordinaryExchange` at the
  quotient ring on finite scalar extension of K. Both source and target are
  identified with restriction of finite coefficient objects by the specified
  `finiteSourceIso` and `finiteTargetIso`.
- There are no properness, smoothness, constructibility, etale-origin, boundedness,
  or resolution-existence assumptions on the square or K. K ranges over the full
  `X.Complete A I` category. Resolution existence on these small module sites is
  supplied by named prerequisites, not required as a new hypothesis.

Dependencies used directly:

- `Sheaf.Paper.ConstantCompletionEquivalence`, namespace
  `CategoryTheory.ConstantCompletion`: `constant`, `quotient`, `Mod`, `D`, `TD`,
  `change`, `res`, `dres`, `extend`, `extendComparison`, `resFactors`,
  `reductionTower`, `reductionComplex`, `quotientPresentation`, `rlim`,
  `limitComparison`, `completion`, `completionUnit`, `IsComplete`,
  `InverseImageData`, `pull`, `constantMap`, `insertion`, `pullInsertion`,
  `ordinaryFinitePull`, and the Koszul/quotient reflector theorem. This already
  landed genuine node is added to the item's statement dependencies.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`,
  `DerivedCategory.IsPerfectRingComplex`; its already landed definition node is
  added to the item statement dependencies.
- Mathlib `constantSheaf`, `IsNoetherianRing`, `Functor.ofOpSequence`,
  `DerivedCategory`, `HasDerivedCategory.standard`, `CochainComplex.IsKInjective`,
  `mateEquiv`, `conjugateIsoEquiv`, and exact-functor localization interfaces.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`,
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction`; the actual chosen module
  adjunction is passed to this interface. Mathlib adjunction whiskering and
  additive-right-adjoint instances supply the tower and direct-image interfaces.
- `Sheaf.Algebra.Homology.KFlat`: `CochainComplex.IsKFlat`, the small same-universe
  compatibility form of the recorded independent-coefficient definition. Both
  express total tensor acyclicity against every acyclic complex; in the present
  single universe the construction and proposition agree by proof irrelevance.
- The recorded diagram-site, strict tower, tensor/pullback and exchange coherence
  modules are imported. The module of every recorded proof prerequisite is also
  imported, preserving the node's proof plan. In particular the canonical arbitrary
  ringed-site tensor interfaces are publicly reexported by the recorded
  `Sheaf.Paper.ProEtaleCanonicalTensorPullback`; no scheme-specific hypothesis is
  imposed on the present square.

Edge cases checked mathematically: I=0 gives the constant identity quotient tower
and identity completion; I=A gives the zero quotient tower and the zero complete
subcategory. Both are included. Zero rings, zero objects, identity edges, identity
squares, arbitrary unbounded complete K, non-subcanonical sites and the empty site
are allowed. Only perfectness of every positive quotient is assumed, without a
uniform projective-amplitude bound. The finite evaluation statements retain all
n, including n=0 corresponding to the first positive power. The theorem does not
attempt to detect equality of derived tower morphisms by evaluation.

Searches performed before construction (recorded in searches.jsonl): LeanFinder
query “The canonical derived adic completion Beck Chevalley mate equals the derived
inverse limit of strict quotient tower mates” returned ordinary AdicCompletion
results, no such comparison. Loogle query `CategoryTheory.mateEquiv` found the
abstract mate interface used here, not the geometric comparison. Mathlib grep
`completion.*mate|[Mm]ate.*[Ll]imit|derivedCompletion` found no matching theorem.
LeanSearch query “The canonical completed adjunction base change mate agrees with
derived limit of the strict quotient tower mate” was unavailable (Internal Server
Error), so no absence verdict is drawn from it. Direct rg searches of upstream
WeilConjectures and shared lean/Sheaf for completion/mate combinations and the exact
item identifier found no exact declaration. They found the reusable
ConstantCompletionEquivalence construction and specialized scheme/pro-etale
interfaces, which were read and reused as appropriate. Initial server source lookups for
`Sheaf.Paper.CompletedPullbackAdjunction`, `Sheaf.Paper.CompletedPullback` and
`Sheaf.Paper.PbcDerivedInverseLimitFunctor` were unavailable; the existing generic
completion module and current recorded comparison modules were available. Other
candidate group packets supplied scheme-specialized constructions rather than
this prerequisite on arbitrary small sites.

The source statements were checked against Stacks Tags 099M (completion and
reflector), 099N (complete pushforward and completed adjunction), 0941 (strict
inverse limit and K-injective computations) and 0E48 (tensor/exchange compatibility).
The node explicitly supplies the additional mate-identification calculation;
its ten-step proof is retained and expanded in the theorem docstring. No
STATEMENT-DISPUTED issue or source correction is asserted.

## Worker recheck

The resumed worker reread the item, every statement dependency record, the supplied
Lean declarations, the sandbox comparison and its helper definitions and the stage-2 contract. Fresh searches
on 2026-10-16 used LeanFinder “Completed adjunction base change mate equals inverse
limit of strict quotient tower mates” (eight abstract mate/composition hits, no exact
comparison), Loogle `CategoryTheory.mateEquiv, CategoryTheory.conjugateIsoEquiv`
(no hits), and Mathlib grep `completion.*mate|[Mm]ate.*[Ll]imit|derivedCompletion`
(two unrelated analysis/number-field hits). Direct rg across upstream
WeilConjectures and shared lean/Sheaf found no item declaration or AdicSites namespace.
The initial server lookup found no CompletedSiteAdjunction. During the worker
recheck, Q09 published the genuine completed-adjunction prerequisite under
CompletedPullbackAdjunction. Its full signature and docstring were read and the
comparison now imports that declaration.

The sources checked directly are [099M](https://stacks.math.columbia.edu/tag/099M),
[099N](https://stacks.math.columbia.edu/tag/099N),
[0941](https://stacks.math.columbia.edu/tag/0941), and
[0E48](https://stacks.math.columbia.edu/tag/0E48). The local literature files named
by the DAG are absent in this shared checkout; the original Stacks pages supply
the cited ingredient statements. None alone asserts the additional comparison;
the DAG's ten-step argument supplies it.

For the prerequisite, the site binders, Noetherian ring and ideal binders occur
in completion_properties and completeAdjunction_existsUnique. Site.IsComplete
is precisely the existing local internal-Hom condition, and Site.Complete is its
full subcategory. Site.completion and Site.unit are the specified strict quotient
limit and quotient augmentation. completion_properties states the reflector Hom
bijection, output completeness and unit characterization; reflectorAdjunction
fixes that same bijection. Morphism.push_complete gives preservation of complete
objects; completePull is inverse image followed by that reflector, and
completeAdjunction_existsUnique fixes its Hom bijection by ordinary transposition
after precomposition with the actual completion unit. This accounts for every
clause of the prerequisite without additional geometric or boundedness hypotheses.

The recheck removed redundant local instance bindings from the representative
normalization signatures. The same globally supplied standard localization and
additive tower instances are used throughout, avoiding expensive instance
reconciliation while retaining every representative equation.

The diagnostic also exposed a depth-limited typeclass search at the termwise
normalization map. The module now gives that composite's zero-map-preserving
instance directly from the existing reductionTower_additive theorem. It introduces
no assumption and changes no map. The definitions selecting unique comparisons
let Lean infer the isomorphism type already fixed by the normalized uniqueness
theorem, instead of rechecking an independently elaborated copy of that type.

The prerequisite landed during compilation. The delivery therefore contains only
the comparison module and its own node. `CategoryTheory.ConstantCompletion.
completedPullbackAdjunction` in `Sheaf.Paper.CompletedPullbackAdjunction` supplies
the recorded geometric module adjunction, derived direct image, completion
reflectors and complete adjunction. The helper API in this module expresses these
on the fixed algebraic lift and Mathlib derived functors used by the square.
The helpers reuse the original completion objects and quotient-unit maps; their
normalization properties follow by the canonical comparison of algebraic lifts
and the universal derived-functor comparisons. No prerequisite record is replaced.

The representative and unit normalization conditions are named public predicates.
The uniqueness statements and chosen comparisons reuse these predicates verbatim;
the representative equations and maps are unchanged. This removes repeated kernel
checking of large normalization formulas. The diagnostic single-file compile passed.

## Second reading by Q38

I independently read the sandbox node, its ten proof steps, the complete 1,247-line
comparison module, every statement dependency record, and the recorded declarations
used for the objects and comparisons. I did not write the worker's statement.
The node has no `statement_change`; its mathematical statement, proof and proof
edges agree with the shared base. The two additional statement dependencies are
already existing DAG nodes, not new definition nodes. No dependency module or new
node is included in this packet.

The local literature checkout has neither cited Stacks TeX file nor the cited
blueprint Markdown file. I therefore read the original Stacks pages and obtained
`proetale.tex` and `sites-cohomology.tex` from the Stacks source repository into
`scratchpad/source-second-reading/`. I read the context before the cited labels,
not just the lemma statements: proetale.tex lines 4280–4383, including
`lemma-naive-completion` (099M) and `lemma-pushforward-Noetherian-case` (099N);
sites-cohomology.tex around `lemma-derived-limit-is-ok` (0941) and
`remark-compatible-with-diagram` (0E48). The completion and preservation statements
assume a Noetherian coefficient ring and an ideal on arbitrary sites/topoi. The
strict-limit and tensor/exchange ingredients add no properness or smoothness.
The extra perfect-quotient hypothesis and the actual completed-mate calculation
belong to this DAG node; none of these ingredient tags alone asserts that whole
calculation. Sources checked: [099M](https://stacks.math.columbia.edu/tag/099M),
[099N](https://stacks.math.columbia.edu/tag/099N),
[0941](https://stacks.math.columbia.edu/tag/0941), and
[0E48](https://stacks.math.columbia.edu/tag/0E48).

Object, hypothesis and conclusion checklist (my step-1 list, followed by its Lean
rendering and verdict):

1. Commutative Noetherian A and an arbitrary ideal I: `A : Type u`, `[CommRing A]`,
   `[IsNoetherianRing A]`, `I : Ideal A`. The Noetherian definition is Mathlib's
   `IsNoetherian A A`, as recorded. PASS; no domain, field, characteristic,
   completeness of A, or nonzero hypothesis occurs.
2. Every positive quotient A/I^m is perfect over A: `PerfectQuotients A I` quantifies
   over every `n : ℕ` and applies `DerivedCategory.IsPerfectRingComplex` to the
   degree-zero complex of `A ⧸ I ^ (n+1)`. I opened
   `PerfectRingComplexGeneral.lean`: the predicate is exactly existence of a bounded
   complex with each term projective and finite and an isomorphism to its image
   in the derived category. PASS; no uniform bound, finite cardinality or quotient
   flatness is imposed. The standard localization instance matches the one used
   by that predicate.
3. Four arbitrary small sites: `{Y X Y' X' : Site.{u}}`, where `Site` records the
   category and its actual Grothendieck topology. `SmallCategory` is explicit.
   PASS; this is the size-convention presentation by small sites in a common
   bound. A site and ring already in smaller universes can be placed within this
   bound; there is no scheme, subcanonical-topology, or enough-points condition.
4. Four geometric edges: `f : Morphism Y X`, `g : Morphism Y Y'`,
   `h : Morphism X X'`, `k : Morphism Y' X'`; the order of `Morphism V U` is
   determined by its inverse-image functor from V-sheaves to U-sheaves. Thus
   h is g' and k is f'. `inverse`, `direct`, `adjunction` and `finiteLimits`
   state precisely a geometric morphism. PASS. Its `algebra` field is the recorded
   `ConstantCompletion.InverseImageData` algebraic lift, not an extra ring-map
   hypothesis: I opened its generalized-section and coefficient-naturality fields
   and `inverseImageData_exists`, which supplies it for every geometric adjunction.
5. Specified isomorphism of the square: `sq : Square f g h k` is
   `g.inverse ⋙ k.inverse ≅ f.inverse ⋙ h.inverse`. PASS, with the inverse-image
   order corresponding to the node's square. `moduleSquare` is fixed on scalar
   insertions and `derivedSquare` is its exact localization, so the square is
   not replaced by an unrelated derived isomorphism.
6. Constant module sheaves and unbounded derived categories: `Site.ring`,
   `Site.modules`, `Site.derived` reduce to `ConstantCompletion.constant`, `Mod`,
   `D`. I opened these declarations: constant sheafification, Mathlib's
   `SheafOfModules` through `ringedSiteModules`, and `DerivedCategory` at
   `HasDerivedCategory.standard`. PASS, not an adic or constructible replacement.
7. Ordinary exact inverse image and canonical derived adjunction: `modulePull`
   is the algebraic inverse image followed by scalar extension along `constantMap`;
   `modulePush` is its representing right adjoint. `pull` is exact localization,
   `push` the K-injective right-derived functor, and `adj` uses the upstream
   `mapDerivedCategoryRightDerivedAdjunction`. I read that upstream declaration's
   exactness, additive and K-injective binders. PASS; these facts are supplied,
   not required as new hypotheses on the square.
8. Completion, its unit and the full complete subcategory: `Site.completion`,
   `unit`, `IsComplete`, `Complete` reuse the actual ConstantCompletion objects.
   I opened the strict quotient presentation laws and local-completeness
   predicate. The ideal is the kernel of the constant A→A/I quotient, and the
   condition is the recorded local internal-Hom vanishing on all slices.
   `completion_properties`, the normalized reflector adjunction and normalized
   `completeAdjunction` give C after inverse image with the specified unit.
   PASS; the published `completedPullbackAdjunction` prerequisite was read and
   imported. The local helper API fixes the same functors through their universal
   comparisons rather than silently choosing a different completion.
9. Strict inverse sequences and their derived limit: `Site.towers` is
   `ℕᵒᵖ ⥤ T.modules A`; `towerDerived` derives this category, and `rlim` is the
   universal total right-derived strict limit from ConstantCompletion. PASS.
   I opened the diagram-site realization and ringed strict-limit theorem
   signatures. The indexing shift n↦n+1 is cofinal and retains all positive powers.
10. Strict reduction R_T: `Site.reduction` is the published quotient presentation's
    whole derived strict tower. I checked its `QuotientPresentationLaws`, ordinary
    quotient transitions and representative comparison. `reductionPullIso` is
    normalized on a single flat-term K-flat complex and the whole strict ordinary
    tensor comparison. PASS; no family of unrelated level morphisms is lifted.
    The K-flat definition used here is the recorded same-size total-tensor
    acyclicity predicate; the independent-coefficient form specializes to it.
11. G_u and R_u^T: `towerModulePull`, `towerModulePush`, `towerPull`, `towerPush`
    are the actual termwise functors and their derived functors, with the
    whiskered ordinary adjunction derived as `towerAdjunction`. PASS.
12. K, B, D and v: K ranges over all `X.Complete A I`. The source and target of
    `(towerExchange sq A).app ((X.reduction A I).obj K.obj)` are exactly
    `g.towerPull (f.towerPush (R_X K))` and
    `k.towerPush (h.towerPull (R_X K))`. `towerExchange` applies Mathlib `mateEquiv`
    to the exact localization of the termwise module square. PASS; the mate is
    constructed independently of the theorem's equality.
13. Specified projection arrow H: `projectionComparison` is inverse horizontal
    reduction/pullback comparison followed by horizontal pullback of
    `f.towerProjection`. The latter is the adjunction transpose of the reduction
    of the ordinary counit after the fixed tensor/pullback map. PASS; its direction
    agrees with R_(Y')(g*Rf_*K)→B. The first conjunct is exactly `IsIso H`.
14. Finite evaluation of H: the second conjunct uses `evaluate A n`,
    `finiteSourceIso` and `finiteEvaluationIso` to identify evaluation of H with
    restriction of `finiteProjectionComparison`. That comparison transposes the
    same counit after `finitePullIso`. PASS; every n is quantified, finite quotient
    coefficients are retained, and the first conjunct supplies invertibility.
15. Specified s: `comparisonS.app K` is exactly `(Y'.rlim A).map H`. The preceding
    identification C=rlim∘reduction is definitional. Its named naturality theorem
    supplies an actual natural transformation on complete objects. PASS.
16. Specified t: `comparisonTComponent` combines `directLimitIso` with rlim of
    direct image of inverse `reductionPullIso`; `comparisonT` packages these
    components as an isomorphism. `directLimitIso` is the adjunction conjugate
    of the identity-component constant-tower/pullback square. Its limit adjunction
    has the unit normalized by the ordinary const/limit unit and the universal
    right-derived comparison on every complex. PASS: this determines the ordinary
    direct-image/limit comparison on K-injective representatives and its tower
    projections, rather than supplying an arbitrary isomorphism.
17. Specified completed mate E^c: `completeRightSquare` restricts the conjugate
    `rightSquare` of the ordinary derived square; `completeSquare` conjugates it
    back through the composite normalized completed adjunctions; `completeExchange`
    applies `mateEquiv`. PASS. This fixes completed composition by the ordinary
    right-adjoint composition normalization and does not define E^c using s,t,v.
18. Main equality, natural in K: the third conjunct is
    `whiskerRight completeExchange inclusion ≫ comparisonT.hom =
    comparisonS ≫ whiskerRight (whiskerLeft (inclusion ⋙ reduction) towerExchange) rlim`.
    PASS: Lean's `≫` makes this exactly t∘E^c=rlim(v)∘s, an equality of entire
    natural transformations, with no evaluation-detection premise.
19. Finite coefficient normalization of v: the last conjunct compares evaluated
    towerExchange with restriction of `ordinaryExchange sq (quotientRing A I n)`
    on `finiteReduction K`, through the explicit `finiteSourceIso` and
    `finiteTargetIso`. PASS; these isomorphisms are independently built from
    normalized evaluation, pullback, restriction and direct-image comparisons.
20. No additional geometric hypotheses: the theorem binders impose none beyond
    the ring, ideal, perfect quotients, sites, geometric morphisms and specified
    square listed above. PASS; arbitrary unbounded complete K is covered.

Edge cases: the empty site and empty scheme presentations are permitted because
neither `Site` nor `Morphism` assumes a nonempty object type. Zero objects and zero
rings are allowed. I=0 makes all positive quotients A and gives identity completion;
I=A makes them zero and the complete subcategory contains just zero objects up to
isomorphism. Both satisfy the displayed perfect-quotient convention. n=0 means
A/I, not the unwanted A/I^0; no positive quotient is omitted. Identity edges and
identity squares remain valid. No characteristic or torsion constraint is imposed.
The sequence category is fixed nonempty ℕᵒᵖ, so an empty indexing family is not
part of this node. There is no hidden boundedness on K or common projective
amplitude bound for the quotients. All universes and site variables are explicitly
bound; I checked the single standard derived localization used across the aliases.

Independent H4 searches used different wording from the worker and the required
real search wrapper (results appended to searches.jsonl): LeanFinder
“Beck Chevalley transformation for reflective derived I complete modules computed
by derived inverse limit of quotient towers” returned eight local-cohomology and
ordinary adic-completion hits, no match; Loogle `CategoryTheory.conjugateIsoEquiv`
returned the abstract conjugation equivalence and its four formulas, which are
already reused; Mathlib grep `adic.*exchange|completion.*Beck|completed.*mate|reflect.*tower`
returned no hit. Direct rg with the same alternatives over upstream WeilConjectures
and shared lean/Sheaf found ordinary pro-etale `adicLowerStarComp_exchange` and
unrelated purity/support modules. I opened `adicLowerStarComp_exchange`: it is
composition coherence for ordinary adic sheaf direct images on schemes, not the
arbitrary-site derived completion/tower statement. Thus the delivery remains a
new theorem, and no existing declaration warrants dropping its module.

H5–H9 checks: every local chosen comparison has an existence-and-uniqueness theorem
with an explicit tensor-insertion, representative, or unit normalization. The
modulePush choice represents a fixed Hom functor. Universal derived constructions
are reused with their universal comparison maps. No object's data is a bare
postponed existence choice without such specification. There are 21 named
postponed theorems, each with a source/blueprint docstring and a natural-language
proof; every theorem proof is `sorry`. Proof fields in ordinary structures use
actual functoriality/instance arguments. The main docstring follows all ten DAG
steps, including the whole-diagram identity and the completed-unit transpose
calculation. No private notion, file-local instance or notation, new axiom,
unbound auto-implicit or line wider than 100 characters was found. The dependency
`ProEtaleCanonicalTensorPullback` publicly imports the arbitrary-site canonical
tensor comparison; I opened that import chain rather than treating its
scheme-specialized primary theorem as a theorem about these sites.

Mismatches and changes: no mathematical signature, canonical-map, hypothesis,
conclusion, or dependency mismatch was found, so I left the Lean and node as
written. I added this independent correspondence audit and fresh search evidence.
The extracted text from `theorem completionMateComparison` through its conclusion
is verbatim equal to the node's `lean.statement` (checked by string equality).
There is no statement correction and therefore no citer audit to attach.

Fresh verification: the prescribed scompile.py single-file invocation was run on
the delivered comparison module. The delivery wrapper then compiled both its
sandbox diagnostic and the named library module under its default 60-second
limit with no Lean errors or warnings (see
`scratchpad/second-reader-dryrun.log`). Its first preflight ran before this
second-reading section had been captured and rejected only the missing section;
no mathematical or compiler failure was reported. I rerun the prescribed dry run
with this complete report before delivery.
