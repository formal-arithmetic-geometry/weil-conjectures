## Worker report

The module `lean/Sheaf/CategoryTheory/MarkedSectionsPointwiseLimits.lean` states the
node's marked-section pointwise-limit theorem. The earlier sandbox attempt was
incorrect: its purported evaluation clause repeated the unevaluated cone predicate,
and its preservation predicate asserted only existence of some image limit. These
were defects of that Lean attempt, not of the DAG statement. The rewritten module
supplies the actual cone images, fiber evaluations and coherent transport families.
The original node statement is unchanged.

The declarations are:

* `sectionFiberInclusion` is the canonical second projection from the strict fiber `fiber p s`.
* `sectionTransportEdge` uncurries a vertex of the internal hom on `Δ[1]` to its edge.
* `CoherentSectionTransport p a τ` supplies one coherent simplicial family of lifts with both endpoint equations, the fixed base edge, and cocartesianness at vertices.
* `ConeImagesAgree f h c d` equates the actual apex and the complete internal-hom cone transformation after applying `f` and `h`.
* `HasJIndexedLimits C J` supplies an actual limiting cone for each coherent `J`-diagram. It includes `J = ∅`.
* `PreservesJIndexedLimits τ` sends every actual limiting cone to an actual limiting cone with the transported cone image specified by `ConeImagesAgree`.
* `MarkedSection p g W` requires each edge selected by `W` to map to a `p`-cocartesian edge; `markedSections` is the corresponding full subcomplex and `markedSectionsInclusion` is its canonical inclusion.
* `sectionEvaluationInTotal` is evaluation of a section at a vertex of `T`, followed by the pullback projection to `E`.
* `SectionFiberwiseLimiting` says that, for every vertex, the actual evaluated diagram has an actual fiber cone with the displayed equality and a limiting proof.
* `MarkedConeFiberwiseLimiting` says that an ambient marked cone is precisely one whose marked-subcategory image has the preceding fiberwise property.
* `PointwiseLimitConclusion` records ambient existence, the ambient fiberwise iff criterion, marked-apex closure, marked existence, the marked fiberwise iff criterion, and creation of marked limits by the full inclusion.

The theorem hypotheses render the node statement as follows. `E` and `S` are quasicategories in universe `max u v`; `T` is a small quasicategory and `J` a small simplicial set in universe `u`; `p : E ⟶ S` and `hp : cocartesianFibration p` give the cocartesian fibration; `g : ulift T ⟶ S` is the coherent base functor; and `W` is a predicate on all edges of `ulift T`. The hypothesis `hT` gives an actual `J`-indexed limiting cone in every fiber `fiber p (g.app _ t)`. The hypothesis `hW` ranges over every selected edge and every transport map equipped with `CoherentSectionTransport`, and requires `PreservesJIndexedLimits` for the lifted shape. The conclusion is `PointwiseLimitConclusion`, whose six clauses are: ambient section limits; ambient limits iff evaluated fiber limits; every ambient limiting cone on a marked diagram has marked apex; marked-section limits; marked limits iff marked cones are fiberwise limiting; and creation of the limits by the inclusion together with joint vertex detection. Unmarked arrows occur in no preservation hypothesis. The empty shape is included by the unrestricted `J` binder and the explicit `HasJIndexedLimits` definition.

Dependency declarations used:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.coneCategory`, `IsLimiting`, `fullSubcomplex`, `evaluation`, `diagramVertex`, and the coherent simplicial-set primitives.
* `Sheaf.CategoryTheory.InfinityFibrations`: `SSet.Enhanced.cocartesianFibration`, `IsCocartesianEdge`, and `fiber`.
* `Sheaf.CategoryTheory.EnhancedCartesianFibration`: `sectionSSet`, `sectionMap`.
* Proof imports are `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`, `Sheaf.CategoryTheory.EquivalenceOuterHornFilling`, `Sheaf.CategoryTheory.InfinityMappingComposition`, and `Sheaf.CategoryTheory.PointwiseCocartesianTransport`; their theorem proofs remain postponed by the DAG.

Edge cases checked: `J = ∅` gives terminal-object limits through the same actual-cone predicate; `W` empty makes `markedSections` the whole section object; `T` empty makes the vertexwise quantification vacuous while the section object is terminal; degenerate and repeated edges remain eligible because `W` is an unrestricted edge predicate; and a point base with the identity fibration reduces to the fiberwise theorem. No assumption is imposed on unmarked transports.

Searches made:

* `msearch.py ... leanfinder` with “Limits of marked coherent sections of a cocartesian fibration computed in fibers”: only ordinary-category/site limit declarations; no match.
* `msearch.py ... leansearch` with “Coherent cone postcomposition and marked sections pointwise infinity category limits”: only ordinary pointwise cone declarations; no match.
* `msearch.py ... loogle` with `CategoryTheory.CreatesLimits, SSet.Quasicategory`: no hits.
* `msearch.py ... grep` with `[Mm]arked.*[Ss]ection|[Cc]ocartesian`: only Mathlib ordinary fibered-category declarations; no match.
* `rg` over `WeilConjectures/`, `lean/Sheaf/`, and Mathlib for the theorem and helper names: no duplicate declaration.
* `grep -rn "lem-coef-marked-sections-pointwise-limits" WeilConjectures`: no source declaration.

No new DAG node or dependency repair was needed. The existing landed node
`def-cbc-enhanced-cartesian-fibration` is added to `stmt_deps` because the statement
uses its recorded `sectionSSet` and `sectionMap`; the original statement, proof and
proof dependencies remain unchanged. The auxiliary definitions belong to the
individual clauses of the owning theorem and are listed in `lean.declarations`. No `STATEMENT-DISPUTED` flag is raised.

Validation on 2026-10-17: the required `scompile.py Q29
lem-coef-marked-sections-pointwise-limits
lean/Sheaf/CategoryTheory/MarkedSectionsPointwiseLimits.lean` checked the sandbox
and library views cleanly (1.6 s and 1.7 s, respectively). All helper bodies are
explicit constructions or predicates; the sole postponed proof is the named main
theorem. Rechecked the declaration signatures and docstrings in all three
statement-dependency modules, including the pullback factor order and the
`δ 1` source / `δ 0` target convention. Repeated name searches in Mathlib,
`WeilConjectures/`, and the side library found no existing declarations of these
helpers or of the theorem.

The preservation hypothesis is invariant under the choice of coherent transport:
`hW` quantifies over every functor with a complete cocartesian lift family over the
specified edge. Such families exist for a cocartesian fibration; their existence
is not an additional assumption or data chosen from a postponed existence proof.
The equations in `CoherentSectionTransport` retain higher coherences. In
`ConeImagesAgree`, equality of the vertex in the twice-internal hom means equality
of the entire natural transformation, not equality of its components alone.

As a variance check, take a base with one nonidentity arrow and transport the
constant functor at the initial object of the two-object chain. It does not
preserve the terminal object. With that arrow unmarked, an ambient terminal
section still has terminal values in both fibers, and its structure arrow is the
unique arrow from the initial to the terminal object. Thus the unrestricted
ambient pointwise clause has the correct direction; marking that arrow makes
`hW` fail for the empty shape, exactly as required.

## Second reading by Q29

I read the node `lem-coef-marked-sections-pointwise-limits`, its source place (the
agent-formulated marked-section theorem underlying HA §3.2.2, especially
Proposition the project server and Corollaries the project server--the project server), the three statement
dependencies, and the complete Lean module. The node introduces the following
objects and hypotheses, matched to the file as follows.

* The fixed nested universes and quasicategories are rendered by
  `{E S : SSet.{max u v}}`, `{T J : SSet.{u}}`, and the instances
  `[Quasicategory E] [Quasicategory S] [Quasicategory T]`. The lift
  `SSet.uliftFunctor.{v}.obj T` (and the corresponding lift of `J`) is the
  explicit containing-universe presentation of the node's small `T` and `J`.
* The cocartesian fibration `p : E ⟶ S` and its hypothesis are exactly
  `(p : E ⟶ S) (hp : cocartesianFibration p)`, using the recorded definition
  `SSet.Enhanced.cocartesianFibration` from
  `Sheaf.CategoryTheory.InfinityFibrations`. The source and target conventions
  in that declaration make `S.δ 1` the source and `S.δ 0` the target.
* The coherent functor `g : T ⟶ S` and edge set `W` are rendered as
  `g : SSet.uliftFunctor.{v}.obj T ⟶ S` and
  `W : (SSet.uliftFunctor.{v}.obj T) _⦋1⦌ → Prop`. This is an unrestricted
  predicate on all edge simplices, so degenerate and repeated edges remain
  allowed.
* The fibrewise existence hypothesis is `hT`: for every vertex `t`,
  `HasJIndexedLimits (fiber p (g.app _ t)) (SSet.uliftFunctor.{v}.obj J)`.
  `HasJIndexedLimits` is the actual-cone predicate
  `∀ F, ∃ c, IsLimiting F c`, so it includes the empty shape and does not
  replace a limit by a mere nonempty choice.
* For a marked edge `e`, the node's transport hypothesis is rendered by `hW`:
  for every map `τ` from the source strict fibre to the target strict fibre,
  `CoherentSectionTransport p (g.app _ e) τ` supplies the complete coherent
  family of cocartesian lifts and endpoint/base equations, and
  `PreservesJIndexedLimits ... τ` requires the transported actual cone to be
  limiting. Quantifying over every such coherent lift is the choice-independent
  rendering of the node's `g(w)_!`; it imposes no preservation condition on an
  unmarked edge.

The auxiliary declarations render the node's notions without introducing a
second definition: `sectionFiberInclusion` and `sectionEvaluationInTotal` use
the factor order and maps of `fiber` and `sectionSSet`; `sectionTransportEdge`
and `CoherentSectionTransport` retain the whole internal-hom family;
`MarkedSection`, `markedSections`, and `markedSectionsInclusion` are the marked
predicate, full subcomplex, and canonical inclusion; `ConeImagesAgree` records
both apex equality and equality of the complete cone transformation; and
`SectionFiberwiseLimiting`/`MarkedConeFiberwiseLimiting` state the evaluated
fibre cone criteria. I checked the dependency declarations themselves: the
recorded `coneCategory`, `IsLimiting`, `fullSubcomplex`, `evaluation`, and
`diagramVertex` are used from `EnhancedDiagramsCones`; `fiber`,
`IsCocartesianEdge`, and `cocartesianFibration` are used from
`InfinityFibrations`; and `sectionSSet` and `sectionMap` are used from
`EnhancedCartesianFibration`. No private replacement occurs.

The six conclusion clauses are rendered by `PointwiseLimitConclusion` in order:
(1) `HasJIndexedLimits` for the ambient section object; (2) for every ambient
diagram and cone, `IsLimiting` iff `SectionFiberwiseLimiting`; (3) every ambient
limiting cone on a marked diagram has a `MarkedSection` apex; (4)
`HasJIndexedLimits` for `markedSections`; (5) a marked cone is limiting iff its
ambient image has a cone related by `ConeImagesAgree` and is fibrewise limiting;
and (6) every ambient limiting cone on a marked diagram lifts to a marked cone
with the same image relation and a limiting proof. The last clause is the
creation statement for the full inclusion, while (2) and (5) give joint vertex
detection. The theorem `marked_sections_pointwise_limits` has exactly the node's
objects, hypotheses, quantifier order, and conclusion, and its proof is the one
postponed `sorry` required at stage 2.

Edge cases checked independently: `J = ∅` is admitted by the unrestricted
`HasJIndexedLimits` binder and gives terminal objects; `W` empty makes the full
section object the marked subcomplex; `T` empty makes vertexwise detection
vacuous while the section object is terminal; degenerate/repeated edges are
included by the edge predicate; and no characteristic or zero-object
hypothesis is present because none belongs to this simplicial statement. The
`max u v`/`ulift` arrangement permits the node's independent small indexing
universe without forcing an equality of universes.

For the duplicate check I searched Mathlib, the read-only source checkout
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, and the repository's
`lean/Sheaf` with `rg` for marked-section, pointwise-limit, coherent-transport,
and all helper names; no declaration states this theorem or any of these
notions. The worker's independent `msearch.py` LeanFinder, LeanSearch, Loogle,
and grep searches likewise returned only ordinary-category limits/fibrations.
The node's three statement dependencies are the only recorded declarations
needed by the statement. The module has no line over 100 characters, no
unbound variables, and all declaration docstrings name the source and
`(blueprint: lem-coef-marked-sections-pointwise-limits)`.

No mismatch was found, so no Lean or node statement change was made. In
particular, the apparent extra `τ` quantifier in `hW` is precisely what avoids
choosing a noncanonical cocartesian transport: it ranges over maps carrying a
complete coherent lift family, and preservation of limits is invariant under
those choices. The node's `lean.statement` remains verbatim equal to the
theorem signature. `scompile.py` compiled the module cleanly on both the
sandbox and library views; only the intentionally postponed theorem proof is a
`sorry`.
