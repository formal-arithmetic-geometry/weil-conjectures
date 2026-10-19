## Worker report

Stage 2, N6, 2026-10-17. This packet states
`SSet.Enhanced.parametric_comma_fiber_comparison` in
`Sheaf.CategoryTheory.ParametricCommaFiberComparison`.
The sole theorem ends in `by sorry`. All other declarations are concrete constructions,
records specifying the comparison, or predicates spelling out its properties.
No definition has postponed data. The category-law proofs construct the indexing category;
no mathematical theorem has been proved in this statement delivery.

The preceding worker's stale-assignment diagnosis confused stages. The Q86 merge recorded
in the ledger and `reviewed` field was the stage-1 DAG split/review. On inspection the
assigned node had neither `lean` nor `reviewed_lean`, and no statement module existed.
The stage-2 assignment therefore remains valid. Nothing from the Q86 statement or proof
was resplit or rewritten.

### Hypotheses and clauses, individually matched

1. **One sufficiently large universe.** The file explicitly declares `universe u` and sets
   `autoImplicit false`. Every input quasicategory and every simplicial parameter is an
   arbitrary `SSet.{u}`. The collection of these data and the coherent space category live
   in `u+1`; `homSpaceCategory.{u, 0}` and the existing `uliftFunctor.{u+1,u}` handle that
   bookkeeping. This imposes no equality of previously independent universes or bound
   by a smaller, previously fixed universe.
2. **Arbitrary quasicategories C, B, D.** The theorem's first conjunct universally binds
   `(C B D : SSet.{u}) [Quasicategory C] [Quasicategory B] [Quasicategory D]`.
   There is no nonemptiness hypothesis.
3. **Arbitrary F and G.** Its binders `(F : C ⟶ D) (G : B ⟶ D)` are simplicial maps.
   There is no inner-fibration, fullness, universal-arrow or adjunction condition.
   `Datum` stores the same objects, maps, and their quasicategory proofs for the global
   naturality statement. Its extra-looking comma quasicategory proof is produced by the
   first conjunct, rather than assumed about F or G.
4. **The precise comma and projection p.** `ParametricComma.object F G` is
   `pullback (laxCommaTarget F) G`. The existing `laxComma F` is exactly
   `C ×_{F,D,ev₀} Fun(Δ[1],D)`, so this is the displayed two-sided comma.
   `target F G` is the outer `pullback.snd`; `source` and `arrow` are the actual first
   and transformation coordinates. No unrelated replacement category or map is used.
   The first theorem conjunct supplies its quasicategory structure.
5. **Every simplicial K.** `ExponentiationStatement F G` quantifies over all
   `K : SSet.{u}` without a Kan, quasicategory, inhabitedness, or finiteness condition.
6. **The canonical simplicial isomorphism of comma exponentials.** The family `P K`
   contains an actual `Iso` from `(ihom K).obj (object F G)` to
   `object ((ihom K).map F) ((ihom K).map G)`. Its source and target equations fix the
   endpoint coordinates, and its arrow equation fixes the entire transformation coordinate
   to `(ihom K).map (arrow F G) ≫ interchange K Δ[1] D`.
   `interchange` is explicitly double currying of the factor symmetry and evaluations.
   These three coordinates determine the isomorphism, so it cannot be an arbitrary iso.
7. **Both endpoint projections and every restriction K' → K.** The final clause of
   `ExponentiationStatement` binds every such map r and gives the corresponding comma
   restriction s. Its first equation is the isomorphism/restriction square; its next
   three equations specify the actual source, target and complete arrow restrictions.
   Restriction of the arrow is `(ihom Δ[1]).map ((MonoidalClosed.pre r).app D)`.
8. **The actual a=(A,B,alpha) and a'=(A',B',alpha').** A `Presentation` permits the
   actual functor comma itself, with the previous canonical iso, rather than moving the
   theorem to a different category. `Datum.a` and `.a'` are vertices of that E.
   Their A/B coordinates are exactly `presentation.source/target.app`.
   The typed right-pinched alpha vertices have underlying edges equal to the actual
   `presentation.arrow` vertices, converted by the existing internal-hom/Yoneda
   equivalences. `DataCoverageStatement` asserts existence of these alpha vertices for
   *every* presentation and pair a,a', so the typed representation excludes no objects.
   It also supplies the uniquely prescribed identity vertex.
9. **The specified beta:B' ≃ B.** `Datum.beta` is a vertex of precisely
   `mappingSpace B (p a') (p a)`, and `.beta_equivalence` is the dependency's
   `IsEquivalenceEdge B beta.1`. No inverse or universal property is supplied as extra data.
10. **Exactly gamma=(G beta) alpha'.** `gamma d` is the degree-zero value of the existing
    `canonicalHomComposition` on the pair `((mappingSpaceMap G).app beta, alpha')`.
    Its endpoints are `F A'` and `G B`. The same gamma, not an independently chosen arrow,
    is inserted in `phi`.
11. **The precise q.** `k d` is `mappingSpaceMap presentation.target a a'`; `t d` is
    postcomposition with the specified beta. `q d = k d ≫ t d`, with codomain
    `Y₀ d = mappingSpace B (p a) (p a)`.
12. **The precise phi.** `phi d` first applies `mappingSpaceMap F A A'` and then
    postcomposes with `gamma d` by the recorded canonical composition. Its domain is
    `X d = mappingSpace C A A'`; its codomain is `Z₀ d = mappingSpace D (F A) (G B)`.
    `f,g,s,t,v` separately expose the same cospan legs and endpoint adjustments as
    proof steps 2--3; none is an unconnected arbitrary map.
13. **The two homotopy fibers and their equivalence.** `Q d` is the dependency's actual
    `homotopyFiber (q d) d.identity`, with `identity.1 = B.σ 0 (p a)`.
    `R d` is `homotopyFiber (phi d) d.alpha`. `Comparison.map : Q d ⟶ R d` has
    `weakEquivalence : IsWeakHomotopyEquivalence map`, and both `sourceKan` and
    `targetKan`. The original definition of spaces identifies weak homotopy equivalences
    of these Kan models with equivalences of spaces; no truncation to components is made.
14. **The specified comparison, including all compatibility paths.**
    `IsCanonicalMappingComparison` fixes both projections of m to the actual h,k.
    Its bridge fixes the two composition triangles' free and long edges and the entire
    intervening path. Its final relative homotopy identifies this with the actual comma
    square's canonical `arrow_morphism_square` comparison, fixing both free edges.
    `Comparison.associate`, `.functorial` and `.unitPath` are the precise endpoint
    homotopies of proof steps 3--5. `.adjustment` uses the existing
    `PathModelComparisonFamily`, including both triangles of that endpoint adjustment.
    `.source_eq` retains the original C-arrow. `.firstTriangle` appends `v(rho)` to the
    adjusted path; `.lastTriangle` appends the unit path and fixes its long edge to the
    actual path coordinate of the output fiber. These are maps of whole simplicial sets,
    not merely relations on points or path components.
15. **Naturality in all data, with higher homotopies, and parameter restrictions.**
    `DatumHom` is an actual compatible map of the four quasicategories, commuting with
    F,G and the comma source, target and arrow maps and preserving the specified vertices
    and alpha/alpha'/beta edges. Its induced maps `onM,onX,onY₀,onZ₀` are fixed on
    *every underlying simplex* by those actual functors, including endpoint transport.
    These maps form the ordinary indexing category `datumCategory` by actual composition.
    `CoherentComparisonStatement` gives a **single simplicial map**
    `H : nerve Datum ⟶ (ihom Δ[1]).obj homSpaceCategory.{u,0}`.
    Thus this is a coherent natural transformation between two full space-valued systems.
    `RepresentsEdge (componentEdge H d) (W d).map` fixes every component to the actual
    path-pasting comparison. For *every* DatumHom, the two endpoint edges are fixed to
    the actual induced fiber maps. `FiberMap.induced` uses the existing
    `IsInducedFiberMap`, so its domain coordinate and complete triangle path are specified.
    Higher simplices of the same H give the composition, identity, and all further
    naturality homotopies. This is stronger bookkeeping than asserting unrelated
    existence of objectwise equivalences or only commuting diagrams on pi_0.
    Taking the four functors to be precomposition by r on the functor quasicategories
    gives every parameter restriction, with the presentation supplied in clause 7;
    their composites and all higher compatibilities belong to the same H.
    Families of object/arrow data are included by using their functor quasicategories
    and restrictions along simplex maps.
16. **No universal-arrow, adjunction, fullness, or fibration assumptions.** None occurs
    in the main theorem, `Datum`, or the comparison. The `Presentation` and
    quasicategory assertions are the explicitly constructed comma interface and its
    resulting structure. The typed alpha/identity witnesses are supplied by coverage.

### Dependency declarations used

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.evaluation`,
  `mappingSpace`, `mappingSpaceMap`, `IsEquivalenceEdge`, `homotopyFiber`,
  `commaSubcomplex`, `IsWeakHomotopyEquivalence`. Read the complete source declarations.
- `Sheaf.CategoryTheory.InfinityMappingComposition`: `MappingCompositionStatement`,
  `mapping_composition`; its uniquely specified composition *class* is reused through
  `canonicalHomComposition`, so no new strict composition is postulated.
- `Sheaf.CategoryTheory.InfinityHomBifunctorFunctoriality`:
  `canonicalHomComposition`, `homSpaceCategory`, `homSpaceEdgeSource`,
  `homSpaceEdgeTarget`, `homSpaceEdgeTransport`. The space category uses its existing
  coherent nerve; the larger-universe lift is the recorded canonical one.
- `Sheaf.CategoryTheory.InfinityLaxCommaTargetFibration`:
  `laxComma`, `laxCommaSource`, `laxCommaArrow`, `laxCommaTarget`. Only these concrete
  constructions are used; this packet does not apply that module's theorem or inherit
  its separate hypotheses on F.
- `Sheaf.CategoryTheory.ArrowMorphismSquare`: `arrowSquareFamily`,
  `arrowSquarePathFamily`, `arrowSquarePathEndpoints`, `arrow_morphism_square`.
  The chosen comparison is fixed by that theorem's ambient inclusion formula.
- `Sheaf.CategoryTheory.KanHomotopyCommutingPullbackInvariance`:
  `PathModelComparisonFamily`, with its two triangle families and factor equations.
- `Sheaf.CategoryTheory.SourceAttachmentGluing`: `simplicialHomotopyPullback`,
  `sourceAttachmentPullbackFst`, `sourceAttachmentPullbackSnd`, `sourceAttachmentPinch`.
  These existing canonical path-model helpers are reused rather than redefined.
- `Sheaf.CategoryTheory.SpacesHomotopyFiberDetection`: `homotopyFiberProjection`,
  `homotopyFiberPath`, `IsInducedFiberMap`. A late duplicate search found these exact
  helpers, so the draft copies were deleted and the published interfaces imported.
- The stated proof dependencies `EnhancedFunctorConeCalculus` and
  `InfinityHomotopyPullbackPasting` are non-public proof imports. The original proof
  dependency `lem-coef-infinity-comma-mapping-pullback` has no Lean record yet and is
  not imported; its statement is not needed to *state* this node. Its canonical-square
  comparison appears as construction witnesses in this node's conclusion, and the
  natural-language proof explicitly calls the DAG dependency in step 2.
- Mathlib's actual `SSet`, `Quasicategory`, `KanComplex`, internal homs, symmetry,
  evaluation, curry, nerve, `SSet.Homotopy`, categorical pullback, and `uliftFunctor`.

Six already-landed nodes providing the reused statement interfaces were added to
`stmt_deps`, as allowed by brief-stage2 §5, STMT_DEPS MAY GAIN LANDED NODES:
`lem-coef-infinity-hom-bifunctor-functoriality`,
`lem-coef-infinity-lax-comma-target-fibration`,
`lem-coef-infinity-arrow-morphism-square`,
`lem-coef-kan-homotopy-commuting-pullback-invariance`,
`lem-coef-infinity-source-gluing`, and
`lem-coef-spaces-homotopy-fiber-detection`.
Each has a published Lean record. A read-only DFS of both statement and proof dependencies
found no path from any of these nodes back to this item. No dependency record, statement,
proof, proof dependency, status, review, or source was changed. No new DAG node or dependency
module is needed: all additional constructions are the comma E, its canonical map/formula,
or the coherence interface of this very theorem, and are listed in `lean.declarations`.

### Edge cases checked before finalizing

- Empty K: its internal functor objects are terminal even if the original comma is empty;
  K has no additional hypotheses, and the statement still includes its unique data.
- Empty C or B: the original comma may be empty, so its vertex clauses are vacuous;
  exponentiation, including empty K, remains asserted.
- Empty, disconnected, or noncontractible mapping spaces: all are full simplicial sets;
  no identity is requested in a cross space lacking endpoints, and no nonemptiness is
  assumed. A source or target fiber may be empty.
- Beta the identity: q is the actual target map up to the recorded unit homotopy;
  the construction retains the unit path instead of silently identifying nonstrict maps.
- Arbitrary specified equivalence beta: its value is retained in t, s, gamma and the
  input identity fiber. No arbitrary inverse is substituted in these constructions.
- Alpha/alpha' need not be equivalences or universal arrows. Constant F or G and F
  which is not fully faithful are covered. No fibration assumption was introduced.
- Simplicial restrictions include identities, compositions, vertex evaluations,
  degeneracies and boundary/face maps. The nerve-valued coherence system records all
  iterated restrictions, not only their separate objectwise assertions.
- The auxiliary typed data are not a hollow hypothesis: coverage and exponentiation
  supply them for every original pair of objects, and the comparison is asserted for
  every datum in the resulting category.

### Searches for existing statements and interfaces

All searches below were actually run through the prescribed tools or read-only source rg.

- `msearch.py ... leanfinder`:
  "The homotopy fiber of mapping spaces in a comma quasicategory over a specified target
  equivalence is the fiber of postcomposition". Eight hits on ordinary Grothendieck/comma
  fibers and model-category fibrations. No quasicategorical, parameter-natural comparison.
- `msearch.py ... loogle`: "Comma, homotopyFiber". Zero hits; service reported the
  unknown identifier `Comma`. This is not evidence of absence by itself; the other searches
  and the actual source reads provide the required check.
- `msearch.py ... grep`: "comma|fiber|homotopy", subdirectory `CategoryTheory/Comma`.
  Twenty-five ordinary category hits. Read Mathlib `CategoryTheory/Comma/Basic.lean`
  signatures: objects and strictly commuting squares in ordinary categories, without the
  stipulated full homotopy fibers or arbitrary simplicial parameters.
- `msearch.py ... leansearch`:
  "The homotopy fiber of the comma target map on mapping spaces after a specified target
  equivalence is the fiber of source postcomposition". Eight hits on ordinary
  `Comma.post`, Grothendieck comma fibers, and model-category postcomposition. No match.
- `rg` in the complete upstream `WeilConjectures` and current `lean/Sheaf` for
  "parametric.*comma|comma.*fiber|ParametricComma|parametricComma", plus the prescribed
  upstream grep for the item id. No existing declaration states this lemma. Hits on
  `ParametricUniversalArrows` impose universal-arrow hypotheses and state a different
  result; `EnhancedFunctorConeCalculus` specializes to cones, not arbitrary F and G.
- Read the existing `ParametricUniversalArrows`, `InfinityLaxCommaTargetFibration`,
  `ArrowMorphismSquare`, `InfinityMappingComposition`,
  `InfinityHomBifunctorFunctoriality`, `KanHomotopyCommutingPullbackInvariance`,
  `InfinityHomotopyPullbackPasting`, and enhanced-diagram sources to reuse their precise
  models. No imported declaration is a match for the whole assigned node.
- `rg` for every new namespace/main name and `IsCanonicalMappingComparison` in upstream,
  current `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.
- Additional source `rg` for homotopy-fiber projections/paths found the exact published
  `homotopyFiberProjection`, `homotopyFiberPath`, and `IsInducedFiberMap`; reused them.

### Validation

All compiles use the required `scompile.py N6 lem-coef-parametric-comma-fiber-comparison`
wrapper, compiling this module individually against the published library. The complete
statement and concrete category constructors compiled in about ten seconds per pass;
the final import-reuse pass exposed two overlong lines, both repaired before final checks.
The final compile and `deliver2.py --no-push` results are recorded below after completion.

No STATEMENT-DISPUTED claim. No statement correction, new node, or dependency repair.
The source is the current main-20261015 blueprint proof paragraph named by the DAG;
the assigned lemma is explicitly agent-formulated, not attributed to a nonexistent
Stacks statement. Its six-step proof is carried into the theorem docstring.

Final verification: the complete module compiled cleanly through `scompile.py`, both in
the sandbox and at its library module path (10.3 s and 10.2 s), with no warnings.
The prescribed `deliver2.py N6 lem-coef-parametric-comma-fiber-comparison --no-push`
reported `OK (dry run)` at commit `6ce116f264`: maintainer preflight and per-file compile
both passed. The delivery wrapper supplies the authorized no-second-worker-reading note;
no independent reading is claimed in this worker report.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
