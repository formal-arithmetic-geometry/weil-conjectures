## Worker report

This repairs H13 of returned immutable head `afa93b21ca5a`. The saved packet's
initial prescribed dry run passed at `f3546f43e7`, but the required self-check
confirmed that it still replaced the landed dependency's Lean record with a
helper definition. The requested ownership repair is now applied:

- The delivery contains no copy or change of the dependency node
  `lem-coef-infinity-join-cone-calculus`; its original module and theorem remain
  owned by that node.
- `CoherentWeightLimitRecognition.lean` publicly imports
  `Sheaf.CategoryTheory.InfinityJoinConeCalculus` directly.
- The standalone `JoinConeComparisonImage.lean` is removed from the packet.
  Its five declarations are moved unchanged into a section of the item's module
  opening `CategoryTheory.Limits` and `CategoryTheory.CartesianMonoidalCategory`.
  Each moved docstring now has this item's blueprint tag, and every moved name
  is listed in this item's `lean.declarations`.
- The accepted recognition statement, all helper signatures and bodies, and all
  other mathematical constructions are unchanged. No source statement correction
  or new definition node is needed.

The prior second reading concerned the returned two-module packet. It is not a
second reading of this repaired packet; the separate second reader must review
this repair before delivery.

The source statement is unchanged. I opened the authors' online PDF,
https://math.jhu.edu/~eriehl/recognizing.pdf, including Definitions 4.1.8 and 5.2.8,
Theorem 6.1.4 and its final proof on printed page 49. The definitions and statement
agree with the DAG's weighted cone and its transposed boundary diagram.

Clause-by-clause correspondence with the item's statement:

1. Simplicial sets, weak homotopy equivalences and limiting cones use the existing
   `SSet`, `SSet.Enhanced.IsWeakHomotopyEquivalence` and
   `SSet.Enhanced.IsLimiting`. `data.Y : SSet.{u}` is arbitrary, including empty Y.
2. The categories A and B are literally
   `SSet.PinchedCube.rigidification.obj data.Y` and the rigidification of
   `orderedJoinFunctor.obj (Δ[0], data.Y)`. There are no arbitrary model categories
   identified only later. `coherentBoundaryInclusion Y` is rigidification of
   `orderedJoinInr Δ[0] Y`. `coherentWeightApex Y` is the existing
   `SSet.Straightening.vertex` of the first-block vertex; it cannot be chosen freely.
3. `coherentJoinWeight Y` is `coherentHomDiagram` applied to that inclusion and
   that vertex. Its value is exactly B(b,inclusion(a)). Its action is
   `coherentHomAction`: curry of identity tensor the inclusion's enriched map,
   followed by enriched composition in B. This fixes the entire enriched action,
   not merely the objects of W.
4. `data.D : SCat.{u}` is a small simplicial category, `data.locallyKan` is
   `IsLocallyKan data.D`, `data.F : A ⟶ data.D` is enriched, and `data.L : data.D`.
   `coherentHomDiagram data.F Z` has values D(Z,F(a)) and the canonical
   postcomposition action `coherentHomAction data.F Z`. Thus its action also
   cannot be changed while preserving the object values.
5. `data.lambda` is a `GradedNatTrans` with grading the monoidal unit, source
   `coherentJoinWeight data.Y`, and target `coherentHomDiagram data.F data.L`.
   This is the enriched naturality equation on mapping simplicial sets in every
   degree. It is stronger than the saved file's `EnrichedNatTrans`, whose Mathlib
   definition only packages an ordinary natural transformation of the underlying
   categories. `coherentWeightLeg` uncurries its component using the right unitor
   to obtain the actual simplicial map lambda_a.
6. `enrichedNaturalMapSpace P Q` remains
   `SSet.stdSimplex.op ⋙ enrichedNatTransYoneda P Q`. Its n-simplices are exactly
   Mathlib's Δⁿ-graded transformations: after currying, enriched natural maps
   P × Δⁿ → Q. All faces and degeneracies are the existing presheaf operations.
7. The map in the every-Z hypothesis is the DEFINITION
   `coherentWeightedPostcomposition data.F data.L data.lambda Z`. It is no longer
   a field of the datum. On a simplex z : Δⁿ → D(Z,L), its component at a is the
   curry of `(lambda_a ⊗ z) ≫ symmetry ≫ eComp SSet Z L (F.obj a)`.
   `weightedPostcompositionComponent_naturality` supplies its enriched naturality;
   `weightedPostcompositionSimplex_naturality` supplies simplicial compatibility.
   Both are named postponed laws of this explicitly specified construction.
   The only recognition hypothesis is that THIS map is a weak homotopy
   equivalence for every Z : data.D, as in the node.
8. `data.collageMap` has source B and target D. `collage_restrict` requires its
   entire boundary functor to be F; `collage_vertex` requires its new vertex to
   be L; `collage_mixed` requires its map on every B(b,inclusion(a)) to be the
   simplicial map `coherentWeightLeg data.lambda a`. The HEq only handles the
   endpoint transports from the preceding equalities. It compares entire maps,
   not vertices or homotopy classes. The collage property of B makes these the
   canonical functor determined by lambda: these fields record the source's
   specified construction, with no additional mathematical restriction.
9. `coherentTranspose data.collageMap` is the actual join cone ℓ. On a simplex
   s it is `coherentSimplexUnit ≫ rigidification.map (yonedaEquiv.symm s) ≫
   data.collageMap`, a simplex of the recorded `nerveFunctor.obj data.D`, whose
   underlying construction is Mathlib's `SimplicialNerve`. Its naturality law is
   named and postponed. There is no independent `coneMap`.
10. The diagram in the conclusion is precisely
    `d = orderedJoinInr Δ[0] data.Y ≫ coherentTranspose data.collageMap`.
    By the collage restriction equation and naturality of the Kan unit it is the
    transpose of F. The cone in the conclusion is the DEFINITION
    `joinConeComparisonImage (coherentTranspose data.collageMap)` in
    `(coneCategory d) _⦋0⦌`. It is the comparison image of ℓ with its actual apex
    and entire boundary fixed. There is no independent cone vertex. Thus the
    conclusion is `IsLimiting d c` for exactly the cone required by the node.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.diagramVertex`, `evaluation`, `constantDiagrams`, `coneCategory`,
  `IsLimiting`, and `IsWeakHomotopyEquivalence`.
- `Sheaf.AlgebraicTopology.PinchedCubeLatching`:
  `SSet.PinchedCube.rigidification`, `coherentSimplexUnit`, and the existing
  subset-poset coherent simplices. The recorded latching theorem is retained.
- `Sheaf.CategoryTheory.CoherentNerveInfrastructure`:
  `CategoryTheory.CoherentNerve.SCat`, `hom`, `IsLocallyKan`, and `nerveFunctor`.
- `Sheaf.CategoryTheory.InfinityJoinConeCalculus`:
  `SSet.Enhanced.infinity_join_cone_calculus`, `IsJoinConeCylinder`,
  `joinConeArrowFamily`, and the existing join inclusions. The five named
  fixed-boundary comparison helpers now belong to this item's module and node;
  the dependency's original record is retained without modification.
- `Sheaf.AlgebraicTopology.RightStraighteningFiberComparison`:
  `SSet.Straightening.vertex`. Its already landed owner node is added to the
  item's stmt_deps under the authorization to cite landed nodes. I checked that
  this introduces no dependency cycle. This uses only its existing vertex
  construction; no straightening theorem is a hypothesis of recognition.
- Mathlib's `EnrichedFunctor`, `GradedNatTrans`, `enrichedNatTransYoneda`,
  enriched identity/composition and the closed/cartesian monoidal constructions.

All already stated proof-dependency modules are imported privately (cone
presheaf adjunction, relative terminal-boundary criterion, join slice right
fibration and cocone comparison, locally Kan coherent nerve, Kan model core and
both projective-model interfaces). The only unstated proof dependency on the
read base is `lem-coef-join-boundary-cubical-extension`, so it has no import yet.
It is not required to type the statement; its argument is retained in the main
theorem's complete proof docstring.

Edge cases checked:

- Y empty: the weighted natural-map space is terminal and the hypothesis says
  D(Z,L) is weakly contractible for every Z. The conclusion is the cone with
  apex L over the EMPTY boundary. It no longer permits a different apex X.
  In the returned counterexample D={X→L}, the old nonterminal cone
  `(X,X→L)` over const L cannot be substituted for the comparison image. This
  specifically resolves the reported false instance.
- Y a point: W is the unit weight; the hypothesis compares D(Z,L) to D(Z,F(a))
  by the specified leg, and the resulting ordinary cone is precisely that leg.
- Mapping spaces may be empty: no Nonempty or inhabited assumption is added.
  The every-Z condition itself determines when emptiness prevents recognition.
- n=0 and every degeneracy: the natural-map space and comparison are defined
  for every object of the simplex category, with no positive-dimension cutoff.
- All small simplicial sets/categories occupy the fixed sufficiently large u,
  as in the recorded SCat and rigidification interfaces. No equality between
  independent source universes or new cardinal bound is imposed.

Searches performed/read:

- `msearch.py leanfinder`: "simplicial enriched corepresentable functor hom
  postcomposition weighted homotopy limit coherent nerve" returned eight
  matches (ordinary nerve-adjunction maps and SimplicialNerve), no exact theorem
  or canonical comparison image.
- `msearch.py leansearch`: "enriched covariant Hom simplicial functor composition
  weighted natural transformations" returned sHomFunctor, eHomFunctor, ordinary
  functor-category enriched Hom, enriched composition and sHomComp. The first
  two are ORDINARY functors to SSet, not enriched functors with the required
  mapping-simplex action. None supplies the needed weighted recognition map.
- `msearch.py loogle`: "enrichedNatTransYoneda, EnrichedFunctor, eCoyoneda"
  returned no hits (unknown identifier enrichedNatTransYoneda in the service).
  Its actual source declaration was read directly in Mathlib.
- `msearch.py grep`, query
  `enrichedCoyoneda|enrichedCorepresented|coherent_weight_limit_recognition`
  in `CategoryTheory/Enriched`: zero matches.
- `rg` in Mathlib's enriched files, project `lean/Sheaf/CategoryTheory` and
  `AlgebraicTopology`, upstream `WeilConjectures` and `dag/lean_names_upstream.json`:
  no exact existing recognition theorem or named fixed-boundary comparison
  vertex. The existing `InfinityCategoryOfSpaces.enrichedCorepresented` instead
  uses Sing realization and takes values in Kan; it changes the Hom objects and
  is not the raw representable required here. `Enriched.Ordinary.eCoyoneda`
  only gives the ordinary functor. No second definition of those notions is made.
- I read the existing Mathlib `GradedNatTrans`, `EnrichedNatTrans`,
  `enrichedNatTransYoneda`, `EnrichedFunctor` and closed-category enrichment
  signatures to check enriched naturality and all tensor-factor orientations.
- `scompile.py --source Sheaf.CategoryTheory.InfinityJoinConeCalculus` confirmed
  the current published interface used by the dependency extension.

No statement correction and no STATEMENT-DISPUTED flag. All theorem proofs are
`sorry`, as required for stage 2; all definitions have explicit data. Named laws
needed by the constructions are documented under their owning node and listed
in lean.declarations. No second-reading verdict is asserted by this author.

## Ownership repair and self-check

No dependency module is delivered. The landed
`lem-coef-infinity-join-cone-calculus` record already states its full node through
`SSet.Enhanced.infinity_join_cone_calculus` and is usable as it stands.
Replacing that record with a helper definition was H13 even though the original
theorem was publicly imported. Removing the dependency-node copy ensures that
this delivery cannot displace its ownership or affect its existing citers.

The item's module now owns `SSet.Enhanced.joinConeCylinder`, `joinConeApex`,
`joinConeComparisonArrow`, `joinConeComparisonArrow_endpoints`, and
`joinConeComparisonImage`. Their signatures and bodies are identical to the
returned helper module; only their module location and blueprint tags change.
`joinConeCylinder K` selects the theorem's specified cylinder collapse.
`IsJoinConeCylinder` determines both pure ends and every mixed interval simplex,
which exhaust the simplices, so the witness is unique up to equality.
`joinConeComparisonArrow` evaluates the existing `joinConeArrowFamily` at the
join cone. The named endpoint law identifies both whole endpoint diagrams:
the constant diagram at its actual apex at zero, and the boundary diagram at one.
`joinConeComparisonImage` packages precisely that apex and arrow into the existing
`coneCategory` of the boundary diagram, retaining the required const-to-boundary
orientation. Its postponed endpoint theorem has a complete proof docstring under
this item's blueprint tag and is listed in the item's declaration inventory.

I reread the dependency's cylinder specification, arrow-family definition and
full theorem signature, plus the existing `coneCategory`, `IsLimiting`,
`diagramVertex`, `evaluation`, `constantDiagrams`, rigidification, Kan unit,
canonical vertex, enriched Hom and coherent-nerve definitions. The relocated
helpers continue to use those exact declarations. A fresh `rg` search across
Mathlib's enriched directory, upstream `WeilConjectures` and the side project's
`lean/Sheaf` found none of the five helper names or the recognition theorem,
so moving them does not create a duplicate declaration.

The edge cases in the clause-by-clause report remain valid: empty and point Y,
empty mapping spaces, n=0, all degeneracies, and the single sufficiently large
universe. The item's natural-language statement and `lean.statement` are
unchanged; its existing added landed vertex dependency is retained. Every theorem
proof remains `sorry` and no definition's data was changed.

## Verification

Initial saved-packet dry run: `f3546f43e7`, mechanically OK; H13 remained and was
repaired as above. After the repair, the prescribed `scompile.py NN
lem-coef-coherent-weight-limit-recognition` compiled the single merged module both
as a sandbox module (2.8 s) and under its library name (3.2 s), exit status 0,
with no errors or warnings. The final prescribed `deliver2.py NN
lem-coef-coherent-weight-limit-recognition --no-push` is the last mechanical gate;
its exact outcome is recorded in the worker's tool transcript. Nothing is pushed.

The self-check also confirms that the packet contains exactly one Lean module and
one node file, every moved helper is in `lean.declarations`, all blueprint tags
name this item, no Lean line exceeds 100 characters, and `lean.statement` remains
verbatim from the main theorem signature. Against the read-only base, the only
node fields differing are `lean` and the already authorized added landed vertex
owner in `stmt_deps`. The dependency-node override and standalone helper module
are absent.

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
