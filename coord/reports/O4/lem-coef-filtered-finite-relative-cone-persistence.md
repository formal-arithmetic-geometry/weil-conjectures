## Worker report

Module: `Sheaf.CategoryTheory.FilteredFiniteRelativeConePersistence`.
Main declaration: `SSet.CatInfinityCalculus.filtered_finite_relative_cone_persistence`.
One theorem has `sorry`; every definition and instance has real data. The natural
statement, dependencies and proof of the DAG node are unchanged.

The saved packet passed mechanical preflight after removing the trailing `:=`
from `lean.statement`, but its data record was mathematically incomplete: it
had no diagram or cocone, used the total category at every stage, and permitted
an arbitrary final comparison map. The self-check replaced that record with
the actual coherent slice diagram and its specified universal cocone.

Clause-by-clause correspondence:

- The marked Cartesian-model interface `M` fixes the existing coherent nerve
  `Marked.quasicategoryNerve M.qcat_enrichment`, which is Cat infinity in the
  recorded dependency. Its vertices are the bundled small quasicategories
  extracted by `relativeConeObject`. This selects the ambient model, not an
  additional mathematical restriction on the diagram or base.
- The small base `B` is `relativeConeObject M data.b`. There is no extra
  restriction on its size beyond the small universe `u`.
- `data.I : SSet.{u+1}`, `hI`, `smallI`, `filteredI` give the small filtered
  coherent indexing quasicategory, in the ambient universe containing Cat
  infinity. Smallness is `Presentability.IsSmall.{u,u+1}` and filteredness is
  `Presentability.IsKappaFiltered` at `aleph0`; no ordinary-category indexing
  restriction or independent smaller universe is used.
- `relativeConeSlice M b` specializes the existing coherent comma construction
  to the identity of Cat infinity and its vertex `b`. It keeps the entire
  structure arrow and all higher triangles. `D` is the actual map into this
  slice. `relativeConeProjection` forgets only the structural arrow.
- `cocone`, `sliceColimiting` give the specified colimiting slice cocone;
  `totalColimiting` tests the image of that very cocone under the projection,
  using `Spaces.mappedCocone`. Thus its underlying total cocone is colimiting.
- `pStage j` is the map from the actual object at stage `j` to `B`, and `p` is
  the map from the actual cocone apex to `B`. Their normalization fields are
  heterogeneous equalities to the functors of the actual structure edges of
  the comma vertices. HEq permits the endpoint equality transports; it does
  not allow an unrelated structural map.
- `i`, `K`, `finiteK`, `q` are respectively the specified stage, arbitrary finite
  simplicial shape, its finiteness, and the actual left-join cone at that stage.
  The node's beta is the derived composite `q ≫ pStage i`; its apex, boundary
  and legs are restrictions of this single simplicial map. They are not
  independent arbitrary fields.
- For every `j`, `a : (Enhanced.mappingSpace I i j) _⦋0⦌` is an arrow `i → j`.
  The mapping-space definition identifies its underlying simplex `a.1` with
  precisely that edge, including both endpoint conditions. The normalization
  of `transition j a` fixes it to the functor of the image edge under
  `D ≫ relativeConeProjection M b`. The entire slice diagram supplies its
  structural equivalence over `B` and all higher compatibilities.
- `stageLimit` applies `Enhanced.IsRelativeLimitDiagram (pStage j)` to the
  actual image cone `q ≫ transition j a`, for every such arrow. The node's
  displayed fibrewise universal property is the mapping-space formulation of
  exactly this relative limit property. Restriction gives the coherent map
  to the K-diagram of relative mapping spaces; its homotopy fibre over a base
  arrow is the displayed Map^h. A square of spaces is a homotopy pullback
  exactly when its maps on all such fibres are equivalences. The cone version
  retains the whole coherent K-diagram, hence its limit and all postcomposition
  legs, without selecting a strict composition operation on right-pinched
  mapping spaces. This uses the already recorded relative universal predicate;
  it does not introduce an arbitrary candidate limit or comparison map.
- The conclusion is that same relative-limit predicate for `data.p` and
  `q ≫ relativeConeCoconeLeg ... data.i`. The leg is the existing `coconeLeg`
  of the mapped total cocone, with its endpoint transports. Consequently its
  map on relative mapping spaces is the image cone's specified map, for every
  test object `z` and every base arrow `h`, as required.
- Empty K is allowed: neither `finiteK` nor the relative-limit predicate asks
  for a vertex of K. The corresponding mapping-diagram limit is terminal.
  No operad, existence of cocartesian lifts, fibration condition on a structural
  functor, or full faithfulness of transitions is assumed.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `Enhanced.comma`,
  `commaSubcomplex`, `mappingSpace`, `IsColimiting`, and the coherent
  cocone/diagram primitives; the fibre convention is `homotopyFiber`.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`: `Presentability.IsSmall`
  and `IsKappaFiltered`.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `Marked.CartesianModelStatement`, its `qcat_enrichment`, and
  `Marked.quasicategoryNerve`.
- `Sheaf.CategoryTheory.RelativeInfinityCone`: `Enhanced.leftJoinCone` and
  `Enhanced.IsRelativeLimitDiagram`, whose definition was read in full.
- Proof dependency `Sheaf.CategoryTheory.CatInfinityFilteredFiniteCalculus`:
  `nerveObject`, `nerveArrow`, `coconeLeg`, `coconeLeg_endpoints` and
  `coconeArrow`. The current server source was also checked via
  `scompile.py --source` to diagnose the explicit instance argument order.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`: `Spaces.mappedCocone`.
- Proof dependency `Sheaf.CategoryTheory.SpacesKappaLimitFilteredColimit`
  is imported for the fourth proof step.

The helpers specialize these existing notions to the fixed model. They do not
redefine general slices, nerves, relative limits, homotopy fibres or filteredness,
and require no new definition node or dependency repair.

Edge cases read against the exact statement: empty K; K a point; finite discrete
K; finite nondiscrete K with higher coherence; identity structural functor;
identity transition; arbitrary and identity base arrows. All are admitted.
For K empty the hypothesis and conclusion assert the corresponding relative
terminal-object property. No nonempty-shape shortcut is used. The chosen `i`
already supplies an indexing object, and filteredness also includes empty tests.

Searches retained from the previous packet (2026-10-17): LeanFinder for filtered
colimits preserving finite relative mapping-cone equivalences returned ordinary
Ind/set-valued filtered colimits and SSet finiteness; Loogle for finite-limit
preservation returned ordinary category results; Mathlib grep for
`relative.*limit|filtered.*limit|quasicategory` and quasicategory/relative mapping
patterns found no matching assertion. Searches of upstream WeilConjectures and
side Sheaf for `relativeMappingSpace`, filtered finite cone persistence, and
mapping-space cone declarations found no existing statement.

Resumption searches with `msearch.py` (2026-10-17): Loogle query
`SSet.Quasicategory, CategoryTheory.Limits.PreservesFiniteLimits` returned zero
hits; grep query `relative.*[Ll]imit|filtered.*[Cc]one` in `AlgebraicTopology`
returned zero hits. LeanFinder query: “A relative limit cone remains a relative
limit after a filtered colimit of infinity categories over a fixed base”.
The upstream and side-source rg checks for `relativeMappingSpace`,
`FilteredRelativeConeData`, `filtered_finite_relative_cone_persistence`, and
`relativeConeSlice`, and the upstream node-id search returned no match.
The dependency's existing relative-limit predicate is reused directly.

Source read again online: Gepner--Haugseng, arXiv:1312.3178v4, Section 3.3,
Proposition 3.3.2 and proof of Theorem 3.3.1. The finite coherent incidence-shape
case is the generalized mapping-condition argument, using filtered colimits
commuting with finite limits of spaces. The module docstring carries the node's
four proof steps, naming the filtered calculus and spaces exactness dependencies.

No statement correction or STATEMENT-DISPUTED is needed.

Validation: `scompile.py N4 lem-coef-filtered-finite-relative-cone-persistence
lean/Sheaf/CategoryTheory/FilteredFiniteRelativeConePersistence.lean` compiles
both sandbox and library forms cleanly (2.0 s and 2.3 s). No error or warning.

## Second reading by N4

Resumption self-check by the dispatched worker, not a claim of an independent
review; the maintainer performs the independent delivery review. I opened the
node, all four recorded dependency interfaces, the filtered-calculus helper
source, and the complete saved module. The old arbitrary comparisons and missing
diagram/cocone were found and repaired as detailed above. I then matched each
hypothesis and conclusion again: the base is small; I is coherently filtered;
D and both cocone universal properties are present; q lives at i; every image
transition is normalized; the relative universal property uses q itself; and the
conclusion uses the actual cocone leg. K empty and all base arrows remain
included. The record signature is extracted verbatim up to the proof separator,
and the declaration list includes every helper. The natural-language DAG node
and its dependencies remain unchanged. All delivered code is in the single
owning module; no other library source was modified.
