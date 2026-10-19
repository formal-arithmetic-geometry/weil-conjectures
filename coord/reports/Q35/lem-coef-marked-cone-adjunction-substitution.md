## Worker report

The module `Sheaf.AlgebraicTopology.MarkedConeAdjunctionSubstitution` states
`SSet.MarkedConeAdjunction.marked_cone_adjunction_substitution` with proof `sorry`.
It asserts `Nonempty (Statement M)` for the marked point-model presentation `M`
already supplied by the marked-point dependency. `M` is only the existing
presentation of marked objects and their sharp enrichment; it adds no fibrancy,
local Kan, base-model or straightening-equivalence hypothesis. Every theorem in
this delivery has proof `sorry`; definitions contain real data.

The worker records reading Lurie, HTT, Definition 3.2.1.2, Remark 3.2.1.3,
Proposition 3.2.1.4 and Corollary 3.2.1.5, printed pp. 171--172, and the
adjunction identifications in the proof of Lemma 3.2.3.2 and before Lemma
3.2.3.3, printed pp. 188--189. The independent maintainer reader verified
these places directly in the IAS PDF during this review:
https://www.math.ias.edu/~lurie/papers/HTT.pdf (PDF pages 188--189 and
205--206, zero-based). The source agrees with the node; no statement
correction is needed. An archival copy under literature/ remains WANTED.

Clause-by-clause translation:

- Small `S`, small `I` and simplicial `u : C[S] → I^op` are the explicit
  `S : SSet.{u}`, `I : SCat.{u}` and coefficient-functor binders in
  `ConeFamily`, `Statement.right`, `adjunction`, `simplices` and `colimits`.
  All variables and the universe are explicit; `autoImplicit` is false.
- The functor `L_u` is `ConeFamily.left`. It equality-transports the exact
  `MarkedCone.Realization.functor` from the dependency, with a common
  `SimplicialDiagramEnrichment` for each index. This preserves its object,
  full enriched action and canonical arrow normalizations; it does not make
  a private copy of cone straightening. `ConeFamily.left_objects` exposes its
  value equality for the fiber formula. Its postponed proof substitutes the
  enrichment equality and uses `Realization.objects`.
- Small-colimit preservation is `Statement.colimits`, with size `{u,u}`.
  The marked right adjoint is `Statement.right`, with
  `Statement.adjunction : cones.left I φ ⊣ right S I φ`.
- The asserted n-simplices over a base simplex are exactly
  `SimplexDescription.equiv`: a dependent sum of the base map `σ` and an
  enriched marked transformation `L(flatOver σ) → F`. The category's arrows
  are the existing enriched-end arrows, not ordinary unenriched natural maps.
  `projection` fixes the map to `S`; `operator` fixes all face and degeneracy
  operators by precomposition with `restrictOver`; `map` fixes postcomposition
  on arrows of diagrams.
- Marked edges are precisely `SimplexDescription.marking`: existence of an
  extension from `L(flatOver σ)` to `L(sharpOver σ)` along `L.map (markOver σ)`.
  The extension equation is stated explicitly. `adjunct` fixes the adjunction
  on every simplex of every marked input, using the actual `simplexOver` map.
- `canonicalIndex S` and `canonicalComparison S` are the dependency's existing
  opposite coherent index and identity coefficient map. Their specialization
  of `left`, `right` and `adjunction` is `L_S ⊣ U_S`.
- `PointAdjunction.T`, `objects` and `maps` identify the terminal-index functor
  with the existing `Straightening.markedPoint` and `MarkedCone.pointMap`.
  `PointAdjunction.U` and `adjunction` are `U_0` and `T ⊣ U_0`.
- Composition of base maps is the existing `Marked.Over.push a`. The generic
  reattachment isomorphism is `Statement.base`; `base_generator` fixes its
  actual cone map to the identity. `Statement.canonicalBaseIso a` is the
  requested isomorphism `L_B a_! ≅ (C[a]^op)_! L_A`, constructed by composing
  `base`, the equality of its two attaching maps, and the inverse target
  comparison. `canonical_base_coefficients` records exactly that equality
  of double-opposite coefficient functors, without changing any objects.
- For `v : I → J`, `Statement.kan v` supplies the left Kan extension and
  restriction. `KanExtension.restriction_objects`, `restriction_actions` and
  `restriction_maps` specify actual precomposition on objects, all mapping
  simplices and all enriched transformations, respectively.
- The displayed marked coend is specified by `KanExtension.injection`, whose
  domain is exactly `J(v(i),j)^sharp × G(i)`, and `balanced` and `universal`.
  `IsBalanced` is the equality `[g v(f),z] = [g,G(f)z]` for every simplicial
  degree and every composable mapping simplex. `universal` says maps out are
  injectively determined by their restrictions to the injections, with image
  exactly the balanced families. Thus this is the actual coend universal
  property, not merely an unspecified adjoint or an arbitrary isomorphic
  object. `markings` says the marked edges are exactly the images of marked
  product edges; the sharp mapping factor has all edges marked. `action`
  specifies postcomposition on the mapping factor, and `maps` specifies
  functoriality in `G`. `adjunction` and `adjunct` fix the Kan adjunction by
  evaluation on the identity vertex in every degree.
- `TargetComparison.leftIso` is `v_! L_u ≅ L_(v^op u)`, so its inverse is the
  orientation displayed in the node. `generator` fixes its adjunct to the
  actual `UnmarkedStraightening.targetValueMap` of the cone pushout.
  `rightIso` is `U_(v^op u) ≅ U_u v^*`, with `mate` fixing it to that very
  adjunction mate. These isomorphisms are natural transformations of the
  input functors, so they include naturality on all input maps.
- Identity and composition coherence are specified by `base_identity`,
  `base_composition`, `kanIdentity`, `kan_identity`, `kanComposition`,
  `kan_composition`, `target_identity` and `target_composition`.
  The coend composition formula is `[h,[g,z]] ↦ [h w(g),z]`; the unit formula
  is the enriched action `[g,z] ↦ G(g)z`. The target comparisons are unique
  adjuncts of the specified pushout maps; their generator identity and
  composition equations therefore give exactly their coherence under these
  canonical Kan identifications. `mate` transfers the same laws to the right
  comparisons. The base comparisons fix every cone generator, so their
  canonical specialization and mixtures with target changes have the same
  identity/composition compatibility. No arbitrary comparison isomorphism
  is substituted for these maps.
- `FiberComparison.iso F s` is the marked isomorphism
  `(U_S F)_s ≅ U_0(F(s))`. The fiber is the existing marked pullback
  `Marked.Over.pullObject (const s) (U.obj F)`, and `vertex S s` is the
  existing coefficient vertex in the canonical opposite index.
  `naturality` explicitly gives naturality in `F` on marked maps.
- `FiberComparison.coneMap X s` is the first arrow `T(X_s) → L_S(X)(s)`.
  It is fixed on EVERY coend summand by `cone_generators`: the existing
  `qGenerator`, normalized `PointCalculation.coend`, and the existing
  `pinchedValueMap` followed by the actual `valueMap` induced by the fiber
  simplex inclusion. The pinched generators are normalized on the quotient,
  the cone inclusion, collapsed initial face and cone point by their
  dependency's fields. Thus the map uses the fiber inclusion and identity
  of `s`; it is not an arbitrary map with the desired source and target.
  `cone_naturality` specifies naturality in `X` on marked maps.
- `FiberComparison.adjunct` is exactly the last specified equality: the
  marked fiber of the adjoint of `h`, composed with the fiber isomorphism,
  is the `T ⊣ U_0` adjoint of `coneMap X s` followed by the component `h_s`.
  Components come from the actual enriched end projections.
- The last clause uses the existing `PinchedCube.initialFace n : Δ[n] → Δ[n+1]`.
  With `n` running over all naturals, this is the node's `Δ[N-1] → Δ[N]`
  for every `N ≥ 1`. `Statement.initialFace` gives the marked isomorphism
  with `G(i)` at all old vertices `i : Fin (n+1)`.
  `initial_face_unit` fixes that isomorphism by identity-insertion in the
  coend, so it is canonical and natural in `G`.
  `initial_face_empty` states that EVERY simplicial degree at the last
  vertex is empty. In marked simplicial sets this is exactly the empty
  marked object (there are no edges to mark), including its canonical
  uniqueness. There is no extra model or local Kan condition in any field.

Dependencies read and used:

- `Sheaf.CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.CoherentNerveComparisonStatement`, `SCat` and the coherent
  realization conventions, concretely the existing `PinchedCube.rigidification`.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked`, its actual maps/products/flat/sharp objects and
  `SSet.Marked.CartesianModelStatement` with its normalized sharp enrichment.
- `Sheaf.AlgebraicTopology.MarkedConeGeneratorCalculations`:
  `SSet.MarkedCone.Realization`, `ModelObjects`, `action`, `canonicalIndex`,
  `canonicalComparison`, `simplexMap`, `pointMap`, `PointCalculation`;
  and its imported existing `markedValue`, `Input`, `underlyingInput`.
- `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`:
  `SSet.Marked.Over`, `push`, `pull` and `pullObject`. Only the real slice,
  pullback and map definitions are used; no relative model is assumed.
- `Sheaf.AlgebraicTopology.UnmarkedStraighteningTargetChange`:
  `SSet.UnmarkedStraightening.targetOpposite` and `targetValueMap`, with the
  actual pushout leg and endpoint normalizations; its imported
  `UnmarkedStraighteningQuillen` supplies `coefficientVertex`, `qGenerator`,
  `qRealization`, `PinchedGenerators`, `pinchedValueMap`, `fiberSimplexArrow`
  and `valueMap`. These were read in full where used.
- `Sheaf.CategoryTheory.EnrichedCoend` is a proof import for the existing
  balanced coend definition. The module gives no second coend construction.
  Mathlib's `CategoryTheory.Adjunction` and `conjugateIsoEquiv` are used
  directly for the adjunctions and the unique right comparison mates.

Searches for an existing declaration:

- msearch LeanFinder, `Marked simplicial cone adjunction substitution enriched
  Kan extension vertex fibers`: eight hits on ordinary strict-Segal Kan
  extensions and realization, with no marked cone adjunction package.
- msearch LeanSearch, `marked simplicial set cone straightening adjunction
  enriched left Kan extension`: eight hits, including `Functor.lanAdjunction`,
  bicategorical Kan adjunctions and ordinary cone adjunctions; none is this
  marked enriched simplicial statement.
- msearch Loogle, `CategoryTheory.Adjunction, SSet.Marked`: zero hits; the
  Mathlib search index does not contain the project's `SSet.Marked`.
- msearch grep, `MarkedCone|marked.*[Aa]djunction|markedPoint`, Mathlib
  `AlgebraicTopology`: zero hits.
- `rg` of the slopmaster2 `WeilConjectures` tree for those names, and grep
  for this exact blueprint id: zero hits. The upstream name index likewise
  has no marked-cone-adjunction declaration.
- `rg` of project `lean/Sheaf` found the cone-generator and external-product
  interfaces above, and `MarkedConeStraighteningQuillen`. The latter has
  the normalized ordinary adjunction and some substitution interfaces as
  part of a Quillen package, but neither the full simplex/marking description,
  the vertex-fiber adjunct normalization nor the initial-face values here.
  It also uses another diagram presentation; it is not an exact match to
  this node. Its reusable opposite and pushout comparison are already the
  upstream definitions imported here via unmarked target change.
- Additional LeanFinder query, `Marked cone functor right adjoint naturality
  fibers and initial face extension by the empty simplicial set`, returned
  ordinary nerves/strict-Segal and ordinary adjunction results, no match.

Edge cases checked before and during writing: empty bases and inputs (no
simplex or marked-edge conditions become spurious); an empty coefficient
index (the coend has the initial object by its maps-out property); no
fibrancy or local Kan assumptions; all face and degeneracy operators,
including degenerate edges; all marked inputs, not just flat ones; vertices
with nontrivial enriched endomorphisms; initial face Δ⁰ → Δ¹; all old
vertices and the final vertex; and fixed arbitrary small universe `u`.
The coend universal property deliberately says injectivity plus image equal
to balanced families, not surjectivity onto arbitrary unbalanced families.

No new nodes, dependency repairs or statement changes were necessary.

## Second reading by Q35

Independent maintainer reading of immutable delivery
`d4a3e50f678af56a2310c53d53a095530f82966d`, supplied as a report-only
landing fix. The original heading contained an explicitly identified worker
self-check, not an independent reading. This section records the independent
reading actually performed; it does not attribute that reading to a second
worker of Q35.

I opened packet.md, the immutable item JSON, all three immutable statement
dependency JSON records, the entire delivered Lean module and report, the
review brief, stage-2 contract and delivery-errors H. I read the source places
above and the exact dependency interfaces in the read-only Q35 clone.
The detailed worker clause list above is correct, independently checked as
follows.

1. Objects and hypotheses: `SSet.{u}`, `SCat.{u}` and the enriched coefficient
   functor binders match the small simplicial inputs. `M` is the previously
   supplied `Marked.CartesianModelStatement`, whose normalized sharp mapping
   enrichment defines the diagram category; it is available from
   `marked_point_cartesian_model`. It adds no hypothesis about an input,
   local Kan mapping set, relative model structure or derived equivalence.
   The universe `u` is arbitrary, with small colimits at size `{u,u}`.
2. `ConeFamily.left` transports `Realization.functor` along its enrichment
   equality. The dependency's `objects`, `actions` and `arrows` normalize
   the actual marked cone values, full action and pushout-induced maps.
   The category `SimplicialDiagramEnrichment.Diagrams` represents enriched
   transformations through its end projections, rather than only ordinary
   natural transformations. No duplicate marked cone definition is used.
3. `Statement.right`, `adjunction`, `colimits` and `simplices` give the
   adjoint and colimit assertions. `SimplexDescription` fixes the base map,
   every ordinal operator, diagram maps and the actual adjunct simplex.
   Its marking iff is exactly extension across `L.map (markOver sigma)`.
4. `KanExtension` has the correct covariant variance: the injection domain
   is `J(v(i),j)^sharp × G(i)`. `IsBalanced` equates mapping-factor action
   with diagram action in every degree. The maps-out assertion is injectivity
   with image exactly balanced families, so it is the coend universal
   property. `markings` is exactly the image marking from the marked products.
   Its restriction, action, input-map and identity-insertion formulas are
   the specified enriched restriction and Kan adjunction.
5. `TargetComparison.generator` fixes the left comparison to the actual
   pushout `targetValueMap`; `mate` fixes the right comparison to its
   adjunction mate. `base_generator` fixes reattachment to the identity
   on values. `canonical_base_coefficients` has the correct double-opposite
   variance, and `canonicalBaseIso` composes these comparisons in the
   required orientation. Base identity/composition, coend identity/composition
   and the target generator laws imply the required canonical coherence;
   natural isomorphisms include naturality in input maps.
6. `PointAdjunction` has the dependency's actual `markedPoint` objects and
   `pointMap` arrows. The source's terminal-index cone is this functor.
   `FiberComparison.iso` is the marked fiber isomorphism, natural in diagrams.
   The pullback marking is exactly that induced from the input. Its
   `cone_generators` equation fixes `coneMap` on all quotient-cube summands
   using `PointCalculation.coend`, `pinchedValueMap` and the actual
   `fiberSimplexArrow` inclusion. Thus its `adjunct` equation states precisely
   the required fiber adjunct compatibility, not compatibility with an
   arbitrary map having the right endpoints.
7. The initial-face fields use `Delta[n] -> Delta[n+1]` for every natural n,
   which includes exactly every requested positive target dimension.
   `initialFace` covers all old vertices; `initial_face_unit` fixes its
   inverse to identity insertion, hence its canonical naturality.
   `initial_face_empty` asserts emptiness in every degree at the final
   vertex, which determines the empty marked simplicial set.

Edge cases checked: empty bases and inputs; empty coefficient indices and
coend summands; all face and degeneracy operators; degenerate marked edges;
vertices with nontrivial endomorphisms; the first initial face Delta[0] ->
Delta[1]; every old vertex and the final vertex; arbitrary small universe.
For the final vertex the mapping factor is C[Delta[n+1]](n+1,k), empty for
k < n+1, so the coend is empty. No fibrancy condition is needed.

Independent searches used `rg` with straightening/unstraightening and marked
Kan-extension terminology in Mathlib's AlgebraicTopology, slopmaster2's
WeilConjectures, and the Q35 clone's AlgebraicTopology/CategoryTheory modules.
I inspected `MarkedConeStraighteningQuillen` and `ConePresheafAdjunction`:
the former supplies a different Quillen-package presentation and neither
supplies this complete simplex, coend, fiber-normalization and initial-face
statement. The worker's recorded LeanSearch, LeanFinder and Loogle searches
are also present. The delivery reuses the existing marked objects, cone
values and enriched-end diagram category; its structures specify the new
assertion rather than construct a competing notion.

All 21 listed declarations were checked. All three theorem proofs are
`sorry`; definitions contain explicit data, equality transport or composition
of specified isomorphisms. Every declaration has source/blueprint docstrings,
and the main docstring carries all nine DAG proof steps. No line exceeds
100 characters; autoImplicit is false. The node's `lean.statement` equals
the final theorem signature verbatim. No statement_change, new node,
dependency repair or citer audit is necessary.

Reproducibility: the independent reader ran the prescribed `scompile.py Q35
lem-coef-marked-cone-adjunction-substitution` on the absolute immutable
snapshot module path. Exit status was 0. It reported the sandbox check in
4.7 seconds and the library check in 7.1 seconds, with no diagnostics.
The installed wrapper currently runs the overlay on the server and invokes
its library confirmation; this was the prescribed wrapper, not a direct SSH
command or a global build. The delivery's earlier recorded dry-run success
at `ba0f180ebc` is historical evidence; this review separately reproduced
compilation of the actual immutable module. No Lean file or node was changed.

Findings and fixes: H11/H1 report defect repaired by supplying this actual
independent reading. The worker report's garbled source numbers were restored
to the precise HTT references verified above. Mathematics, Lean and node
records require no correction.

## Returned delivery repair

The return for immutable head `c00c6d9f04ba` rejected the review fix-packet
filename `report.md` under `--apply-fixes`; it did not identify a Lean or
mathematical defect. This worker delivery uses the prescribed sandbox
`report.md`, which `deliver2.py` installs as
`coord/reports/Q35/lem-coef-marked-cone-adjunction-substitution.md`.
Any later reviewer fix packet must instead name its report
`lem-coef-marked-cone-adjunction-substitution.report.md`, as the returned
diagnostic requires. No raw `report.md` is delivered at repository root.

On this repair retry the retained packet was dry-run before any edit. The
wrapper rebuilt it against the current base and reported
`OK (dry run): commit ba0f180ebc passes the preflight and compiles`.
The staged paths were exactly the canonical report, this item's node and
`lean/Sheaf/AlgebraicTopology/MarkedConeAdjunctionSubstitution.lean`.
The saved node differs from the shared node only in `lean`; its statement,
dependencies and proof are retained. This report records the concrete
packaging repair instead of making an unchanged re-push.

For the required self-check I reopened the entire saved module and the node,
and reread the current dependency records and the normalized `Realization`,
`action`, `canonicalIndex`, `canonicalComparison`, `PointCalculation` and
marked-object interfaces. `SimplexDescription` includes projection, all
operators, marking and the actual adjunct; `KanExtension` includes balancing,
the maps-out universal property, exact markings, action and identity-insertion
adjunct; `FiberComparison` includes the actual fiber inclusion on every cube
generator and its adjunct equation. The initial-face clauses cover all old
vertices and degreewise emptiness at the new vertex, including the first
interval. All theorem proofs remain `sorry`, all definition data are explicit,
and `autoImplicit` is disabled. No new statement mismatch was found.
