## Worker report

Item: `lem-coef-infinity-mapping-excision`, stage 2, Q05.
Module: `Sheaf.CategoryTheory.InfinityMappingExcision`.
Main declaration: `SSet.Enhanced.infinity_mapping_excision`.
The only postponed theorem is this declaration, with the complete six-step node proof
in its docstring. Its proof is `sorry`. Both helper definitions contain real data.
The node copy changes only `lean`; the reviewed statement and split are retained.
No repair note for this item is present in `coord/repair-notes/`.

Hypotheses and every clause of the statement are rendered as follows:

- Simplicial sets small in one sufficiently large fixed universe are
  `{A B D K C : SSet.{u}}`, with `universe u` explicitly declared. This follows the
  fixed-universe convention of the recorded enhanced-diagram definition. A smaller
  simplicial set may be lifted to this universe; no object/morphism universe equality
  for an independent site is introduced.
- The arbitrary maps `j : A ⟶ B` and `i : A ⟶ D` are both bound. The sole injectivity
  hypothesis is `hi : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (i.app n)`.
  There is no monomorphism assumption on `j`.
- `K = B ⨿_A D` is stated invariantly by the legs `b : B ⟶ K`, `d : D ⟶ K` and
  `h : IsPushout j i b d`. This ranges over every pushout presentation and in
  particular the selected categorical pushout. The equality `h.w` identifies
  `j ≫ b` with `i ≫ d`; it is part of the pushout data, not an extra hypothesis.
- The target is a quasicategory by `[Quasicategory C]`. There is no assumption that
  `C`, or any functor quasicategory, has limits or colimits. Categorical pullbacks
  in the statement are formed in simplicial sets, where Mathlib supplies them.
- The two arbitrary coherent diagrams are `F G : K ⟶ C`. Their vertices are the
  recorded `diagramVertex F` and `diagramVertex G` in `(ihom K).obj C`.
  The source of `e F G` is exactly the recorded right-pinched `mappingSpace`
  between these vertices, not a Hom set or a homotopy-category quotient.
- The spaces over `B`, `D`, and `A` use the same `mappingSpace`, with vertices
  `diagramVertex (b ≫ F)`, `diagramVertex (d ≫ F)`, and
  `diagramVertex ((j ≫ b) ≫ F)`, and likewise for `G`.
- `excisionMappingRestriction a F G` is exactly the dependency's
  `mappingSpaceMap ((MonoidalClosed.pre a).app C) (diagramVertex F) (diagramVertex G)`.
  The restricted endpoint vertices are definitionally the vertices of the
  composite diagrams. This is actual restriction on all pinched simplices.
- `excisionMappingRestrictionOver a t s h F G` composes that actual restriction
  with `eqToHom` for the endpoint-space equality from `a ≫ t = s` and associativity.
  Thus its extra argument is only the already supplied indexing-square equality.
  In particular the `D` leg uses `h.w.symm` to land in the same `A` mapping space
  as the `B` leg. No new map or homotopy is chosen for this identification.
- Write `u` for `excisionMappingRestrictionOver j b (j ≫ b) rfl F G`, and `v`
  for `excisionMappingRestrictionOver i d (j ≫ b) h.w.symm F G`.
  The codomain of `e F G` is written directly with Mathlib's pullbacks as
  `pullback (pullback.snd u ev₀ ≫ ev₁) v`, where `ev₀` and `ev₁` are the
  recorded `evaluation Δ[1] _ (stdSimplex.obj₀Equiv.symm 0)` and its endpoint-1
  counterpart. Its simplices are precisely a `B` transformation, a path in the
  `A` mapping space starting at its restriction, and a `D` transformation whose
  restriction is that path's endpoint. This is the node's entire path model,
  with all higher simplices, not just points and path components.
- `KanComplex` is asserted for the source and the path-model codomain, so the
  asserted equivalence is an equivalence of spaces. The comparison's equivalence
  is `IsWeakHomotopyEquivalence (e F G)`, using exactly the recorded realization,
  path-component and based homotopy-group convention.
- The first projection equation is
  `e F G ≫ pullback.fst _ _ ≫ pullback.fst _ _ = excisionMappingRestriction b F G`.
  The second is `e F G ≫ pullback.snd _ _ = excisionMappingRestriction d F G`.
  The third projects to the path and equates it to restriction along `j ≫ b`
  followed by `constantDiagrams Δ[1]` of the `A` mapping space. Consequently the
  comparison is precisely the two restrictions and their constant compatibility
  path. The three projections jointly determine the map by the two pullback
  universal properties. The existential family `e` is not an arbitrary weak
  equivalence or an assumed map: these equations specify its entire simplicial data.
- Naturality in both diagrams and coherent compatibility with precomposition and
  postcomposition are retained by these projection formulas together with the
  final formulas quantified over every `T : SSet.{u}` and
  `H : T ⟶ (ihom K).obj C`. For each of `b`, `d`, and `j ≫ b`, they identify the
  uncurried restricted family with precomposition of the original family by
  `s ▷ T`. A triangle in this functor object is a coherent composite witness;
  arbitrary `T`, including every higher simplex, retains all higher witnesses.
  Since these are equalities of simplicial maps, substitution along every
  parameter map retains the same equalities. The path projection is the constant
  family, induced by projection off the interval, and hence has the same parameter
  compatibility. This expresses the node's final proof paragraph, rather than
  imposing strict composition operations on a quasicategory.

Dependency declarations read and used:

- Statement dependency `def-cbc-enhanced-diagrams-cones`:
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, especially
  `SSet.Enhanced.mappingSpace`, `mappingSpaceMap`, `diagramVertex`, `evaluation`,
  `constantDiagrams`, and `IsWeakHomotopyEquivalence`. Read their full definitions
  and docstrings and the entire dependency statement. Its `mappingSpace` imposes
  the entire initial-face condition, not merely its vertices.
- Mathlib primitives used through that module: `SSet`, `Quasicategory`, `ihom`,
  `MonoidalClosed.pre`, `MonoidalClosed.uncurry`, `KanComplex`, `Δ[1]`, and
  `stdSimplex.obj₀Equiv`. `IsPushout`, `pullback`, `pullback.fst`, and `pullback.snd`
  come from `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`
  and its imports.
- Stated proof dependency `lem-cbc-internal-hom-quasicategory` is the Mathlib match
  `SSet.instQuasicategoryObjIhom` in
  `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`.
  Read its signature and nearby restriction-fibration instance; its module is a
  non-public proof import.
- Stated proof dependency `lem-coef-infinity-pinch-comparison` is
  `SSet.Enhanced.right_pinch_comparison` in
  `Sheaf.CategoryTheory.RightPinchComparison`; its canonical prism, Kan clauses,
  inverse-homotopy clauses, and naturality formula were read. The module is a
  non-public proof import.
- The other proof-only nodes `lem-coef-infinity-isofibration-exponentiation`,
  `lem-coef-kan-pullback-path-comparison`, and
  `lem-coef-kan-homotopy-pullback-invariance` have no Lean attachment in the
  inspected base, so there is no module to import yet. They are retained verbatim
  in the proof plan and DAG; they do not obstruct writing the present statement.
  No statement of any of these other DAG nodes is introduced in this delivery.

Edge cases checked before writing:

- Empty `A`: the `A` functor category is terminal, so its mapping space is a point;
  the formula is the product comparison for a disjoint indexing union. No
  nonemptiness assumption excludes this case.
- Empty `K` (and therefore empty `A`, `B`, `D`): the unique empty diagrams remain
  covered even if `C` is empty. For nonempty `K` and empty `C`, quantification
  over `F G : K ⟶ C` is correctly empty.
- Identity attachments: if `i` or `j` is an identity, the statement becomes the
  expected path-space comparison for the corresponding trivial pushout.
- Noninjective `j`, such as collapsing the boundary of an interval, is admitted:
  no proof or instance for `Mono j` is requested. Only the `i` leg is injective.
- Degree zero of `mappingSpace` still records an entire edge with its endpoints;
  no restriction to components or to ordinary transformations is used.
- General `C` has neither chosen composites nor specified limits. Composition
  compatibility is represented by restricting simplex families, including their
  triangles and higher simplices, exactly as in node proof step 6.

Searches for an existing statement/notion:

- `msearch.py`, LeanFinder: "For a simplicial pushout along a monomorphism mapping
  spaces of coherent diagrams are homotopy pullbacks" returned 8 hits, including
  `SSet.instIsStableUnderCobaseChangeMonomorphisms`, `CategoryTheory.Adhesive.van_kampen`,
  and `CategoryTheory.Limits.Types.isPullback_of_isPushout`. These concern ordinary
  pushouts or pullbacks; none gives this mapping-space restriction comparison.
- `msearch.py`, Loogle: `"Quasicategory", "IsPushout"` returned zero hits.
- `msearch.py`, grep: `mappingSpace|homotopyPullback|mapping.*[Ee]xcision` in
  `AlgebraicTopology` returned zero hits.
- `msearch.py`, LeanSearch: "Restriction mapping spaces of coherent diagrams along
  a simplicial pushout homotopy pullback" returned 8 hits about ordinary restrictions,
  ordinary pushout preservation and pushout cocones, with no exact match.
- Source `rg` in `WeilConjectures/` for mapping-space/excision names, and the exact
  node id, found no declaration for this node. Existing sheaf-theoretic excision
  statements are unrelated.
- Project `rg` in `lean/Sheaf` found the recorded enhanced mapping spaces,
  `RightPinchComparison`, `KanMappingRestriction`, and the downstream
  `SourceAttachmentGluing` and `InfinityColimitGluing` modules. The latter two cite
  this result in their proof plans; neither states its general comparison theorem.
  `SourceAttachmentGluing.simplicialHomotopyPullback` is a general path-pullback
  helper in a downstream node's module. This delivery introduces no competing
  homotopy-pullback definition and avoids that downstream import: the theorem's
  target is expressed directly using Mathlib's iterated pullbacks.
- The new adapter and theorem names were checked against Mathlib, upstream and
  `lean/Sheaf`; there was no existing declaration with any of these names.

Source checked: the node's Kerodon references, including the online
[Remark the project server](https://kerodon.net/tag/01P9), describing Kan-fibration
mapping-space fibers as homotopy fibers. The complete reviewed node proof was
read and retained in the theorem docstring.

Validation: the final file was compiled through the prescribed `scompile.py`,
with both sandbox and module-path compilations clean and no warnings. Every
variable and universe is explicitly bound (`set_option autoImplicit false`).
No target, statement correction, new definition node, or dependency repair is needed.
The previous retry's stage-1 unchanged-node refusal is addressed by an actual
stage-2 `lean` attachment and the new module, without changing the reviewed split.

## Second reading by Q05

The node's objects and hypotheses were matched against
`SSet.Enhanced.infinity_mapping_excision` in order. `A B D K C : SSet.{u}`
are the five simplicial sets in the fixed universe; `j : A ⟶ B`, `i : A ⟶ D`,
`b : B ⟶ K`, `d : D ⟶ K`, and `h : IsPushout j i b d` render the two attaching
maps, the pushout presentation, and its commuting square. The sole hypothesis
`hi : ∀ n, Function.Injective (i.app n)` is exactly degreewise injectivity of
the (A\to D) leg; no injectivity or monomorphism of `j` was added. The target
assumption is exactly `[Quasicategory C]`, with no limits, colimits, finiteness,
or nonemptiness assumptions.

For each `F G : K ⟶ C`, the source mapping space is the recorded
`mappingSpace ((ihom K).obj C) (diagramVertex F) (diagramVertex G)`. The two
restricted spaces are rendered by `excisionMappingRestrictionOver j b ...`
and `excisionMappingRestrictionOver i d ...`; the latter uses `h.w.symm` to
identify both restrictions with the same `A` mapping space. The codomain is
the exact iterated pullback path model
`pullback (pullback.snd u ev₀ ≫ ev₁) v`, so its simplices retain the `B` datum,
the full path in the `A` mapping space, and the `D` datum. The three equations
for `e` are respectively the `B` projection, the `D` projection, and the
constant path at their common `A` restriction. `IsWeakHomotopyEquivalence`
uses the dependency's realization, components, and based homotopy-group
convention. The final quantified formulas for every `T : SSet.{u}` and
`H : T ⟶ (ihom K).obj C` give the stipulated coherent parameter naturality
of all three restrictions, including composition triangles and higher
parameter simplices. Together with the projection equations, they specify
the canonical comparison and its compatibility with pre- and postcomposition.

Edge cases were checked explicitly: empty `A`, empty `K` (and empty pieces),
empty target with no diagrams, identity attaching maps, noninjective `j`,
degree zero mapping simplices, and arbitrary higher simplices. No case is
excluded; in particular there is no hidden `Mono j`, nonempty index, or
characteristic assumption.

I read the dependency declaration `SSet.Enhanced.mappingSpace`/
`mappingSpaceMap`/`diagramVertex`/`evaluation`/`constantDiagrams` in
`Sheaf.CategoryTheory.EnhancedDiagramsCones`, and the full statement and
source of `SSet.Enhanced.right_pinch_comparison` in
`Sheaf.CategoryTheory.RightPinchComparison`. The Mathlib leaf
`SSet.instQuasicategoryObjIhom` and the recorded proof-only dependencies
`lem-coef-infinity-isofibration-exponentiation`,
`lem-coef-kan-pullback-path-comparison`, and
`lem-coef-kan-homotopy-pullback-invariance` were checked against their node
interfaces. The Kerodon source pages 01J4, 01P8, 01P9, and 01L5 were read;
01P9 confirms the Kan-fibration homotopy-fiber model used by the statement.

The three searches (LeanSearch, Loogle/LeanFinder, and focused `rg` searches
of Mathlib, `WeilConjectures/`, and `lean/Sheaf`) found no existing excision
statement or competing adapter definitions. The existing mapping-space and
right-pinch declarations are the single definitions used here. No mismatch,
missing hypothesis, extra hypothesis, wrong object, edge-case failure,
duplicate notion, hollow definition, or docstring defect was found, so no
source, node, or Lean repair was made. The prescribed `scompile.py` run was
clean for the module and its sandbox wrapper.
