## Worker report

The module `Sheaf.AlgebraicTopology.KanRealizationMappingClasses` states
`SSet.Enhanced.kan_realization_mapping_classes`, with its only proof `sorry`.
It gives the realization bijection as a family of equivalences, fixes its value
on every actual simplicial map, and states the two naturality squares on all
components. There are no new definitions, dependency repairs, or statement
corrections. The node copy changes only `lean`.

Hypothesis and clause correspondence:

- The fixed universe is the explicit `universe u`; all of `K`, `K'`, `W`, and
  `W'` are `SSet.{u}`. The supplied dependency uses precisely these Mathlib
  simplicial sets, internal homs, Kan complexes, and realizations.
- An arbitrary simplicial set `K` is quantified in the family `e`. There is no
  `KanComplex K` hypothesis.
- A Kan target is the explicitly bound instance `[KanComplex W]`. The
  postcomposition square also quantifies `[KanComplex W']`, exactly because it
  concerns maps between Kan targets.
- The source class set is `π₀ ((ihom K).obj W)`. In Mathlib's
  `SimplicialSet/PiZero.lean`, `π₀ X` is `Quot π₀Rel`, where the relation means
  an edge with the specified endpoints. `π₀.mk_eq_mk_iff` identifies equality
  with its equivalence closure, exactly the edge-generated convention in the
  node. It is not the path-component type of the realized mapping object.
- The target class set is the literal
  `Quot (@ContinuousMap.Homotopic |K| |W| _ _)`. Mathlib defines `Homotopic`
  as existence of a continuous homotopy; its `refl`, `symm`, `trans`, and
  `equivalence` declarations show this is already an equivalence relation, so
  `Quot` does not identify additional pairs. `ContinuousMap.Homotopy` extends
  `C(unitInterval × X, Y)` with its endpoint equations. Its product topology
  is ordinary. Swapping the two factors gives exactly the node's
  `X × [0,1]`; no endpoint or basepoint is fixed in `X` or `Y`.
- Bijectivity is expressed by `≃`. The family `e` is existentially quantified,
  and the first conjunct requires
  `e K W (π₀.mk (diagramVertex a)) = Quot.mk _ (toTop.map a).hom` for every
  actual simplicial map `a`. This fixes the comparison to `[a] ↦ [|a|]`.
  Every internal-hom vertex represents such a map, and `π₀.mk` is surjective;
  hence this is a characterization of the specified canonical bijection,
  rather than an arbitrary equivalence. No object is chosen from the theorem.
- Precomposition by every `r : K' ⟶ K` is the second conjunct. Its source
  operation is `mapπ₀ ((MonoidalClosed.pre r).app W)` and its topological
  operation is `Quot.map (fun f ↦ f.comp (toTop.map r).hom) ...`. The
  relation-preservation argument is the existing `Homotopic.comp` applied
  to the reflexive homotopy of the fixed realized map.
- Postcomposition by every `s : W ⟶ W'` is the third conjunct. Its source
  operation is `mapπ₀ ((ihom K).map s)` and its topological operation is
  `Quot.map (fun f ↦ (toTop.map s).hom.comp f) ...`, with the analogous
  existing composition argument. Both equations quantify every component
  `x`, not just chosen representatives.
- Neither domain nor target has a nonemptiness, connectedness, finiteness,
  or basepoint binder. There are no assumptions beyond those of the node.

Dependency declarations read and used:

- `def-cbc-enhanced-diagrams-cones`, module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`: read the complete module and
  its docstrings. The statement uses `SSet.Enhanced.diagramVertex`; its
  signature is `{K C : SSet.{u}} (F : K ⟶ C) → ((ihom K).obj C) _⦋0⦌`.
  The same module explicitly adopts Mathlib's `SSet`, `KanComplex`,
  `(ihom K).obj W`, and `SSet.toTop`; those definitions are reused directly.
- Mathlib `Mathlib.AlgebraicTopology.SimplicialSet.PiZero`: `SSet.π₀`,
  `SSet.π₀.mk`, and `SSet.mapπ₀`; full source read, including the quotient
  relation and its equivalence-closure characterization.
- Mathlib `Mathlib.Topology.Homotopy.Basic`: `ContinuousMap.Homotopy`,
  `ContinuousMap.Homotopic`, `ContinuousMap.Homotopic.comp`, and
  `ContinuousMap.Homotopic.refl`; signatures and source read.
- Mathlib's `SSet.toTop` and realization/singular adjunction were read in
  `Mathlib.AlgebraicTopology.SingularSet`. The realizations are the existing
  left Kan extension of the topological simplices, not a replacement model.
- The stated proof dependencies
  `Sheaf.AlgebraicTopology.RealizationFiniteLimits` (`SSet.realization_finite_limits`)
  and `Sheaf.AlgebraicTopology.RealizationCylinder`
  (`SSet.realization_cylinder`) are imported without `public`. Their records
  were read, and the cylinder module including the canonical comparison and
  endpoint formulas was read. The unit-weak-equivalence and Kan Whitehead
  proof nodes have no Lean record in the supplied DAG snapshot, so there is
  no proof-dependency module to import for those two nodes. Their natural
  statements are recorded in the proof docstring, step by step. Neither is
  needed to elaborate this statement; they are not statement prerequisites.

Source check: opened https://kerodon.net/tag/0149 (Proposition the project server) and
https://kerodon.net/tag/0148 (Construction the project server). The proposition gives the
comparison for arbitrary source and Kan target, and its proof uses
postcomposition by the realization/singular unit and its homotopy inverse.
The node is its component-level consequence. The five-step proof docstring
follows the node's adjunction, unit, Whitehead, cylinder, and naturality route.
No source discrepancy or STATEMENT-DISPUTED flag is present.

Edge cases checked before writing:

- `K` empty, including non-Kan sources in general: the empty map is unique,
  so both sides are singletons for every `W`, including empty `W`.
- `W` empty and `K` nonempty: there are no simplicial maps or continuous
  maps of realizations, so both class sets are empty. A nonempty simplicial
  set has a vertex by face restriction and thus a nonempty realization.
- `K = W = Δ[0]`: both sets have exactly one class; the representative
  formula and both naturality equations give the unique value.
- Disconnected targets retain every component; no connectedness was used.
- Identity maps and arbitrary source and Kan-target maps are all included
  by the quantified naturality formulas. Ordinary continuous homotopy is
  unbased, so moving a basepoint imposes no extra requirement.

Searches for an existing statement (through the prescribed `msearch.py`,
Q96 / lem-cbc-kan-realization-mapping-classes):

- LeanFinder query: “Geometric realization gives a bijection from edge
  components of the internal hom into a Kan complex to continuous homotopy
  classes”. Result: 8 hits, including `TopCat.toSSetObjEquiv`,
  `SSet.hoFunctor.unitHomEquiv`, `SSet.unitHomEquiv`,
  `CategoryTheory.SimplicialCategory.homEquiv'`, and `SSet.yonedaEquiv`.
  None identifies the two specified quotient sets by realization.
- Loogle query: `SSet.toTop, ContinuousMap.Homotopic`. Result: 0 hits.
- LeanSearch query: “Continuous homotopy classes of maps between
  realizations are components of the internal hom into a Kan simplicial
  set”. Result: 8 hits, all supplying `ContinuousMap.Homotopic`, its
  reflexivity, homotopy continuity, or the ordinary homotopy structures;
  no realization comparison theorem.
- Mathlib grep query:
  `(toTop|realization).*(Homotopy|homotop|ihom)|(Homotopy|homotop|ihom).*(toTop|realization)`
  in `AlgebraicTopology`: 0 hits.
- Direct `rg` searches in the source project's `WeilConjectures/` for
  realization with homotopy and the node id found no statement. The same
  node-id search with `grep -rn` found no upstream attachment.
- Direct `rg` in `lean/Sheaf` found `KanMappingHomotopyInvariance` and
  `RealizationWeakEquivalence`, which mention this node as a proof input,
  not as an existing theorem. `KanRealizationSerre` uses relative pointed
  mapping classes, a different statement. Searches for the proposed full
  declaration and module names in Mathlib, both project source trees,
  and `dag/lean_names_upstream.json` found no collision.
- Direct Mathlib and project searches for quotients by
  `ContinuousMap.Homotopic` found the existing relation and path-relative
  quotients, but no additional unbased mapping-class definition. The
  literal `Quot` of that existing relation suffices; no helper notion or
  new DAG node is needed.

Validation: `scompile.py Q96 lem-cbc-kan-realization-mapping-classes` compiled
this file both as a sandbox module and under its final library module name,
with no errors or warnings. Every variable and universe is explicitly bound;
there are no private declarations, local notation, local instances, extra
axioms, or data definitions using `sorry`. The signature in `lean.statement`
is copied verbatim from the file. The UTC date is obtained from this machine.

## Second reading by Q96

I independently read the repository node, sandbox node and complete delivered
module, then Kerodon Tags 0149, 0148 and 013H online. This source is Kerodon,
not Stacks; there is no corresponding Stacks .tex source place in the node.
Tag 0149 assumes only that the target simplicial set is Kan. Its comparison
is a homotopy equivalence of mapping Kan complexes; the node asks precisely
for its component consequence. Construction 0148 specifies realization on
maps and its compatibility with both variables. Example 013H identifies
the mapping complex into a singular complex degree by degree. No standing
connectedness, nonemptiness, finiteness or source fibrancy assumption was
found. The node has no statement_change. There is no repair note for this
item, no new node and no dependency module in this delivery.

My object/hypothesis/conclusion checklist, in the order of the node:

1. Fixed universe and simplicial objects: `universe u` and every binder
   `K W K' W' : SSet.{u}` use the same arbitrary universe. Verdict: exact.
   `SSet.toTop.{u}` lands in `TopCat.{u}`, and the internal hom and both
   quotient sets exist in this universe; no universe equality beyond the
   node's fixed-universe convention is imposed.
2. Simplicial sets, Kan complexes, realization and internal functor complex
   from def-cbc-enhanced-diagrams-cones: the public dependency import uses
   Mathlib's `SSet`, `KanComplex`, `SSet.toTop` and `(ihom K).obj W`.
   I opened EnhancedDiagramsCones.lean and read its signatures and bodies,
   especially `diagramVertex {K C : SSet.{u}} (F : K ⟶ C) :
   ((ihom K).obj C) _⦋0⦌`. It evaluates `Functor.natTransEquiv.symm F`
   at the terminal vertex. FunctorHom.lean:142-155 constructs that
   equivalence from actual natural transformations, and
   Closed/FunctorToTypes.lean supplies the internal hom used by the
   simplicial-set monoidal structure. Verdict: the dependency's actual
   objects and canonical vertex are reused, with no substitute notion.
3. Vertices modulo equivalence generated by edges: `π₀ ((ihom K).obj W)`.
   I read PiZero.lean:41-107. Its `π₀Rel` is `Nonempty (Edge x₀ x₁)`,
   `π₀` is its `Quot`, and `π₀.mk_eq_mk_iff` identifies equality with
   `Relation.EqvGen π₀Rel`. `mapπ₀` maps vertex representatives by the
   actual simplicial map. Verdict: exactly the specified edge-generated
   component set, without assuming that the single-edge relation itself
   is already an equivalence relation.
4. Continuous maps modulo ordinary unbased homotopy:
   `Quot (@ContinuousMap.Homotopic |K| |W| _ _)`. I read
   Homotopy/Basic.lean:78-84 and 329-355. `Homotopy` extends
   `C(unitInterval × X, Y)` and imposes only its two endpoint equations;
   `Homotopic` is its `Nonempty`. Its explicit equivalence theorem ensures
   `Quot` adds no identifications beyond continuous homotopy. Swapping
   the factors gives the node's `X × [0,1]` with ordinary product topology.
   Verdict: exact; no relative condition, basepoint or function-space
   topology has entered the conclusion.
5. Arbitrary source `K` and Kan target `W`: the family is quantified as
   `∀ (K W : SSet.{u}) [KanComplex W], ...`; it has no source Kan binder
   and no other instance hypothesis. Verdict: exactly the node's scope.
6. Realization induces a bijection: `∃ e : ∀ ...,
   π₀ ((ihom K).obj W) ≃ Quot ...` gives equivalences, and the first
   conjunct fixes every value by
   `e K W (π₀.mk (diagramVertex a)) = Quot.mk _ (toTop.map a).hom`.
   `π₀.mk_surjective` and the internal-hom vertex correspondence show
   these representatives cover the domain. Verdict: this is the specified
   map `[a] ↦ [|a|]`, not an unconstrained equivalence. The existential
   family merely packages the canonical maps uniformly, as needed for
   naturality; no definition chooses data from this sorry theorem.
7. Naturality under every `r : K' ⟶ K`: the second conjunct uses
   `mapπ₀ ((MonoidalClosed.pre r).app W)` and the quotient map induced by
   `fun f ↦ f.comp (toTop.map r).hom`. I read Closed/Basic.lean:244-273:
   `pre` is the canonical internal-hom precomposition and its uncurry
   equation confirms the direction. `Homotopic.comp` with the reflexive
   homotopy of `|r|` preserves the relation. Verdict: the required square,
   on every component `x`, with arbitrary sources `K` and `K'`.
8. Naturality under every map `s : W ⟶ W'` of Kan targets: the third
   conjunct binds `[KanComplex W] [KanComplex W']`, acts simplicially by
   `mapπ₀ ((ihom K).map s)`, and topologically by the quotient map of
   `fun f ↦ (toTop.map s).hom.comp f`. Verdict: exactly postcomposition,
   with the required two Kan hypotheses and every component quantified.
9. No nonemptiness of either object, and no Kan condition on `K`: there
   are no such binders or implicit instances. Verdict: all cases retained.

Edge cases: for empty `K`, both mapping-class sets are singletons,
including when `W` is empty. For nonempty `K` and empty `W`, both are
empty: a simplex restricts to a vertex, whose realization supplies a point.
For `K = W = Δ[0]` both are singletons. Disconnected targets keep every
component; unbased homotopies may move all points. Degree zero is present
in the vertex and endpoint definitions; no positive-degree restriction
appears in the statement. Identity pre/postcomposition is included in the
universal naturality clauses. Zero objects, schemes, characteristics and
index sets are not objects of this statement. The arbitrary `u` covers
every fixed-universe case of the node.

I independently searched with different wording:

- `msearch.py ... leanfinder "For a fibrant simplicial set Y, pi zero of
  the exponential Y^X equals unbased homotopy classes from the geometric
  realization of X to that of Y"`: eight hits, including
  `TopCat.toSSetObjEquiv`, `SSet.hoFunctor.unitHomEquiv`,
  `SSet.unitHomEquiv` and `HomotopicalAlgebra.FibrantObject.homMk`.
  The first identifies singular simplices with actual continuous maps;
  the others identify vertices or abstract categorical homotopy classes,
  not the two realization mapping-class sets. I also read the abstract
  Whitehead and left/right-homotopy-class equivalence declarations in
  ModelCategory/Homotopy.lean:214-260; they do not state this comparison.
- `msearch.py ... loogle "SSet.π₀, ContinuousMap.Homotopic"`: zero hits.
- `msearch.py ... grep
  '(toTop|realization|realisation).*(π₀|Homotopic)|(π₀|Homotopic).*(toTop|realization|realisation)'`:
  zero hits.
- Direct `rg` of Mathlib, upstream WeilConjectures and `lean/Sheaf` for
  `Quot.*ContinuousMap.Homotopic|ContinuousMap.Homotopic.*Quot` found no
  existing comparison. Searches in upstream WeilConjectures and
  `dag/lean_names_upstream.json` for the proposed declaration, module and
  node id found no upstream attachment or collision.
- Direct project `rg` with realization/realisation/toTop and
  homotop/Homotop/mapping-class/π₀ found nearby nodes. I opened
  KanMappingHomotopyInvariance.lean and RealizationWeakEquivalence.lean:
  their conclusions concern weak-equivalence invariance and detection,
  and their proof docstrings cite this item as input. I opened the
  signatures in KanRealizationSerre.lean: its component comparison is for
  one Kan object, and its higher comparison is relative and pointed;
  neither is the unbased mapping-class theorem. No duplicate was found.

I read the recorded proof-dependency signatures in
RealizationFiniteLimits.lean and RealizationCylinder.lean, including the
canonical cylinder comparison body and endpoint formulas. Their ordinary
cylinder, adjunction and horn-pair interfaces match the five-step proof
docstring. The two remaining proof nodes, realization-singular-unit-weak
and kan-whitehead-inverse, currently have no Lean records and therefore
no module import to add. They are proof inputs, not missing objects needed
to state this theorem. There is exactly one declaration and its proof is
only `sorry`; no data definition or additional theorem is introduced.
The module and theorem docstrings include the correct source and blueprint
id and carry all five proof steps, including the comparison's formula,
naturality and empty cases.

Mismatches found: none. Changes: appended this independent reading only;
the correct Lean file and node record are unchanged. I checked that the
node copy differs from the shared node only in `lean`, that
`lean.statement` equals the complete file signature verbatim, and that
there are no lines over 100 characters, unbound variables, local notation,
private declarations, extra instances or extra axioms. The required
`scompile.py Q96 lem-cbc-kan-realization-mapping-classes
lean/Sheaf/AlgebraicTopology/KanRealizationMappingClasses.lean` completed
successfully for both sandbox and library module names, without errors or
warnings (2.1 and 2.2 seconds respectively).
