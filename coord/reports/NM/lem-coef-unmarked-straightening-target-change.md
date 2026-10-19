## Worker report

The delivery states `SSet.UnmarkedStraightening.unmarked_straightening_target_change`
in `Sheaf.AlgebraicTopology.UnmarkedStraighteningTargetChange`. The node's natural-language
statement is unchanged. Only its `lean` record changes. No dependency record changes and
no new node is needed. No repair note exists for this item.

Source checked: Lurie, Higher Topos Theory, Section 2.2.1, printed pp. 73–74,
https://www.math.ias.edu/~lurie/papers/HTT.pdf, especially Proposition the project server(2).
The source defines straightening by the mapping simplicial sets of the cone pushout and
identifies target substitution with the left adjoint to enriched restriction. The right-adjoint
form and coherences in this node are the consequences spelled out in its seven proof steps.
The module's main theorem docstring reproduces that proof plan step by step.

Hypotheses and clauses, in the order of the node:

- Small simplicial sets are `SSet.{u}`; small simplicial categories are `SCat.{u}`.
  The explicit `universe u` and `set_option autoImplicit false` bind every size and variable.
  The theorem binds `S`; its comparison family quantifies over every `D E : SCat.{u}`,
  `π : D ⟶ E`, and `φ : PinchedCube.rigidification.obj S ⟶ oppositeCategory D`.
- The coherent realization, ordered right cone, last vertex, cone pushout and full enriched
  transformations are the existing dependency declarations. No second cone or diagram notion
  is defined. `Over S` represents every map `a : X ⟶ S` and all its commuting input maps.
- `targetOpposite π` has object map `d ↦ op (π.obj d.unop)` and mapping map
  `π.map e.unop d.unop`. Thus `φ'` is exactly `φ ≫ targetOpposite π`.
- `TargetChangePresentation.L` is normalized by its `straightening` field using the existing
  `IsStraightening`: each value is `value D φ X d`, each full simplicial action is
  `valueAction D φ X d e`, and each input map is `valueMap D φ f d`. These are the actual
  `M(e,v)` with precomposition action, not ordinary diagrams on the underlying category.
- `targetRestrictionObj π F` is exactly `π.comp SSet F.functor` wrapped in the existing
  `Diagram`. `targetRestrictionHom` has components `f.app (π.obj d)` with the full enriched
  action square. `targetRestriction π` packages these explicit object and arrow maps.
- The enriched left Kan extension is `TargetChangeComparison.kan`. Its `kanAdj` is an
  adjunction to the actual `targetRestriction π` in the categories whose arrows are strict
  enriched transformations. Its `homEquiv` therefore has the precise natural-bijection
  meaning of the node's `π_!`, rather than ordinary Kan extension along underlying functors.
- `targetPushoutMap π φ X` is the actual `pushout.map`, using the identity on the realized
  cone, `targetOpposite π` on the coefficient target, and identity on the common boundary.
  Its two defining leg equations follow from `pushout.map`. `targetPushoutMap_objects`
  states the old-object and fixed-last-vertex consequences. `targetValueMap` applies its
  enriched mapping map and transports only these endpoint equalities.
- `TargetChangeComparison.unitMap` is natural in every `X : Over S` and is an enriched
  transformation `L_φ(X) → π* L_φ'(X)`. Its `unitMap_eq` fixes every simplicial component
  to `targetValueMap`. Thus it is the specified pushout map, not an arbitrary map.
- `mate` is an isomorphism of functors `L_φ ⋙ π_! ≅ L_φ'`. Its `mate_adjunct` equation
  identifies its hom at each `X` with the precise adjunct of `unitMap` under `kanAdj`.
  Naturality in `X` is part of this natural isomorphism. For another presentation of
  `π_!`, the unique adjunction comparison transports exactly this mate; no choice of
  an unrelated isomorphism is allowed by the equation.
- `homEquiv X G` is the transformation-set bijection in the node's equivalent formulation.
  `homEquiv_apply` is exactly `b ↦ unitMap.app X ≫ (targetRestriction π).map b`.
  Naturality in `G` follows directly from this formula and functoriality; in `X` it follows
  from naturality of `unitMap`.
- `TargetChangePresentation.U` and `description` use the existing `SimplexDescription`.
  It gives all `n`-simplices as pairs `(σ, enriched transformation)`, their projection
  to `S`, every simplex operator, and the maps in `G`. No arbitrary right adjoint is
  substituted for the directly described simplicial set.
- `unstraightening` is a natural isomorphism `U_φ' ≅ π* ⋙ U_φ` valued in `Over S`,
  so each component is an isomorphism over the fixed base. `unstraightening_simplex`
  states that each simplex keeps its `σ` and applies the very same `homEquiv` to its
  enriched transformation. Its simplex operators and naturality in `G` are therefore
  precisely those required in the node.
- The first final conjunct states the identity law for every component of `unitMap`.
  The second states `u_(ρπ) = u_π ≫ π*(u_ρ)` on every simplicial mapping object, for every
  `X,d`. Because `mate_adjunct` specifies every mate, these are equivalently the identity
  and composition laws for mates under the canonical identity/composed adjunction
  identifications of `π_!`. Equality of adjuncts determines equality of the mates.
- The third final conjunct is the identity law for the underlying simplicial map of
  every `U` comparison. The fourth is its composite law. Since all these are maps in
  `Over S`, equality of underlying maps is exactly equality over `S`.
- Compatibility with every map `X → Y` over `S` is included in the natural transformation
  `unitMap` and the natural isomorphism `mate`; its simplex-instance form supplies the
  operator compatibility of `unstraightening`.
- No Kan, local Kan, Dwyer–Kan, fibrancy, cofibrancy, inhabitedness, or injectivity of
  `π.obj` is assumed anywhere.

The uses of `HEq` have a specific purpose. The existing `IsStraightening.obj_eq` presents
canonical cone values by equality rather than definitionally. Identity/composite target
functors also give equal, rather than definitionally equal, attaching functors and
restricted diagrams. `HEq` is exactly equality after these equality transports; it is not
an isomorphism condition and does not discard any simplicial degree. The composition
formulas compare maps on entire simplicial sets, not merely their zero-simplices.

The existential `P` and `T` are simultaneous presentations of the already named canonical
functors and comparisons. Their objects, enriched actions, arrows, comparison components,
adjuncts and simplex maps are fixed by the displayed normalizations. No definition extracts
an object, map, functor or isomorphism from this existential theorem. In particular there
is no choice of data from a theorem with a postponed existence proof. Helpers belong to
the node's target substitution construction, as allowed by the human's owning-module
helper convention; they do not introduce an independent mathematical notion.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: the existing `SSet`/simplex conventions
  and `SSet.Enhanced` coherent constructions, imported through the recorded straightening
  dependency. Only its simplicial primitives are needed here; no quasicategory assumption
  is imposed on `S` or `D`.
- `Sheaf.AlgebraicTopology.UnmarkedStraighteningQuillen`:
  `Diagram`, `DiagramHom`, `DiagramHom.app`, `action`, `diagramHomOfComponents`,
  `oppositeCategory`, `conePushout`, `baseObject`, `coneVertex`, `value`, `valueAction`,
  `valueMap`, `IsStraightening`, `SimplexDescription`, and
  `unmarked_straightening_quillen`. The recorded module and its full construction
  signatures/docstrings were opened. The presentation fields reuse its normalized
  interfaces directly, including the full enriched action square.
- `Sheaf.AlgebraicTopology.PinchedCubeLatching` (through that public import):
  `SSet.PinchedCube.rigidification`, the existing coherent realization.
- Proof-only import `Sheaf.AlgebraicTopology.ConeBoundaryProjectiveCells`:
  `SSet.CoherentCone.cone_boundary_projective_cells`; its structural clause is the
  first step of the proof and has no model-category hypotheses. Its full signature
  and surrounding docstrings were opened.
- Mathlib's `EnrichedFunctor.comp`, `EnrichedCategory.opposite`, `GradedNatTrans`,
  `pushout.map`, `Adjunction.homEquiv`, `NatIso`, and `Over` are reused. Mathlib's
  ordinary `EnrichedNatTrans` is deliberately not substituted for `DiagramHom`.

Edge cases checked mathematically before writing and against the compiled binders:

- `X` empty: the cone is just its last vertex and all old-to-last maps are empty;
  the comparison and the Kan extension of the initial diagram remain isomorphisms.
- `S` empty: its slice contains only empty simplicial sets up to isomorphism. No
  vertex or nonemptiness binder is needed; the same initial diagrams occur.
- `D` empty (with the possible `φ`, hence empty `S`): restriction and enriched
  Kan extension have the expected unique/initial values. Nothing requires an object.
- `X = Δ[0]`, including a simplex over a vertex: the construction is the usual
  representable/free cone diagram and gives the corresponding Kan-extension map.
- `π = id` and two successive target maps: the final four conjuncts retain these
  cases explicitly, including the canonical equality transports.
- A functor identifying objects or with non-Kan mapping spaces: `pushout.map` and
  the enriched transformation bijection remain defined; no faithfulness/injectivity
  or Kan hypothesis appears.
- Degree zero and arbitrary higher operators: `n : SimplexCategory` includes zero
  and `SimplexDescription.operator` includes all monotone maps. No dimension is omitted.

Searches performed (actual msearch outputs are retained in `searches.jsonl`):

- `msearch.py ... leanfinder "enriched cone straightening change of target is left Kan
  extension"`: 8 hits, including ordinary `RightExtension.coneAtFunctor`,
  `coneOfIsRightKanExtension`, and `Enriched.FunctorCategory.coneFunctorEnrichedHom`.
  These do not state the cone-pushout target-change result. The relevant enriched
  definitions and ordinary Kan-extension signatures were read in the source.
- `msearch.py ... loogle "EnrichedFunctor, GradedNatTrans"`: no hits, unknown identifier
  `EnrichedFunctor` in the remote index. A corrected `loogle '"GradedNatTrans"'` search
  returned 7 hits including the existing structure, app and naturality. These support
  reuse of the strict transformation notion, but do not supply the item theorem.
- `msearch.py ... leansearch "Changing target in enriched cone straightening is enriched
  left Kan extension"`: 8 hits, including `Functor.leftKanExtension`,
  `Functor.IsLeftKanExtension`, and ordinary left-extension/cocone declarations.
  These concern ordinary functors, not the enriched cone-pushout comparison.
- `msearch.py ... grep 'targetChange|target_change|[Ss]traightening'
  CategoryTheory/Enriched`: zero hits.
- `rg -n 'targetChange|target_change|[Ss]traightening'` in upstream `WeilConjectures`
  and side-project `lean/Sheaf`: existing straightening modules, including the recorded
  dependency, but no target-change theorem. The upstream item-id search was empty.
- `rg` for all new helper names and the theorem name in Mathlib, upstream
  `WeilConjectures`, side-project `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no declarations with these names. Existing cone and diagram definitions are reused.

Six postponed theorems belong to this node, all with source/blueprint and complete proof
instructions in their docstrings: `targetOpposite_comp`, `targetRestriction_naturality`,
`targetRestrictionHom_id`, `targetRestrictionHom_comp`, `targetPushoutMap_objects`, and
`unmarked_straightening_target_change`. Every theorem body is exactly `by sorry`.
Every definition has explicit data; only proof fields refer to the named helpers.

Validation: `scompile.py NM lem-coef-unmarked-straightening-target-change
lean/Sheaf/AlgebraicTopology/UnmarkedStraighteningTargetChange.lean` compiled both the
sandbox form and the module form cleanly. The latest complete-module compile took
6.1 seconds and 2.6 seconds respectively, with no errors or warnings. All Lean lines
are at most 100 characters. The exact signature is extracted by the shared stage-2
signature reader into the node record. No statement dispute or node fault was found.

The required `deliver2.py ... --no-push` dry run is the final worker validation; an
independent second reader supplies its own section and performs the eventual delivery.

## Second reading by NM

I independently read the item node and all 254 lines of its Lean module, rather
than relying on the worker's report. I opened the recorded dependency modules
`EnhancedDiagramsCones`, `UnmarkedStraighteningQuillen`, and the structural
proof dependency `ConeBoundaryProjectiveCells`, including their actual
signatures and construction data. I also read `PinchedCubeLatching.rigidification`
and Mathlib's enriched composition/opposite declarations. There is no repair
note for this item. There are no new nodes, dependency modules, or statement
corrections to review. The Lean statement says what the node says; I found no
mathematical or interface mismatch and preserved the Lean and node records.

Source verification: I opened the IAS HTT PDF independently, Section 2.2.1,
printed pp. 73--74 (PDF pages 90--91, zero-based), including the cone pushout,
the displayed mapping-object definition of straightening, the right adjoint,
and Proposition the project server(2). The source has arbitrary simplicial sets and
simplicial categories here; fibrancy conditions belong to later comparison
results. It uses the same opposite target and the left adjoint of composition
with the coefficient functor. This is not a Stacks-sourced item, so there is
no Stacks .tex location to substitute for this source. The right-adjoint
formula and identity/composition conditions are the explicit consequences of
the seven-step proof supplied by this node.

Object, hypothesis, and conclusion checklist (in node order):

1. Small simplicial sets, coherent realization, small simplicial categories,
   and enriched transformations: `SSet.{u}`, `SCat.{u}`,
   `PinchedCube.rigidification`, and the recorded `Diagram`/`DiagramHom`.
   `DiagramHom` wraps tensor-unit `GradedNatTrans`; its naturality is the
   full action square of simplicial maps. Verdict: exact objects, not
   diagrams with only ordinary naturality.
2. Fixed arbitrary base `S`: the theorem's sole outer parameter is
   `(S : SSet.{u})`. The simultaneous comparison witness then quantifies
   over every `D E : SCat.{u}`, `(π : D ⟶ E)`, and
   `(φ : rigidification.obj S ⟶ oppositeCategory D)`. `targetOpposite`
   has objects `op (π.obj d.unop)` and mapping maps `π.map e.unop d.unop`.
   Thus `φ ≫ targetOpposite π` is exactly the stipulated new attaching
   functor. Verdict: no extra hypothesis; correct variance.
3. Every `a : X ⟶ S` and every map of such inputs: `X : Over S` and
   its category of arrows. The reused `conePushout` attaches
   `C[X]` to `C[X star Delta[0]]` and `D` opposite by `C[a] ≫ φ`.
   `coneVertex` is the pure final-block vertex; `value` is the actual
   mapping simplicial set from the included `op d` to that vertex.
   Verdict: the same ordered cone and categorical enriched pushout.
4. `L` has precisely these objects and precomposition action:
   `P.straightening` is `IsStraightening`, whose `obj_eq`, `action_eq`,
   and `map_eq` identify every value, full simplicial action, and input
   arrow with `value`, `valueAction`, and `valueMap`. Verdict: complete
   normalization, including input naturality, with no substitute functor.
5. Restriction is composition with `π`: `targetRestrictionObj` uses
   Mathlib's `EnrichedFunctor.comp`. `targetRestrictionHom` evaluates
   components at `π.obj d`, with its full action square supplied by the
   named naturality theorem. Verdict: the exact enriched restriction
   functor on the intended transformation sets.
6. Enriched left Kan extension and its defining natural bijections:
   `TargetChangeComparison.kan` and `.kanAdj : kan ⊣ targetRestriction π`.
   This is an ordinary categorical adjunction between the categories of
   enriched diagrams and strict enriched transformations, precisely the
   node's definition of enriched left Kan extension. Verdict: exact.
   A different adjoint presentation transports the comparison uniquely;
   the existence of a normalized presentation loses no case of the node.
7. The canonical map of cone pushouts: `targetPushoutMap` is `pushout.map`
   with identity cone and boundary maps and `targetOpposite π` on the
   coefficient target. Its defining leg equations determine it.
   `targetPushoutMap_objects` records its old-object and final-vertex
   images; `targetValueMap` uses its entire enriched hom map and transports
   only these endpoint equalities. Verdict: the stipulated map, not an
   unconstrained choice.
8. The induced map `L_φ(X) → π* L_φ'(X)`:
   `.unitMap` is a natural transformation in `X`, with every component
   fixed to `targetValueMap` by `.unitMap_eq`. Verdict: exact map and
   enriched/input naturality. Here `HEq` is equality of simplicial maps
   after the object equalities from `IsStraightening`, not agreement only
   on vertices or up to homotopy.
9. Its adjunct is an isomorphism natural in the input:
   `.mate : P.L D φ ⋙ kan ≅ P.L E (φ ≫ targetOpposite π)` and
   `.mate_adjunct` says its hom is the inverse image of `unitMap.app X`
   under the specified adjunction bijection. Verdict: exactly the
   canonical mate with the required direction and all input maps.
10. The equivalent transformation-set bijection: `.homEquiv` and
    `.homEquiv_apply` identify it with
    `b ↦ unitMap.app X ≫ (targetRestriction π).map b`.
    Naturality in diagrams follows from this formula and functor laws;
    naturality in the input follows from `unitMap.naturality`.
    Verdict: the specified natural bijection, without a missing condition.
11. The definition of `U` on every simplex over `σ`:
    `P.description : SimplexDescription ...` has `.equiv`, `.projection`,
    `.operator`, and `.map`, prescribing the pairs, their projection to
    `S`, every simplex operator, and every diagram arrow. Verdict: the
    node's directly described unstraightening, with all degrees retained.
12. Its comparison: `.unstraightening` is a natural isomorphism
    `P.U E φ' ≅ targetRestriction π ⋙ P.U D φ` in `Over S`.
    `.unstraightening_simplex` keeps `σ` and applies exactly `.homEquiv`
    to its transformation. Verdict: the canonical isomorphism over `S`,
    natural in `G`; its operator compatibility follows from its simplicial
    map type and the displayed simplex formula.
13. Identity and composite coherence for straightening: the first two
    final conjuncts quantify over all targets, attaching maps, inputs,
    and objects, and assert the identity and composite laws for the
    entire simplicial components of `unitMap`. Verdict: exact. By
    `.mate_adjunct`, uniqueness of adjuncts gives the corresponding mate
    laws under the canonical identity/composed adjunction comparisons.
    This does not require choosing equality of unrelated Kan functors.
14. Identity and composite coherence for unstraightening: the last two
    conjuncts assert the corresponding equalities of underlying
    simplicial maps. Maps in `Over S` are determined by these underlying
    maps. The `HEq` endpoints differ only by equality of identity/composite
    target functors and restriction functors. Verdict: exact coherence
    over the fixed base, retaining the identity case.
15. No Kan, local Kan, Dwyer--Kan, fibrancy or cofibrancy assumptions:
    inspection of the complete theorem and both witness structures finds
    none. Imports of the earlier model comparison do not insert these
    assumptions into its definitions. Verdict: the unrestricted assertion.

Edge cases checked independently: empty `X` has the disjoint old category
and cone vertex, hence initial straightening; empty `S` has no nonempty
input; empty `D` forces an empty attaching source, while the unique enriched
restriction still has its left adjoint. No `Nonempty` instance excludes any
of these. The one-vertex input gives the expected representable cone
calculation. Degree zero and every higher simplex operator are present
through arbitrary `SimplexCategory` objects and arrows. Target functors may
identify objects or have non-Kan mapping spaces. Identity and two successive
target changes are asserted explicitly. The common arbitrary `u` is the
small-set universe specified by the node: the dependencies use `SSet.{u}`
and `SCat.{u}` throughout, with no new universe equality or finite-size
restriction. Schemes, ring characteristics and integer truncation parameters
are not objects or hypotheses of this statement.

Independent searches, with words different from the worker's first queries:

- LeanFinder: `Base substitution for simplicial enriched correspondence
  mapping diagrams commutes with left adjoint to restriction`. Eight hits
  concerned enrichment transport, enriched functor categories and generic
  adjoints; none computes these cone pushouts or their canonical mate.
- Loogle: `"EnrichedFunctor.comp"`. Three hits are the existing composition
  and its object/map equations. These are reused in `targetRestrictionObj`;
  none is a target-change theorem.
- LeanSearch: `Change the coefficient category of a simplicial cone pushout
  and obtain a canonical enriched left Kan extension isomorphism`. Eight
  hits are ordinary Kan-extension/cocone theorems. Their signatures do not
  state enriched cone straightening or this normalized comparison.
- `rg` in Mathlib's `CategoryTheory/Enriched` and `AlgebraicTopology`, and
  upstream `WeilConjectures`, for target change and straightening variants:
  no existing theorem. I also searched the side project's `lean/Sheaf` and
  read the existing straightening and cone modules rather than treating
  similarly named declarations as matches. Mathlib's enriched opposite
  file supplies the category and its composition equations, not the
  enriched opposite functor or this target restriction/comparison.

The helper declarations carry explicit construction data. Their five
proof obligations and the main theorem have named `by sorry` bodies,
source/blueprint docstrings, and natural-language proofs; the owning node
and its proof steps cover their target-change assertions. No object is
extracted from a postponed mere-existence proof. The main docstring gives
all seven node proof steps. All variables/universes are bound, there is no
file-local notation or instance, every Lean line meets 100 characters, and
the recorded `lean.statement` agrees with the main signature (whitespace
normalized by the delivery signature reader).

Changes by this second reader: this independent report section only; no
Lean, node statement, dependency, or definition needed repair. I also opened
the two citers, `lem-coef-space-valued-straightening` and
`lem-coef-unmarked-relative-nerve-cone-comparison`: their uses of arbitrary
target change, input naturality, and identity/composition laws remain valid.
This was a supplementary consumer check, not a statement-change audit.

Validation: the prescribed `scompile.py` compiled the only delivered module
as both sandbox and library forms, cleanly in 2.2 s and 2.8 s, with no
errors or warnings. The dry run and delivery below use the required wrapper;
no global build or direct live-library mutation was performed.
