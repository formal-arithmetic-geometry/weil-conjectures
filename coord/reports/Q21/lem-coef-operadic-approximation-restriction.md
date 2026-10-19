## Worker report

The delivery states `SSet.Enhanced.operadicApproximationRestriction` in
`Sheaf.CategoryTheory.OperadicApproximationRestriction`. Its only theorem has proof
`sorry`. The module docstring gives the source, and the theorem docstring gives all
six proof steps, including the relative enriched-Hom argument in the opposite slice.
The original mathematical statement, proof and proof dependencies are unchanged.
The statement dependencies additionally cite the new approximation node and the landed
`def-coef-relative-symmetric-operadic-algebras` interface reused in this repair.

Source checked: Higher Algebra, September 2017 edition, online PDF, printed page 260,
Definition the project server, and printed pages 268–270, Definitions the project server/28, Theorem
the project server and its proof. The approximation definition tests locally cocartesian colour
projections and cartesian lifts of active arrows, and permits a categorical-equivalence
factorization. The unary-fiber equivalence is a separate hypothesis of the theorem.

Hypothesis and clause correspondence:

- Quasicategories, coherent functors and size: `{C P E : SSet.{u}}` and the three
  `Quasicategory` instances. A single arbitrary universe contains all three small
  simplicial sets; the finite pointed-set skeleton is canonically lifted with
  `AsSmall.{u}`. This also covers simplicial sets originally lying in different
  universes by passage to a common universe.
- The map of the infinity operad to finite pointed sets is
  `p : P ⟶ finStarBase`. The hypothesis `hp : IsSymmetricInfinityOperad p`
  is the existing predicate from `RelativeSymmetricOperadicAlgebras`. It requires
  `Quasicategory P`, `InnerFibration p`, inert cocartesian lifts, the operation-space
  Segal comparison, and tuple objects for every finite colour family. The latter
  two express the fibre Segal equivalence (HA Remark the project server), including arity zero. The standard simplices, nerves,
  products, pullbacks and horns are the existing Mathlib constructions.
- `FinStar` is the existing skeleton with underlying pointed object `Fin (n+1)`
  pointed by zero. `IsFinStarInert` requires a unique preimage for each nonzero
  output; `IsFinStarActive` allows only zero to map to zero. `finStarRho i` retains
  the input `i.succ`. All these declarations are imported and reused.
- `IsSymmetricInertEdge p e` is `IsCocartesianEdge p e` together with inertness
  of the entire image edge. This is also exactly the marking pulled back along `f`.
- `hf : IsOperadicApproximation p f` is an existential factorization through an
  actual quasicategory `D`, an actual simplicial map `e : C ⟶ D` satisfying the
  existing `IsFunctorEquivalence`, and an actual map `g : D ⟶ P` with `e ≫ g = f`.
  No replacement is chosen. `IsFibrantOperadicApproximation p g` first requires the
  existing `IsIsofibration g`, namely both quasicategories, inner horn lifting and
  source-prescribed equivalence-edge lifting.
- Approximation clause (i) quantifies over `c`, every `n`, its arity equation,
  and every `i : Fin n`. The existential edge has the prescribed source, image
  `finStarEdge (finStarRho i)`, local cocartesianness for `g ≫ p`, and
  inert image in `P`. `IsLocallyOperadicCocartesian` forms the actual pullback over
  the full image edge and tests its canonical lifted edge for cocartesianness.
- Approximation clause (ii) quantifies over every edge `a` ending at `g(c)` whose
  pointed-set image is active, and asks for an edge with target exactly `c`, image
  exactly `a`, and `IsCartesianEdge g`. It does not ask for all arrows to lift.
- `hcolour : IsFunctorEquivalence (operadicColourMap p f)` uses the induced
  pullback map on the original strict fibres over `finStarVertex 1`. In
  particular this condition is not imposed on an arbitrary replacement `D`.
- `r : E ⟶ P` and `hr : IsSymmetricOperadicFibration p r` expand to the existing
  categorical-fibration predicate, lifts of all `IsSymmetricInertEdge p`
  edges, `HasSymmetricOperadicSegalFibers p r`, and
  `HasSymmetricOperadicMappingSegal p r`.
- The fibre Segal predicate quantifies over each base object of arity `n` and all
  its cocartesian colour projections. It requires actual transport functors on
  the strict fibres, characterized by a cylinder whose component edges are
  `r`-cocartesian, whose endpoint maps are the specified functors, and whose entire
  image is the prescribed base edge. `Pi.lift T` must be a functor equivalence.
  Endpoint equality transports are only `eqToHom`, not additional data.
- The mapping Segal predicate quantifies over every input object and base arrow,
  and all cocartesian output projections and composition triangles over that
  arrow. It uses the existing `monoidalRelativeMap` and simultaneous composition
  graph. The map from the graph to the product is normalized by all its long-edge
  projections and must be an `IsWeakHomotopyEquivalence`. Inner horn filling makes
  the graph's input projection a contractible-choice model of composition. Thus
  the normalized graph map expresses precisely the mapping-space product
  comparison, also over a non-discrete quasicategory `P`.
- The left category in the conclusion is
  `(operadicSections p r (𝟙 P)).toSSet`, and the right is
  `(operadicSections p r f).toSSet`. `relativeOperadicDiagramComplex f r` requires the base equation
  for every degree, parameter map and domain simplex. It fixes transformations
  and all higher simplices over the identity of the given base diagram. The
  intersection with `fullSubcomplex` imposes inert preservation on all vertices
  only. No edges of the parameter are required to be equivalences; in particular
  noninvertible transformations are included.
- The main conclusion is the existing
  `IsFunctorEquivalence (operadicSectionRestriction p r f)`, with a coherent
  simplicial quasi-inverse and coherent natural inverse equivalences. The
  restriction map itself is explicitly defined in every degree by
  `Functor.HomObj.comp (Functor.HomObj.ofNatTrans f) s.1`; it changes the domain
  coordinate and retains the full parameter. It is not an existentially chosen
  equivalence or just an equivalence of cores/homotopy categories.
- Naturality under compatible marked target maps is the second conjunct. The
  map `h` lies over `P` by `hc` and preserves precisely the relevant cocartesian
  marked edges by `hm`. Both routes in the displayed equality are the actual
  degreewise maps, with no equivalence chosen.
- Naturality under restriction of the target over a base is the third conjunct.
  The commuting square `g ≫ f = b ≫ j` gives the explicit equality between the
  two restriction routes. In particular take `D = P' ×_P C`, with its projections,
  for restriction to a base suboperad. Sections of `P' ×_P E → P'` are exactly
  coherent lifts of `j : P' → P`; these are the actual over-diagram sections used
  on the right route. This strict over-diagram formulation is the degreewise
  pullback formulation, and retains all coherences. It does not assume the square
  is homotopy cartesian or require properness.
- There are no assumptions of limits, colimits or presentability of the fibres,
  and no cocartesian-lifting assumption over active arrows of the target `r`.
- The references to `L` and `A` in the node fix the illustrative LM convention;
  these are not extra objects quantified in the general theorem. Their ordered
  category, nerves, inertness and operadic-fibration conditions remain those in
  the dependency `LeftModuleOperadicEncoding`, rather than a redefined LM model.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `IsEquivalenceEdge`,
  `fullSubcomplex`, `diagramVertex`, `IsFunctorEquivalence`,
  `IsWeakHomotopyEquivalence` in namespace `SSet.Enhanced`, and Mathlib's `ihom`.
- `Sheaf.CategoryTheory.InfinityFibrations`: `fiber`, `IsCocartesianEdge` and
  `IsCartesianEdge` in that same namespace; Mathlib's `InnerFibration`.
- `Sheaf.CategoryTheory.LeftModuleOperadicEncoding`: the full live module was
  read with `scompile.py --source`, including `IsLMCategoricalFibration`,
  `HasLMSegalFibers`, `HasLMMappingSegal`, `IsLMOperadicFibration`, `lmBase`,
  `lmAlgebraBase`, `lmSections` and `CoherentLeftTensoring`. It landed during this
  task and now has its Q16 Lean record. No dependency repair is delivered.
- `Sheaf.CategoryTheory.MonoidalInfinityCategory`: `monoidalRelativeMap`,
  `monoidalRelativeMapInclusion`, `monoidalCompositionGraph`, and
  `monoidalCompositionLongEdge`. These already have arbitrary simplicial bases;
  no new mapping-space or composition-graph model is introduced.
- `Sheaf.CategoryTheory.IsofibrationExponentiation`: `SSet.Enhanced.IsIsofibration`
  is reused for all categorical-fibration requirements, rather than copied.
- `Sheaf.CategoryTheory.RelativeSymmetricOperadicAlgebras`: `FinStar`,
  `finStarBase`, `finStarVertex`, `finStarEdge`, `finStarRho`,
  `IsSymmetricInfinityOperad`, `IsSymmetricInertEdge`, `IsActiveEdge`,
  `operadicDiagram` and `relativeOperadicDiagramComplex`. Their complete source
  signatures and docstrings were read in this repair; their owning node is
  `def-coef-relative-symmetric-operadic-algebras`.
- The recorded, already-stated proof dependencies
  `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`,
  `Sheaf.AlgebraicTopology.MarkedPointCartesianModel` and
  `Sheaf.CategoryTheory.SimplicialModelNerveLocalization` are imported without
  `public`. The other four proof dependencies have no Lean records yet; no import
  exists to add for them. None of those theorems is being restated in this delivery.

Edge cases checked before and during writing:

1. Arity zero: `Fin 0` is empty. The fibre Segal assertion still requires an
   equivalence from the zero fibre to the actual empty product. The mapping
   assertion still requires the map to the empty product to be a weak homotopy
   equivalence. Neither case is omitted or made merely vacuous.
2. Arity one: the colour map is the actual strict unary-fibre map. A fold from
   two copies of an operad to one can be an approximation but fails this
   equivalence, so the separate unary hypothesis is essential.
3. An empty colour fibre is not required to be inhabited; all lifting clauses
   retain their source/target quantifiers, and no arbitrary section is assumed.
4. `f = id` is allowed and gives the actual identity precomposition formula.
   General approximations are not narrowed to categorical fibrations.
5. Inert maps to the zero pointed set have no non-basepoint outputs and are
   inert vacuously; active maps include the nullary active operation. Both enter
   the definitions. The projection clause itself is vacuous only when `n = 0`.
6. At every simplicial degree the base equation is imposed on all parameter
   simplices. Imposing it only on vertices would be wrong; `relativeOperadicDiagramComplex`
   explicitly avoids that. Noninvertible parameter edges remain unrestricted.
7. There is no chosen equivalence, transport or operadic object extracted from
   an unproved existence theorem. All new definitions have real data, and their
   subtype/naturality/equality proofs are structural proofs of those formulas.

Searches performed (raw service records are included in the new node):

- `msearch.py leanfinder`, query "Restriction of inert preserving coherent
  sections along an operadic approximation is an equivalence of infinity
  categories": eight ordinary nerve/homotopy-category hits, no match.
- `msearch.py loogle`, query `SSet, InnerFibration, IsFunctorEquivalence`: no
  hits; the service reported unknown identifier `InnerFibration`.
- `msearch.py grep`, query `Operad|operadic|Approximation|CategoricalFibration`
  in `AlgebraicTopology`: three unrelated simplicial-approximation hits.
- `msearch.py leansearch`, query "Symmetric infinity operad as inner fibration
  over finite pointed sets with inert lifts and Segal mapping space product":
  eight hits on strict Segal sets, model-category primitives and the simplicial
  cartesian monoidal structure, no symmetric operad definition.
- `msearch.py leanfinder`, query "Symmetric infinity operad over finite pointed
  sets and approximation with inert locally cocartesian colour projections and
  active cartesian lifts": eight Cech/nerve/strict-Segal hits, no match.
- `rg` for the intended declaration names in Mathlib, upstream `WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no existing declarations at the original search time; the repair now reuses
  the landed symmetric operad interface identified by the maintainer.
  `rg` for the item id in upstream `WeilConjectures`: no hits.
- Concept searches in all DAG nodes and `blueprint_refs.py search 'operadic
  approximation'` found no independent definition node for these notions.
  `def-coef-operadic-weak-approximation` is over `Delta^op` and is a different
  nonsymmetric notion. `def-coef-symmetric-operadic-family` defines families and
  explicitly cites this item for symmetric operads; using it here would be
  circular. The general isofibration predicate found during the search is reused.

Validation: both delivered modules were compiled separately in dependency order
through `scompile.py`, including the module paths used by their imports. Both
compile without errors or warnings. Only the intended item theorem is postponed.
There is no statement correction or STATEMENT-DISPUTED finding.

## New nodes

`def-coef-symmetric-operadic-approximation`, in
`Sheaf.CategoryTheory.SymmetricOperadicApproximation`, reuses the landed symmetric
finite-pointed-set base, infinity-operad predicate and inert/active edges; it supplies
the two relative Segal conditions, general
relative operadic fibrations, local cocartesianness, both approximation clauses,
its general factorization and original colour map, and the full relative section
simplicial sets with their explicit restriction/postcomposition maps. Its source
is HA Definitions the project server, the project server and the project server and the relative section objects
in Theorem the project server. The existing nonsymmetric weak-approximation and symmetric
family nodes do not define this prerequisite; the latter depends on this item.
The three service search kinds and repository/DAG searches above establish the
missing interface. Mathlib pointed maps, existing fibrations/equivalences, the
project's general isofibration, and its existing relative composition graphs
are reused. Every declaration of the new module is listed in its Lean record;
there are no postponed theorems in it.

## Earlier second reading (a previous round; superseded)

The node's objects and hypotheses were matched against
`SSet.Enhanced.operadicApproximationRestriction` in
`Sheaf.CategoryTheory.OperadicApproximationRestriction` as follows.

- The three quasicategories are `C`, `P`, and `E : SSet.{u}` with the three
  `[Quasicategory ...]` instances; the common universe is arbitrary and the
  theorem is universe-polymorphic. The maps are `p : P ⟶ finStarBase`,
  `f : C ⟶ P`, and `r : E ⟶ P`.
- The infinity-operad hypothesis is `hp : IsSymmetricInfinityOperad p`. Its
  existing definition supplies inner fibrancy, inert lifts, the mapping-space
  Segal comparison and tuple objects, equivalently the fibre Segal property.
  `FinStar`, `finStarRho`, inert/active edges and `finStarBase` are imported
  from `RelativeSymmetricOperadicAlgebras`.
- The approximation hypothesis is exactly `hf : IsOperadicApproximation p f`.
  Its factorization is an existential quasicategory `D`, equivalence
  `e : C ⟶ D`, and categorical-fibration approximation `g : D ⟶ P`, with
  `e ≫ g = f`. The categorical-fibration approximation has the source-fixed
  locally cocartesian colour projections for every `i : Fin n` and the
  target-fixed cartesian lifts of active edges. No replacement is selected.
- The unary-colour hypothesis is
  `hcolour : IsFunctorEquivalence (operadicColourMap p f)`, where the map is
  the pullback map on the original strict fibres over `finStarVertex 1`.
  This is the node's colour-fibre equivalence, rather than a condition on the
  existential replacement in `hf`.
- The target hypothesis is `hr : IsSymmetricOperadicFibration p r`. It gives
  the recorded isofibration, inert cocartesian lifts, fibre Segal comparison,
  and output mapping-space product comparison. It has no active-lift,
  presentability, limit, or colimit assumption.
- The first conclusion is
  `IsFunctorEquivalence (operadicSectionRestriction p r f)`. The map is the
  explicit degreewise precomposition map from
  `(operadicSections p r (𝟙 P)).toSSet` to
  `(operadicSections p r f).toSSet`; `operadicSections` fixes the whole base
  simplex and imposes inert preservation on vertices, so transformations and
  higher simplices remain noninvertible when they are noninvertible.
- The second conclusion is the target-map naturality clause. For every
  `h : E ⟶ E'` over `P` preserving the marked `r`-cocartesian edges, the
  displayed equality compares the two actual composites with
  `operadicSectionPostcompose`.
- The third conclusion is the base/restriction naturality clause. For every
  commuting square `g ≫ f = b ≫ j`, the displayed equality compares the two
  actual precomposition maps `operadicLiftRestriction`; this is the strict
  degreewise form of restricting the target diagram over a base map.

The source reading was HA (September 2017), Definition the project server (PDF p. 260),
Definition the project server and Theorem the project server (PDF pp. 268--269). Definition
the project server has precisely the two clauses encoded by `IsFibrantOperadicApproximation`,
and its arbitrary-map clause is the stated equivalence followed by a categorical
fibration. Definition the project server marks exactly edges whose image is inert. Theorem
the project server supplies the unary-fibre equivalence and the marked preoperad
restriction equivalence. No source hypothesis is absent from the Lean binders,
and no extra mathematical hypothesis is used.

Edge cases checked: `n = 0` makes the `Fin 0` projection family and the two
finite products genuinely empty (the Segal conditions still compare with the
terminal empty product); `n = 1` retains the unary colour map; nullary active
maps and inert maps to the zero pointed set are included; empty colour fibres,
empty simplicial sets, and `f = 𝟙 P` are not excluded; all simplicial degrees,
including parameter edges and higher simplices, satisfy the base equation.

Searches were repeated with `rg` over the project Lean tree, the slopmaster2
`WeilConjectures` tree, Mathlib, the DAG and `dag/lean_names_upstream.json`, and
with the recorded LeanSearch, LeanFinder/Loogle and grep queries in the new
definition node. They found no existing symmetric-operad approximation or
restriction declaration. The online HA PDF was opened and searched at the
source places above. Existing project declarations for enhanced diagrams,
infinity fibrations, isofibrations, monoidal mapping graphs, and the LM example
were read and reused. The later maintainer return identified an operad duplicate;
the repair described below removes it and reuses the landed interface.

This section records the original second reading before the maintainer return.
The current repair awaits the separate second reader required by the dispatcher.
The mathematical statement is unchanged; the encoding now reuses the landed base
and operad predicate instead of declaring its own. The copied node's `lean.statement` is verbatim the theorem signature.
Both `SymmetricOperadicApproximation.lean` and
`OperadicApproximationRestriction.lean` compile separately through `scompile.py`
with no errors or warnings; the only postponed proof is the named item theorem.

## Second reading by Q21

I read the copied node, its source place, the two delivered modules, and every
recorded statement dependency. The item statement is unchanged and the copied
`lean.statement` is verbatim the theorem signature.

The object and hypothesis list is:

- `C`, `P`, and `E` are quasicategories, all in the displayed simplicial-set
  universe; `p : P ⟶ finStarBase`, `f : C ⟶ P`, and `r : E ⟶ P` are the three maps.
- `hp : IsSymmetricInfinityOperad p` supplies the inner-fibration operad, inert
  cocartesian lifts, fibre Segal/tuple condition, and mapping-space product
  condition. `finStarBase`, inert/active pointed maps, and inert edges are the
  recorded declarations from `RelativeSymmetricOperadicAlgebras`.
- `hf : IsOperadicApproximation p f` is the source's factorization through an
  actual quasicategory `D`, a categorical equivalence `e : C ⟶ D`, and an
  isofibration approximation `g : D ⟶ P` with `e ≫ g = f`. Its first clause
  quantifies every object, arity, and `Fin n` projection and asks for the exact
  locally cocartesian edge with inert image; its second clause asks for the exact
  cartesian lift of every active edge ending at the chosen target.
- `hcolour : IsFunctorEquivalence (operadicColourMap p f)` is the strict unary
  colour-fibre equivalence of the original `f`, not of a chosen replacement.
- `hr : IsSymmetricOperadicFibration p r` is the categorical/isofibration,
  inert-lifting, fibre-Segal, and output mapping-product package. It adds no
  active lifting, presentability, limit, or colimit assumption.
- The conclusion is the specified `IsFunctorEquivalence` of
  `operadicSectionRestriction p r f`, followed by the explicit target-map and
  commuting-base-triangle naturality equalities. The maps are degreewise
  precomposition/postcomposition and retain every parameter simplex, so all
  noninvertible transformations and higher simplices remain present.

The Lean rendering matches each item: `operadicSections` is the intersection of
`relativeOperadicDiagramComplex` with the full inert-preserving subcomplex;
`operadicSectionRestriction` is actual precomposition by `f`;
`operadicSectionPostcompose` and `operadicLiftRestriction` are the displayed
degreewise maps. No existentially chosen inverse, transport, or section occurs.
The source is Higher Algebra (2017), Definition the project server (printed p. 260),
Definition the project server and Theorem the project server (printed pp. 268--269). The source
definition and theorem were checked against the online PDF; the two approximation
clauses and unary-fibre hypothesis agree exactly.

Edge cases checked: `n = 0` gives genuine empty `Fin 0` projection/product
conditions; `n = 1` retains the unary colour map; nullary active maps and inert
maps to the zero pointed set are included; empty fibres and empty simplicial sets
are not assumed inhabited; `f = 𝟙 P` is allowed; all simplicial degrees and
parameter higher simplices satisfy the base equation; arbitrary common universe
`u` is retained without an equality between independent site universes.

Searches were repeated with `rg` over the shared `lean/Sheaf`, the slopmaster2
`WeilConjectures`, Mathlib-name records, and `dag/lean_names_upstream.json`, and
with `msearch.py` LeanFinder/Loogle queries for operadic approximation,
restriction, and inert-preserving section equivalences. No existing declaration
matches the item. The new prerequisite node and module were read as stage-1
definitions; all data are real constructions or predicates, with no hollow
definition. The previously returned duplicate `IsSymmetricInfinityOperad` was
confirmed removed and the existing declaration from
`RelativeSymmetricOperadicAlgebras` is imported and reused.

No mathematical mismatch was found in this second reading, so no statement,
dependency, or Lean declaration was changed. Both modules compile cleanly via
the required `scompile.py` wrapper; the only remaining `sorry` is the named item
theorem.

Second-reader validation: `deliver2.py --no-push` printed `OK (dry run)` for
commit `7f2acc1c11`: preflight passed and both delivered modules compiled cleanly.

## Repair of return L (immutable head 7750ab8a6d94)

The saved packet was inspected and its required initial `deliver2.py --no-push`
was started before editing. The concrete return identifies a duplicate
`SSet.Enhanced.IsSymmetricInfinityOperad`, also declared in
`Sheaf.CategoryTheory.RelativeSymmetricOperadicAlgebras`. The current shared
source and its DAG record were compared with the saved declarations. The two
are encodings of the same HA notion; neither is retained under a new name.

The repair deletes the packet's `IsSymmetricInfinityOperad` and imports the
existing declaration. It also deletes its duplicate finite-pointed-set category,
inert/active predicates, projection/base/vertex/edge constructors, inert operadic
edge predicate, diagram decoder and whole-simplex over-diagram construction.
All uses now refer directly to `FinStar`, `finStarBase`, `finStarVertex`,
`finStarEdge`, `finStarRho`, `IsSymmetricInertEdge`, `IsActiveEdge`,
`operadicDiagram` and `relativeOperadicDiagramComplex`. The original Option
skeleton is replaced throughout by the imported zero-based Fin skeleton.
No transport equivalence between competing encodings needs to be chosen.

The item gains the landed definition node in `stmt_deps`, as authorized by
coord/delivery-errors.md H2's landed-node update. The new definition node also
cites it, and its declaration inventory no longer lists the deleted names.
The natural-language item statement, all original hypotheses and conclusions,
and proof plan are unchanged. Arity zero, unary fibres, active nullary maps,
empty colour fibres and identity restriction still have their original scope.
The target fibration continues to use the relative Segal predicates, since
they concern a general operadic base rather than the absolute pointed-set base.

Repair searches: `rg` over shared `lean/Sheaf`, the slopmaster2
`WeilConjectures` tree and `dag/lean_names_upstream.json` for the remaining
approximation and relative-fibration names found no other definitions. The
landed relative-operadic-algebra source was read through its full operad
predicate, inert/active predicates, diagram complex and decoder. The archived
three-kind search records remain in the new node as historical search evidence.
Both repaired modules compile separately through `scompile.py` without errors
or warnings. The final delivery dry run is recorded after it completes.
