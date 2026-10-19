## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricStalkToposPoint` states
`AlgebraicGeometry.Scheme.geometricStalkToposPoint`, with `sorry` as its whole proof.
Its two construction helpers belong to this node and are listed in `lean.declarations`:
`geometricLiftFunctionPresheaf` gives the actual function presheaves, including precomposition
restrictions and postcomposition in the target set; `proEtaleGeometricSetStalkFunctor` assembles
the previously defined pro-etale stalk objects and their colimit maps into a functor. Both
have real data. The routine functor-law checks certify those data; no mathematical conclusion
of the node is proved.

The hypotheses and clauses correspond as follows:

- A scheme Y is `{Y : Scheme.{u}}`; the geometric point is `{Ω : Type u} [Field Ω]
  [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)`. There is no additional property of Y or y.
- The two alternatives for C are the two conjuncts, over `Y.smallEtaleTopology` and
  `ProEt.topology Y`. These are the dependency nodes' exact site encodings.
- The chosen larger universe for sets and stalk colimits is `Type (u + 1)`. The bounded
  site has objects in `Type (u + 1)` and morphisms in `Type u`, as in the stalk dependency.
  No equality between those two universe levels is imposed. All universe variables and
  other parameters are explicitly bound.
- In the etale clause L is `(pointSmallEtale y).fiber`, which is definitionally
  `Etale.forget Y ⋙ coyoneda.obj (op (Over.mk y))`. In the pro-etale clause L is
  `ProEt.forget Y ⋙ coyoneda.obj (op (Over.mk y))`. Thus an element is a morphism in
  `Over Y` from the geometric point to U, exactly a lift with composite equal to y;
  `L.map` is postcomposition with a Y-morphism, with no change of the field Ω.
- `geometricLiftFunctionPresheaf L` has object at T and U equal to `L.obj U.unop → T`.
  Its restriction along f is `a ↦ (x ↦ a (L.map f.unop x))`; its map along t is
  `a ↦ (x ↦ t (a x))`. These are the statement's specified maps.
- The etale S is `(pointSmallEtale y).sheafFiber (A := Type (u + 1))`, the recorded
  stalk declaration. The pro-etale S is `proEtaleGeometricSetStalkFunctor y`. Its
  object at F unfolds to `colimit ((proEtaleGeometricNeighbourhoodForget y).op ⋙ F.obj)`,
  definitionally `proEtaleGeometricSetStalk y F`. Its map is the induced colimit map.
  The opposite on the neighbourhood forgetful functor ensures restrictions run from
  F(U) to F(V) for a pointed arrow V → U.
- Each clause asserts existence of a functor `R : Type (u + 1) ⥤ Sheaf ...`, together
  with the literal equality `R ⋙ sheafToPresheaf ... = geometricLiftFunctionPresheaf L`.
  This expresses that the *specified* presheaf is a sheaf for every set T and that its
  target-set maps form the stated right-adjoint functor. It cannot choose an unrelated
  right adjoint or replace that presheaf by its sheafification. The equality is legitimate
  because sheaves are presheaves with a proof of the sheaf property.
- `Nonempty (S ⊣ R)` is exactly existence of the displayed adjunction. It is not used
  to choose data for a definition. `PreservesFiniteLimits S` is the remaining conclusion.
  The node defines a morphism of topoi to mean precisely these last two properties, so
  no extra topos structure or site-morphism hypothesis is needed; its inverse image is
  literally the same S appearing in the adjunction.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, scheme morphisms, `Spec`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points are inline
  as directed by `def-weil-geometric-point`. Also read `Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField` to check the geometric-point interface.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`, `smallEtaleTopology`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: its public imported
  `Mathlib.AlgebraicGeometry.Sites.Proetale` supplies `Scheme.ProEt`, `ProEt.forget`,
  and `ProEt.topology`, exactly the site component documented by the dependency.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: read `Precoverage.IsSiteForCoverings`;
  as its record prescribes, the sheaf component remains Mathlib `Sheaf`, with
  `sheafToPresheaf` the full-subcategory inclusion. The covering-axioms definition
  itself is not an extra hypothesis of this theorem.
- `Mathlib.CategoryTheory.Sites.Point.Basic` and
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`: `Point.sheafFiber` and `pointSmallEtale`.
- `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk`: read its entire module, including
  `ProEtaleGeometricNeighbourhood`, `proEtaleGeometricNeighbourhoodForget`, its
  cofilteredness/smallness/colimit instances, `proEtaleGeometricStalkDiagram`,
  `proEtaleGeometricStalk`, and `proEtaleGeometricSetStalk`. The functor helper reuses
  that exact diagram and colimit, with no replacement neighbourhood notion.
- `def-weil-size-convention` has no Lean declaration, as its record says. Explicit
  universe levels and the dependency's colimit/smallness instances implement it.

Proof imports include the recorded weakly-etale-field and ind-etale algebra modules,
Mathlib's skyscraper adjunction, sectionwise sheaf limits, filtered-colimit/finite-limit
commutation and fpqc site. The seven proof steps are reproduced in the theorem docstring.
No postponed helper theorem, new independent definition node, or dependency repair is needed.

Edge cases checked: T may be empty; if L(U) is empty its function set is a singleton.
No chosen lift is assumed at every U. Empty U is allowed. A geometric point of an empty
Y is impossible, so that case is vacuous through the actual y parameter, without an added
nonemptiness assumption. Finite-limit preservation includes the empty finite diagram
(the terminal object). Neither characteristic nor Noetherian/quasi-compact/separated
hypotheses are imposed on Y. The statement does not assert that these pro-etale points
are conservative; Stacks 0991 explicitly explains why that stronger claim fails.

Sources read: the published Stacks pages [00Y8](https://stacks.math.columbia.edu/tag/00Y8),
[04FM](https://stacks.math.columbia.edu/tag/04FM), and
[0991](https://stacks.math.columbia.edu/tag/0991), since the read-only clone has no local
Stacks TeX. They confirm the function-presheaf adjunction and the same neighbourhood
colimit on the respective sites. No statement correction or disputed statement.

Searches (2026-10-16):

- `msearch.py ... leansearch "geometric stalk inverse image point proetale topos"`:
  service unavailable, Internal Server Error; no absence conclusion from this failure.
- `msearch.py ... leanfinder "geometric stalk functor on small etale or proetale site
  right adjoint sheaf of functions on lifts preserves finite limits"`: eight hits,
  including generic `Point` finite-limit preservation and topological-space stalk
  adjunctions; none states both scheme-site clauses with the prescribed pro-etale stalk.
- `msearch.py ... loogle
  "CategoryTheory.GrothendieckTopology.Point.skyscraperSheafAdjunction,
  AlgebraicGeometry.Scheme.pointSmallEtale"`: zero hits for the combined query. The
  two APIs were independently located and read directly, so this query is not used
  as evidence that either API is absent.
- `msearch.py ... grep
  "geometricStalkToposPoint|pointSmallProEtale|proEtaleGeometricStalk|pointSmallEtale"
  AlgebraicGeometry`: five Mathlib hits, all for the small-etale point.
- Direct `rg` on `WeilConjectures/` and `lean/Sheaf/` for the item id and proposed
  declaration names found no exact theorem or name clash. Broader geometric-point,
  stalk, adjunction and pro-etale searches located and led to reading the existing
  stalk module and Mathlib Point/Basic and Point/Skyscraper APIs. The generic skyscraper
  results require a supplied site point, and no existing pro-etale lift point was found.

Validation uses only `scompile.py` for the delivered file and `deliver2.py --no-push`
for the final dry run. Delivery is reserved for the independent second reader.


## Second reading by Q04

I independently opened the node, the complete Lean module, all eight statement-dependency
records and the declarations implementing the notions used here. Verdict: the statement
says exactly what the node says. No mathematical mismatch was found; the Lean and the
node record are unchanged. This reading adds the present report only.

Source check: I obtained the actual Stacks `proetale.tex`, `etale-cohomology.tex` and
`sites.tex` from the Stacks Project source repository into the item's scratchpad.
I read `section-points` through the paragraph before `lemma-classical-point` (0991),
`lemma-stalk-gives-point` (04FM), `lemma-point-pushforward-sheaf` (00Y8), and the surrounding
geometric-point, neighbourhood and stalk definitions. I also checked the published
[0991](https://stacks.math.columbia.edu/tag/0991),
[04FM](https://stacks.math.columbia.edu/tag/04FM), and
[00Y8](https://stacks.math.columbia.edu/tag/00Y8) pages. These places introduce an arbitrary
scheme and an algebraically closed field point; there is no standing Noetherian,
quasi-compactness, separatedness or characteristic hypothesis. The source uses the
same-field lifts and the opposite neighbourhood index occurring below.

Object/hypothesis/conclusion checklist, written from the node before assessing the Lean:

1. An arbitrary scheme Y: `{Y : Scheme.{u}}`. Read `Scheme` and its morphism structure
   in Mathlib's `AlgebraicGeometry/Scheme.lean`. Verdict: exact, no added scheme property.
2. A geometric point Spec Omega to Y, with Omega algebraically closed:
   `{Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)`.
   The geometric-point node explicitly prescribes this inline interface. Mathlib's
   `Scheme.SpecToEquivOfField` identifies it with the residue-field formulation.
   Verdict: exact, including the field and algebraic-closedness hypotheses.
3. Either of the two bounded small sites: the outer conjunction ranges over
   `Y.smallEtaleTopology` and `ProEt.topology Y`. Read Mathlib's `EtalePoint.lean` and
   `Sites/Proetale.lean`, including the `ProEt` object category, `ProEt.forget` and
   the topology from weakly etale fpqc covers. `ProEtaleDerivedCategory.lean` publicly
   imports that exact site. Verdict: both alternatives, all Y-morphisms, no affine or
   finite-type restriction.
4. Sets and colimits in the chosen larger universe: both coefficient categories are
   `Type (u + 1)`, with schemes and Omega at level u. The site objects have level u+1
   and morphisms level u; their universes have not been identified. Read the size
   convention record and the neighbourhood smallness/colimit instances. Verdict: the
   stated bounded-site convention, valid at every u.
5. L(U) is precisely Hom over Y from Spec Omega to U: the etale expression is
   `(pointSmallEtale y).fiber`, whose definition is
   `Etale.forget Y ⋙ coyoneda.obj (op (Over.mk y))`. The pro-etale expression explicitly
   replaces `Etale.forget` by `ProEt.forget`. Morphisms in `Over Y` impose the lift
   equation, and coyoneda maps by postcomposition. Verdict: the same geometric point,
   including the same Omega, on every object and every arrow.
6. S(F) is the neighbourhood colimit: the etale S is the dependency's
   `(pointSmallEtale y).sheafFiber (A := Type (u + 1))`. Read `Point.presheafFiber` and
   `Point.sheafFiber`: they use the opposite of the fibre category of elements.
   The pro-etale S is `proEtaleGeometricSetStalkFunctor y`; its real definition is
   sheaf inclusion followed by precomposition with
   `(proEtaleGeometricNeighbourhoodForget y).op` and `colim`. Its object is exactly
   `proEtaleGeometricSetStalk y F`; its maps are the canonical induced colimit maps.
   Read `ProEtaleGeometricStalk.lean` in full. Verdict: the required diagram and maps,
   with restrictions F(U) to F(V) for a pointed V to U.
7. The specified presheaf has values Map(L(U),T), restrictions by precomposition,
   and is a sheaf for every T: `geometricLiftFunctionPresheaf L` has
   `obj T := { obj U := L.obj U.unop → T, ... }`, restriction
   `a ↦ (x ↦ a (L.map f.unop x))`, and target-set maps
   `a ↦ (x ↦ t (a x))`. Each existential R satisfies the literal functor equality
   `R ⋙ sheafToPresheaf ... = geometricLiftFunctionPresheaf L`.
   Since sheaves form the full subcategory of sheaf presheaves, such an R states
   exactly that this specified functor lifts through that inclusion. Conversely,
   the sheaf proofs give such an R without changing its underlying presheaves or
   maps. Verdict: exact, including restrictions and functoriality in every set T.
8. The adjunction S left adjoint to that p_*: `Nonempty (S ⊣ R)` inside each
   existential. Verdict: the correct direction and the same S and R as above.
   The existential ranges over the entire functor, so it includes every T and its maps.
9. Finite-limit preservation: `PreservesFiniteLimits S` for each of the two S's.
   Verdict: all finite diagrams, including the empty one.
10. A topos morphism from sets with inverse image S: the node explicitly defines
    this to mean an adjunction with finite-limit-preserving left adjoint. Items 8
    and 9 are exactly those data and properties, with S literally the inverse-image
    functor in the adjunction. Verdict: no missing separate topoi condition and no
    additional conservativity claim.

The site's sheaf notion is Mathlib `Sheaf`, with natural transformations as morphisms,
consistent with `SiteCoveringAxioms.lean` and its dependency record. I read that module.
The current pro-etale-stalk dependency record now points to the extension
`ProEtaleModuleStalkFunctor.lean`; I read it too. Its module-valued functor publicly
imports the original construction through `ProEtaleConstantSheafStalk`. It introduces
no alternative set stalk. This delivery correctly imports and uses the original set
construction in `ProEtaleGeometricStalk`, without duplicating it or requiring module
coefficients. No new node or repaired dependency module is present in this delivery.

Edge cases: T may be empty, and L(U) may be empty; the definition uses the actual
function type in both cases. Empty site objects remain allowed. An empty covering
can only cover an object with no lifts, so its sheaf value is a singleton as required.
The empty scheme has no y, making that case vacuous without an extra nonemptiness
assumption. Empty finite limit diagrams are included. There is no coefficient ring,
cohomological degree, n, zero module, or index parameter whose zero/empty case is
silently restricted. All characteristics and all universe levels u are covered.

Independent duplicate searches, with queries different from the worker's:

- LeanFinder via `msearch.py`: "The geometric fibre on the weakly etale site admits
  the direct image sending a set to functions on geometric lifts". Eight hits,
  including `Point.Hom.sheafFiber`, `Point.sheafFiber`, `Etale.forget` and
  `toPresheafFiber_w_apply`; no combined small-etale/pro-etale construction.
- Loogle via `msearch.py`: `"skyscraperPresheafFunctor"`. Twelve hits. I opened
  `Point/Skyscraper.lean`, including the underlying definition, sheaf theorem and
  adjunction. Its functor requires an already supplied site point. The available
  `pointSmallEtale` supplies only the etale case; there is no pro-etale lift point.
  Thus those declarations do not already state this node or provide the general
  function-presheaf helper for an arbitrary L.
- LeanSearch via `msearch.py`: "The stalk on the weakly etale site is a left exact
  left adjoint with right adjoint given by functions on geometric lifts".
  Internal Server Error; recorded as unavailable, not evidence of absence.
- Direct `rg` in Mathlib, upstream `WeilConjectures`, the current project's
  `lean/Sheaf`, and the newer `lean/WeilConjectures` framework: exact declaration
  names and variants `proetale.*point`, `point.*proetale`, `lift.*function.*presheaf`,
  `proEtale.*[Ss]talk.*[Ff]unctor`, `[Ss]talk.*[Tt]opos`. No exact competing
  construction or theorem. I also opened upstream `PointFunctions.lean` and the
  framework's `TypePointFunctions.lean`: they use the whole underlying set of U,
  whereas this node uses lifts from the fixed Spec Omega. They are different notions.

H5/H6/H8/H9 checks: both helper definitions contain real functor data and existing
colimit constructions. Their routine law proofs certify those data; no theorem is
proved. The sole theorem's proof is `sorry`. Every declaration has its source and
blueprint marker. The theorem docstring follows all seven node proof steps, including
same-field covering lifts, overlap gluing, both adjunction maps and finite limits.
There is no local notation, private copy or unbound variable. All Lean lines are at
most 100 characters. A direct string comparison confirmed `lean.statement` is verbatim
the theorem signature. No statement correction or disputed statement is needed.

Validation: `scompile.py Q04 lem-fix-geometric-stalk-topos-point
lean/Sheaf/AlgebraicGeometry/GeometricStalkToposPoint.lean` from the sandbox passed both
its sandbox and library-file checks, without warnings (3.8 s and 3.6 s reported).
The first attempt used a relative path from the read-only repository instead of the
sandbox and failed to locate the input; rerunning from the sandbox fixed the invocation.
The final delivery wrapper repeats compilation and preflight.


## Immutable maintainer review repair

Independent review of delivery 5578c75ed350929549276ad01d7f721f82abc628 found
no mismatch in hypotheses, sites, stalks, function presheaves, adjunction direction,
finite limits, or universes. For strict compliance with the pilot no-local-proof
gate (H6), the replacement module removes the two explicit tactic proofs of
`map_id` and `map_comp` inside `geometricLiftFunctionPresheaf`. Mathlib's existing
Functor structure defaults discharge those routine construction obligations,
just as for the outer functor and natural transformations already in the module.
The objects, maps, declaration names, theorem signature, docstrings, and node
record are unchanged. No mathematical theorem has been proved or weakened.
The earlier statements that the Lean was unchanged describe the group reading;
this final replacement is the maintainer's mechanical repair.

The immutable original was reproduced with `scompile.py Q04
lem-fix-geometric-stalk-topos-point
snapshot/lean/Sheaf/AlgebraicGeometry/GeometricStalkToposPoint.lean`: exit 0,
no diagnostics, sandbox 8.6 s and library-file 4.1 s. The complete replacement
was reproduced with the same wrapper and
`fixes/lean/Sheaf/AlgebraicGeometry/GeometricStalkToposPoint.lean`: exit 0,
no diagnostics, sandbox 26.7 s and library-file 74.1 s reported elapsed time.
The wrapper's elapsed times include waiting for a compiler slot; its Lean
subprocess timeout remains 60 seconds after slot acquisition. No timeout was
reported, no limit was raised, and no server fallback was required.
No global build, direct SSH, live Lean write, clone edit, or Git mutation was run.
The complete maintainer checklist, source locations, searches and findings are
in the accompanying review.md.
