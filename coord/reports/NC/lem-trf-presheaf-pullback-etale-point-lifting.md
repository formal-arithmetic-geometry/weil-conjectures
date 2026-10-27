## Worker report

Module: `Sheaf.AlgebraicGeometry.PresheafPullbackEtalePointLifting`.
Main declaration: `AlgebraicGeometry.AlgebraicSpace.presheafPullback_etale_point_lifting`.
This states the entire node with one postponed theorem. The returned theorem signature
is unchanged. Maintenance commit `13dcc879ed57f40510112dfe29082edac34a38ac` installed
the required definition owner and the diagonal-module re-export on `sheaf-dag`.
This delivery now adds only the item statement and this report. The retained
prerequisite files match the base exactly and introduce no companion changes.

Hypotheses and objects, clause by clause:

- The base scheme is `{S : Scheme.{u}}`. `I : Type w` is an arbitrary index type,
  without a nonemptiness or finiteness assumption.
- `G H` and `Hᵢ i` have type `Sheaf (Scheme.fppfTopology.over S) (Type u)`,
  exactly set-valued sheaves on the big fppf site. Morphisms `g` and `h i` are
  natural transformations of their underlying presheaves, as required.
- `he : ∀ i, IsEtale (h i)` is the recorded scheme-test definition, which already
  includes representability. There are no algebraic-space, diagonal, atlas,
  quasi-compactness, or separation hypotheses on these arbitrary sheaves.
- The pointwise presheaf P_i is `(sheafPullbackCone g (h i)).pt`; its object value
  is definitionally `Types.PullbackObj (g.app T) ((h i).app T)`, namely
  `{p : G(T) × H_i(T) // g(p.1) = h_i(p.2)}`. The helper's construction uses
  `PullbackCone.combine` on explicit type pullbacks, so restriction is componentwise.
  Its `fst` is exactly the specified projection π_i. This existing helper is reused,
  not redefined. The first conjunct states its sheaf condition.
- For each i, T and `t : yoneda.obj T ⟶ G.obj`, the next conjunct supplies an
  isomorphism from the pointwise test pullback to the pointwise pullback along
  `t ≫ g`. Its two projection equations fix its forward map to `(a,(x,y)) ↦ (a,y)`.
  Since the isomorphism has an inverse and `x=t(a)`, the inverse is necessarily
  `(a,y) ↦ (a,(t(a),y))`. Thus this is the canonical isomorphism, not an arbitrary
  unidentified isomorphism. Each object is a combined explicit type pullback.
- In the same conjunct `∃ U p q, IsPullback q (yoneda.map p) (h i) (t ≫ g) ∧
  Etale p.left` says the right side is represented by a scheme over T with étale
  projection, exactly as in `IsRepresentableWith` from the dependency. The square
  is in presheaves; the factors and the compatible-pair pullback are sheaves.
- The third conjunct states `∀ i, IsEtale (sheafPullbackCone g (h i)).fst`,
  precisely representable étaleness of the base-changed family.
- The fourth conjunct takes an arbitrary representing isomorphism
  `G.obj ≅ yoneda.obj T` and supplies a representing scheme U for each P_i.
  This covers the literal representable G=h_T case and its invariant formulation.
- The final implication assumes `IsJointlySurjective h`, exactly the recorded
  field-extension lifting predicate, and states all the subsequent clauses.
- For every field `K : Type u`, `s : Spec K ⟶ S`, and section x of G at that
  S-scheme, it supplies i, a field M, a unital field homomorphism `e : K →+* M`
  (automatically injective), and a section y of H_i at `Spec M` with structural
  map `Spec.map e ≫ s`. The equation `(h i).app _ y = H.obj.map ... (g.app _ x)`
  is exactly h_i(y)=g(x)|_M.
- It then supplies an actual compatible-pair section p, with
  `p.val = (G.obj.map ... x, y)` and `fst.app _ p = G.obj.map ... x`.
  These state membership of the specified pair in P_i and its projection formula.
- The next conjunct is joint surjectivity of the pulled-back first projections.
- Finally `IsEmpty I → ∀ K [Field K] s, IsEmpty (G.obj.obj (op (Over.mk s)))`
  explicitly states the empty-family consequence, with no extra field-point
  existence assumption on S.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms,
  `Over S`, Spec and its contravariant map on commutative ring homomorphisms.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over`:
  `GrothendieckTopology.over` (all exported through the statement imports).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `IsRepresentableWith`, `IsEtale`;
  these supply the exact scheme-test convention of def-trf-algebraic-space.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`: `IsJointlySurjective`;
  this is used directly in both hypothesis and conclusion, with identical test
  and extension-field universes.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the dependency module retained
  transitively by AlgebraicSpace and SheafPullbackDiagonal; sheaves themselves
  retain Mathlib `Sheaf` and `Presheaf.IsSheaf`, as its node's record specifies.
- Mathlib `Field`, from `Mathlib.Algebra.Field.Defs`, represents def-weil-field.
- `Sheaf.AlgebraicGeometry.SheafPullbackCone`: `sheafPullbackCone`, the literal
  compatible-pair construction, now owned by def-trf-sheaf-pullback-cone. The item
  cites this new definition node instead of lem-trf-sheaf-pullback-diagonal. The
  item imports the definition module directly; no diagonal theorem is imported.

Edge cases checked: I empty forces H to have no field-valued points and therefore
G has none; the same statement remains valid for an empty base scheme. No
`Nonempty I`, inhabited scheme, or chosen field point is required. If h_i is an
identity, the compatible-pair presheaf is G and the projection is an isomorphism.
For g an identity, the comparison removes a redundant equal coordinate. If G is
representable, the identity test gives the required representing scheme.
For H terminal, the presheaf is the ordinary pointwise product. Empty covers glue
uniquely using the sheaf condition, so the sheaf assertion still holds.
All schemes and fields have the universe of the dependency's big site; w is
independent and imposes no size restriction on the index family.

Searches (2026-10-22):

- msearch.py LeanFinder, query "Base change of representable etale maps of sheaves
  and jointly surjective families on field valued points": eight scheme étale
  permanence/site hits, including IsEtale.instIsStableUnderBaseChangeScheme;
  no full statement match.
- msearch.py Loogle, query `CategoryTheory.Functor.relativelyRepresentable`:
  twelve relative representability declarations. Generic base-change stability
  lacks this node's complete scheme-test identification and explicit field lift.
- msearch.py grep, query `pullbackObj|pullback.*IsSheaf|isSheaf.*pullback`, restricted
  to Mathlib/CategoryTheory: 25 hits, chiefly unrelated fibered-category and
  chosen-pullback constructions. Direct source reading identified Mathlib's
  explicit Types.PullbackObj, pullbackCone, pullbackLimitCone and
  PullbackCone.combine; no second definitions were introduced.
- msearch.py LeanSearch, query "Representable etale natural transformations of
  sheaves are stable under pullback with field extension lifts of point classes":
  eight hits, including relative representability base-change and scheme étale
  base-change. None states all the requested clauses.
- rg over lean/WeilConjectures for `IsJointlySurjective|IsRepresentableWith` and
  the item id: no exact statement. Broader `PullbackCone.combine` search gives
  scheme-limit constructions, not this set-valued sheaf-family theorem.
- rg over lean/Sheaf found PresheafFieldLiftFamilyCalculus (only the field-lifting
  clause), AlgebraicSpaceFibreProductsEtaleCovers (requires algebraic spaces,
  omits explicit scheme-test comparison), and SheafPullbackDiagonal. The last
  supplies exactly the needed compatible-pair helper, which is reused.
- The node source was read locally: spaces-topologies.tex lemma-etale (041F)(3),
  spaces-properties.tex definition-points (03BU) and lemma-points-cartesian (03H4).
  The five proof steps in the node are included in the theorem docstring.

No mathematical statement correction or disputed statement. The H2/C5 definition
ownership repair is already on the base, as detailed below.

## Definition ownership repaired on the base

`def-trf-sheaf-pullback-cone` owns module
`Sheaf.AlgebraicGeometry.SheafPullbackCone` and declaration
`AlgebraicGeometry.AlgebraicSpace.sheafPullbackCone`. It introduces the explicit
compatible-pair pullback cone for arbitrary presheaves on schemes over S. The base
scheme is `{S : Scheme.{u}}`; the three presheaves are
`{F G H : (Over S)ᵒᵖ ⥤ Type u}`; the two natural transformations are
`(f : F ⟶ H) (g : G ⟶ H)`; the resulting `PullbackCone f g` has the stated
vertex, componentwise restrictions and projections. Its body is exactly the old
abbreviation: `PullbackCone.combine` of `Types.pullbackCone`, using the actual
`Types.pullbackLimitCone.isLimit` proofs. There is no new choice, postponed data,
sheaf condition or diagonal hypothesis. Source: Stacks spaces.tex, Tags 04T9 and
02X2, the explicit presheaf underlying their fibre products of sheaves. The node
cites def-pc-scheme and def-weil-pbc-sites-and-cohomology for schemes and the
presheaf/natural-transformation convention, imports their recorded modules, and
has the item's chapter, unit and computed blueprint ancestor/via.

Searches made during this repair (2026-10-22), also in the new node's
mathlib_searches, with the tools' output retained in searches.jsonl:

- LeanSearch via msearch.py: "The presheaf pullback of two natural transformations
  to a type valued functor has compatible pairs as sections with componentwise
  restriction". Eight hits concern restriction naturality, compatible families
  and topological pushforward/pullback, not the scheme-presheaf construction.
- Loogle via msearch.py: `CategoryTheory.Limits.PullbackCone.combine`. Five hits:
  combine, combineIsLimit and three formula lemmas. The generic construction is
  used directly, specialized to explicit type pullbacks; it does not separately
  name this scheme-presheaf compatible-pair cone.
- Mathlib grep via msearch.py: `def combine|abbrev sheafPullbackCone|def pullbackCone`
  in CategoryTheory. Seventeen hits include combine and generic pullback cones.
  Direct source reading of FunctorCategory/Shapes/Pullbacks.lean:34 and
  Types/Pullbacks.lean:33-57 confirms the exact data of the abbreviation.
- `rg -n sheafPullbackCone lean/Sheaf lean/WeilConjectures`: the sole existing
  definition is the abbreviation in SheafPullbackDiagonal. No upstream duplicate.
  `rg -l 'sheafPullbackCone|compatible.pair.*presheaf|pointwise.*pullback.*presheaf'
  dag/nodes`: theorem nodes and unrelated categorical notions, no definition owner.
  `tools/blueprint_refs.py search 'presheaf pullback'` returns the étale-sheaves
  node, not this definition. `ancestor` returns lem-trf-local-term-locality.
  Thus we move the existing abbreviation rather than adding a duplicate.

Edge cases for this definition: no field points, nonemptiness, sheaf property,
representability or diagonal hypothesis is used. An empty factor gives empty
compatible pairs; identity maps give the usual compatible-coordinate cone;
restriction laws and compatibility come from the real Mathlib constructions.
The universe and all binders are unchanged by extraction.

## Dependency repair already on the base

`lem-trf-sheaf-pullback-diagonal` has a maintenance ownership repair in
`Sheaf.AlgebraicGeometry.SheafPullbackDiagonal`. The previous lean.declarations
bundled `sheafPullbackCone` under this theorem node, but consumers need the plain
abbreviation without any theorem conclusion. The return explicitly requires moving
it into a definition owner and repairing this landed module to import/re-export it.
Accordingly the abbreviation is removed here and replaced by a `public import` of
SheafPullbackCone. The diagonal theorem signature, proof docstring and sorry proof
are unchanged; lean.declarations now lists only the theorem, and lean.note explains
the ownership repair. Maintenance also added the definition to the diagonal node's
statement dependencies.
The item cites the definition instead of the diagonal theorem. Both prerequisite
node copies and modules now match the repaired server base; no dependency record
is changed by this delivery.

## Second reading by NC

The dispatcher prohibits a separate agent. I performed the required second reading
in this thread with all three files and their nodes open. Independent maintainer
review remains required. The returned item signature is byte-identical, including
arbitrary sheaves and independent index universe w; the scheme-test comparison
is fixed over both factors; the representing square uses t ≫ g and Etale p.left;
the first projection is representable étale; representable G gives representable P;
the field lift supplies exactly the restricted pair and its projection; the final
two clauses are joint surjectivity and the empty-family consequence. No diagonal
hypothesis is inherited. The new node's explicit pair, restriction and both legs
match the moved abbreviation; the data body is byte-identical and contains no
sorry. The repaired diagonal module imports/re-exports this same declaration and
its own theorem signature is byte-identical to current main. Its mathematical
statement is unchanged; maintenance added its actual definition prerequisite. The ownership mismatch
identified in H2/C5 is repaired; the item no longer cites or imports the diagonal
theorem merely to access the abbreviation.

Validation after maintenance on 2026-10-23: the extracted abbreviation body and the
remaining diagonal theorem/docstring are byte-identical to their previous versions.
Affected DAG checks and import-prune checks pass. The definition and diagonal modules
compiled separately through `tools/lean_file.sh` with 60-second limits in 5.6 s and
7.3 s. The item compiled separately through the same tool in 6.1 s. The former prerequisite-closure/module-ownership failures
were historical: the extraction is now committed to the base, so this delivery no
longer asks to modify a companion theorem outside its prerequisite closure.

The standard `deliver2.py NC lem-trf-presheaf-pullback-etale-point-lifting --no-push`
then exited 0: `OK (dry run): commit d64ab1581ef passes the preflight and compiles;
nothing pushed`. Its staged set was exactly the item node, item module and report.
The prerequisite copies matched the base and were omitted automatically. The
maintenance task leaves delivery to the next stage-2 worker; retain this theorem
and run the normal delivery wrapper. No tool-policy exception is required.

Worker continuation, 2026-10-23: the required initial saved-packet dry run first
reported the historical prerequisite-closure/ownership failures. Maintenance
then landed the extraction on the current base. A second prescribed dry run
passed (commit d6011cd59dc), staging only the item node, item module and report.
Both prerequisite modules and node copies now match the current base exactly.
The item's signature remains verbatim, its only mathematical dependency change
is the definition owner, and its declaration date is refreshed to 2026-10-23.
Fresh scompile.py on all three retained modules exited 0 without errors or
unexpected warnings. Final checks passed for the exact item signature, single
theorem sorry, direct definition import and citation, explicit universes u/w,
JSON layout, 100-column bounds, and item-only lean/stmt_deps changes. Re-read
IsRepresentableWith, IsEtale and IsJointlySurjective: all scheme-test and
field-extension clauses still use those recorded definitions directly. No
mathematical statement changed and no unused diagonal theorem edge was added.
