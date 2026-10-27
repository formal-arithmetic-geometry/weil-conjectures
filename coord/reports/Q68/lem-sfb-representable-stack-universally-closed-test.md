## Worker report

The module `Sheaf.AlgebraicGeometry.RepresentableStackUniversallyClosedTest` states
`CategoryTheory.representable_stack_universally_closed_test`, together with
`space_stack_universally_closed_iff` and `space_scheme_tests_universally_closed_iff`.
These three theorems render all clauses of the assigned node. Each proof is `sorry`;
there are no definitions and no mathematical claims proved in this delivery.

Sources read: `literature/stacks-project/stacks-morphisms.tex`,
`lemma-characterize-representable-universally-closed` (Tag 0512),
`definition-closed`, and `lemma-universally-closed-local` (Tag 0CL3);
`spaces-morphisms.tex`, `lemma-characterize-representable-universally-closed`
(Tag 03XD) and `definition-closed`. The node correctly uses arbitrary algebraic-space
base changes rather than requiring these maps to be representable by schemes.
No source error or statement correction was needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base scheme S is `{S : Scheme.{u}}`; schemes over S are `Over S`.
- Stacks and their actual morphisms are `BasedCategory (Over S)` and `BasedFunctor`.
  The source and target are F and G, with independently bound object/morphism universes.
- The DM assumptions are `hF : IsDeligneMumfordModuliStack F` and the analogous hG.
- The specified morphism is `f : BasedFunctor F G`; representability by algebraic spaces
  is `hf : IsRepresentableByAlgebraicSpaces f`.
- Condition (a) is the first side of the main iff: for every Z with
  `IsAlgebraicModuliStack Z` and every `z : BasedFunctor Z G`, the canonical first
  projection of `moduliTwoFiberProduct z f` has closed point map, expressed by
  `IsClosedMap (moduliPointMap (moduliTwoFiberFst z f))`.
- The topology is the existing `moduliPointTopologicalSpace`: it is detected on smooth
  surjective scheme atlases, without choosing an arbitrary topology. `ModuliPoints`
  and `moduliPointMap` use field-valued objects modulo field-extension arrows.
- Condition (b) is the second side: every scheme T and every t into G, every space E
  and every projection a satisfying `HasSpaceBaseChange f T t E a` have the specified
  universal closedness. The latter is expanded as every algebraic space W, every map
  `b : W.obj.obj ⟶ yoneda.obj T`, and
  `IsClosedMap (AlgebraicSpace.mapPoint (pullback.snd a b))`.
  This is the ordinary sheaf pullback with its actual projection to W. All presentations
  are quantified, rather than an unrelated map or a selected Nonempty witness.
  The hypothesis hf guarantees presentations exist for every T,t, so this implication
  is not vacuous; equivalences over T make its value independent of presentation.
- The point spaces on this side are the existing `AlgebraicSpace.Point` with
  `pointTopologicalSpace`, the field-equivalence quotient and etale-atlas topology.
- The final clause for algebraic spaces is rendered explicitly by the two additional
  theorems. For X,Y spaces and their actual map f, the all-stack condition for
  `discreteModuliMap f.hom.hom` is equivalent to closedness of the ordinary projection
  `pullback.snd f.hom.hom b.hom.hom` after every algebraic-space base change W → Y.
  The third theorem gives the same comparison for condition (b), including all its
  scheme and space tests. No representability-by-schemes assumption is imposed.
- An algebraic stack is exactly the existing `IsAlgebraicModuliStack`: etale stack
  descent, representable algebraic-space diagonal and a smooth surjective scheme atlas.
  No finite type, separation, quasi-compactness or relative smoothness is assumed on f.

Universes and edge cases: arbitrary stack tests have hom universe at least u and object
universe at least u+1 (`max` with the free stack universe parameters). Thus scheme and
algebraic-space test categories are included, and arbitrarily larger stack universes
are still available by instantiating those parameters. There is no universe equality
between source, target or test stacks. All field and scheme tests use the established
scheme universe u. The empty scheme, empty space, empty stack and empty closed subset
are included; there is no Nonempty or inhabited hypothesis. Identity maps, arbitrary
characteristic, nonreduced bases, non-quasi-compact spaces and nonrepresentable-by-schemes
space maps remain covered. IsClosedMap tests every closed subset, not just the image of
the whole source. The point lifting proof in the docstring uses surjectivity onto the
set-theoretic fibre product, never an incorrect bijective identification of point spaces.

Dependency declarations used (their definitions, signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `IsDeligneMumfordModuliStack`, `IsRepresentableByAlgebraicSpaces`,
  `HasSpaceBaseChange`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`,
  `discreteModuli`, `discreteModuliMap` (all in CategoryTheory).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`.
- `Mathlib.Algebra.Field.Defs`: `Field`, through the existing point construction.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, as used in
  the existing smooth-atlas predicate; also checked SmoothOfRelativeDimension and Etale.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliPoints`, `moduliPointMap`.
- `Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen`:
  `moduliPointTopologicalSpace` and its actual residue-field atlas maps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.mapPoint`.

The last five owning definition nodes are already landed and are added to stmt_deps as
per brief-stage2 §5. The main statement text, proof, proof_deps and all other node fields
are preserved. No new nodes or dependency repairs are needed. The four proof-only
imports are the recorded modules for stack chartwise calculus, space fibre products,
stack point topology and algebraic-stack fibre products. Their proof roles are explained
step-by-step in the docstrings, following every step of the node's proof.

Searches actually run on 2026-10-24:

- msearch.py leanfinder: "Representable algebraic stack morphism is universally closed
  if and only if every scheme base change is universally closed". Eight hits, all for
  schemes, including `universallyClosed_iff`; no stack equivalence or space compatibility.
- msearch.py loogle: `"UniversallyClosed", "IsClosedMap"`. One hit,
  `AlgebraicGeometry.UniversallyClosed.universally_isClosedMap`, for schemes only.
- msearch.py grep: `AlgebraicStack|DeligneMumford|universallyClosed` in AlgebraicGeometry.
  The printed 25 hits concern schemes; no match for the assigned statement.
- rg in `lean/WeilConjectures/AlgebraicGeometry` for universal closedness and the item id:
  only scheme results, no occurrence of this item. rg in `lean/Sheaf/AlgebraicGeometry`
  found the already existing point-map and topology definitions listed above, which are
  reused. The existing MapToSchemeIsUniversallyClosed only tests schemes, and
  IsUniversallyClosedModuliMap also tests schemes; neither states the required equivalence
  or expanded all-space tests. They were not redefined.
- rg of `dag/lean_names_upstream.json`, `lean/WeilConjectures` and `lean/Sheaf` for the
  proposed declaration names found none. DAG searches identified the five landed owning
  definition nodes, so no duplicate definition node was introduced.

Validation: prescribed scompile.py compiled the sandbox module and the library-named
module cleanly (6.0 s and 5.9 s), with no errors or warnings. All variables and universes
are explicitly bound and autoImplicit is false. Every theorem has only a sorry proof.
No STATEMENT-DISPUTED flag or unresolved node fault.

## Second reading by Q68

This is a direct self-rereading, not an independent subagent review: the dispatcher brief
forbids starting agents and says the maintainer independently reviews this delivery.
I reopened the finished module and compared its three signatures to the node and the
Stacks definitions. In the main theorem the source and target have exactly the two DM
hypotheses and f has exactly representability by spaces. Its left side tests all algebraic
stacks, not merely DM stacks; its right side quantifies every scheme map and every
presentation of its actual 2-pullback, then every algebraic-space base change and all
closed subsets through IsClosedMap. The projection is pullback.snd a b, hence targets W,
not T. HasSpaceBaseChange includes the projection comparison, ruling out an unrelated
space map; hf supplies its existence. In the two compatibility signatures X,Y are
actual algebraic spaces, the map is the actual natural transformation f.hom.hom, and
the ordinary side tests pullback.snd f.hom.hom b.hom.hom for every W → Y with the
existing space topology. Thus both (a) and (b) are explicitly equivalent to ordinary
universal closedness. The max universes include discrete scheme/space groupoids and
allow larger tests; all empty cases remain. No mismatch was found and no statement
correction or weakening was made. The node's proof steps 1--4 are recorded in the main
docstring and step 5 in both compatibility docstrings. The three signatures and the
full declaration names agree with lean.declarations; the lean.statement is the main
signature copied verbatim. All added dependency ids own definitions actually used.

Dry run: deliver2.py --no-push printed OK, with commit 25d0ca8016b passing the
server preflight and compilation. The staged packet consists exactly of the item JSON,
its Lean module and this report.
