## Worker report

This delivery states `AlgebraicGeometry.AlgebraicSpace.fppf_space_atlas_bootstrap` in
`Sheaf.AlgebraicGeometry.FppfSpaceAtlasBootstrap`. Its whole proof is `sorry`.
No definitions, dependency repairs, new nodes, or statement corrections are needed.
The assigned node's mathematical statement and dependency lists are unchanged.

Source checked: `literature/stacks-project/bootstrap.tex`, theorem-final-bootstrap,
Tag 04S6, condition (3), and its proof. Condition (3) assumes an fppf sheaf and an
algebraic-space atlas representable by algebraic spaces, surjective, flat, and locally
of finite presentation. It does not assume representability of the sheaf's diagonal.

Clause-by-clause rendering:

- The base scheme is `{S : Scheme.{u}}`. The explicitly declared universe `u` is the
  bound used by the recorded algebraic-space framework. `Over S` has schemes of
  universe `u`, morphisms in that same universe, and objects in `u+1`.
- The big fppf sheaf is `F : Sheaf (Scheme.fppfTopology.over S) (Type u)`.
  Mathlib's slice topology is precisely the recorded big fppf site over `S`.
- The algebraic space and sheaf morphism are `(U : AlgebraicSpace S)` and
  `(q : U.obj ⟶ F)`. The source is an arbitrary algebraic space, not necessarily
  a scheme, affine, quasi-compact, or separated.
- Every scheme in the site and every section are quantified in
  `∀ (T : Over S) (a : F.obj.obj (op T)), ...`.
  Here the node's `Z` is named `T` in Lean.
- The associated algebraic space is `∃ (P : AlgebraicSpace S) ...`.
  Its two projections are `p : P.obj.obj ⟶ yoneda.obj T` and
  `r : P.obj.obj ⟶ U.obj.obj`. `IsPullback r p q.hom (yonedaEquiv.symm a)`
  identifies precisely the sheaf `h_T ×_{a,F,q} U`, keeping both canonical maps.
  Presheaf pullbacks compute sheaf pullbacks since the sheaf inclusion preserves
  limits. The map to `h_T` supplies the algebraic space's structure over `T`.
- Flatness and local finite presentation of the projection are the conjunction
  `Flat (yoneda.preimage (c ≫ p)).left ∧
  LocallyOfFinitePresentation (yoneda.preimage (c ≫ p)).left`, required for every
  scheme `V` and representable étale chart `c : yoneda.obj V ⟶ P.obj.obj`.
  This is the compatible-chart condition specialized to a scheme target: the
  identity chart of `T` gives this direction. Conversely, in a compatible diagram
  with an étale target chart `W → T`, pull back the source chart to `W`. The map
  to `W` is a base change of the displayed scheme map, and the graph of the
  chosen compatible lift is an open immersion because `W → T` is étale.
  Flatness and local finite presentation persist under those operations.
  Thus this expresses the node's chartwise properties without a stronger
  representability assumption on `p`.
- Surjectivity on field-valued point classes is
  `IsJointlySurjective (fun _ : Unit ↦ p)`. The existing predicate quantifies over
  every field-valued target point and permits lifting after a field extension.
  With a singleton family it is precisely surjectivity, not surjectivity on
  sections over each scheme and not representability by surjective scheme maps.
- The conclusion is exactly `IsAlgebraicSpace F`, including its representable
  diagonal and representable surjective étale scheme atlas. Neither conclusion
  component is assumed of `F` in the hypotheses.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-size-convention`: its convention record, implemented by explicit `universe u`
  and the existing algebraic-space site's universe levels; there is no declaration
  associated to this convention.
- `def-pc-fppf-site`: `Mathlib.AlgebraicGeometry.Sites.Fpqc`, declarations
  `AlgebraicGeometry.Scheme.fppfPrecoverage` and `Scheme.fppfTopology`;
  `Mathlib.CategoryTheory.Sites.Over`, `GrothendieckTopology.over`.
- `def-weil-pbc-sites-and-cohomology`: `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`, and the retained Mathlib `Sheaf`
  encoding described by that module's docstring. This is publicly imported through
  `Sheaf.AlgebraicGeometry.AlgebraicSpace`. No cohomology is needed here.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`, declarations
  `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsAlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, and `IsEtale`.
  The recorded definition's full signature and docstring were read.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`; its affine definition is equivalent to the stalkwise
  definition as documented there.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `lem-trf-space-fibre-products-etale-covers`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`. The module publicly imports
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`, whose
  `AlgebraicSpace.IsJointlySurjective` is the shared point-class definition used here.
- Mathlib `CategoryTheory.yoneda`, `yonedaEquiv`, `Functor.preimage`, and
  `CategoryTheory.IsPullback` retain the maps, not just an existential object with
  unrelated projections.

The theorem docstring gives all nine natural-language proof steps of the DAG:
reduce the algebraic-space atlas to a scheme atlas by scheme tests; construct its
kernel equivalence relation; make that relation schematic using the lft monomorphism
criterion; obtain fppf-local section lifts; identify the sheaf quotient with F;
slice the flat finitely presented relation; make affine étale replacements;
glue the finite local quotient pieces; then glue the affine pieces and transport
algebraicity. The already recorded proof-dependency modules are imported privately.
The proof-only nodes with no recorded module remain named in the docstring, for
later insertion of their imports when stated. In particular no unrecorded theorem
is introduced for the slicing or replacement prerequisites.

Edge cases checked before writing:

- Empty test schemes and the empty base are allowed: no nonemptiness assumption is
  present. The pullback square and chart tests retain their ordinary empty cases.
- If the atlas is empty, surjectivity forces every tested pullback target to have
  empty point set. There is no spurious inhabitance assumption on `U` or `P`.
- The singleton index `Unit` expresses a single projection, not an atlas family
  required to have points. `IsJointlySurjective` quantifies over field representatives
  after extensions, so residue-field extensions and non-algebraically-closed fields
  are all covered. No characteristic restriction occurs.
- Test schemes, fields, extension fields, and set values use the same `u` as the
  recorded algebraic-space framework, preventing a vacuous smaller test universe.
  There is no independent smaller universe of test schemes or fields.
- Neither flatness nor local finite presentation is replaced by finite type or
  finite presentation; quasi-compactness and quasi-separatedness are not imposed.
- The sheaf diagonal is absent from the hypotheses, as required by 04S6(3).

Searches for an existing statement (2026-10-24):

- `msearch.py ... leansearch` with query "A sheaf with a surjective flat locally
  finitely presented algebraic space atlas is an algebraic space": eight hits on
  ordinary scheme sheaves, locally ringed spaces, module finite presentation, and
  scheme flatness; no matching algebraic-space theorem.
- `msearch.py ... leanfinder` with query "A sheaf on the big fppf site with a
  surjective flat locally finitely presented atlas by an algebraic space is an
  algebraic space": eight hits, only scheme flat-descent/permanence results and
  `LocallyOfFinitePresentation`, no algebraic-space bootstrap theorem.
- `msearch.py ... loogle "AlgebraicSpace, IsAlgebraicSpace"`: zero hits;
  Loogle reports unknown identifier `AlgebraicSpace` in the Mathlib index.
- `msearch.py ... grep "IsAlgebraicSpace|fppf.*atlas|MapIsLocallyOfFinitePresentation"`:
  zero Mathlib hits.
- `rg` in `lean/WeilConjectures` for `IsAlgebraicSpace|fppf.*[Aa]tlas|fppf.*[Bb]ootstrap`
  and `grep -rn` for the item id: no existing statement.
- `rg` in `lean/Sheaf` for fppf atlas/bootstrap and `isAlgebraicSpace_of`: found
  references in proof docstrings and the distinct
  `EtaleSheafSpaceAtlasBootstrap.etale_sheaf_space_atlas_bootstrap`, which assumes
  only étale descent and a scheme atlas with étale tests. Its hypothesis is
  different from the arbitrary algebraic-space fppf atlas here.
- Read `AlgebraicSpaceMorphismProperties.lean` and
  `SpaceLocalPropertiesChartTest.lean` to check the chartwise meaning and existing
  scheme-target specialization; no duplicate predicate is defined in this delivery.
- The exact proposed name `fppf_space_atlas_bootstrap` was also searched in
  `lean/Sheaf`, `lean/WeilConjectures`, and `dag/lean_names_upstream.json`: no match.

No statement dispute or node fault was found. Compilation and prescribed delivery
checks are recorded below as they complete.

## Second reading by Q03

Author's second reading, not an independent review; the dispatcher explicitly forbids
starting another agent and the maintainer supplies the independent review. Reopened
the node and compared it with the theorem signature: S, F, U, q are all bound, all
scheme sections are quantified, the square uses exactly q and the Yoneda map of a,
and both structure projections are retained. `P` is an algebraic space. The chart
condition uses the genuine scheme projection c ≫ p, not an arbitrary map. The
singleton point-lifting predicate expresses exactly the node's surjectivity. The
conclusion uses the recorded algebraic-space predicate on the same sheaf F.

The check specifically distinguished a general algebraic-space map from a
scheme-representable map: `IsSurjective p` would incorrectly strengthen the atlas
hypothesis, so the statement uses `IsJointlySurjective (fun _ : Unit ↦ p)`.
Similarly the property tests use étale charts and never demand that P itself be a
scheme. No conclusion clause, field-extension case, or empty-scheme case was lost.
No mathematical statement change was made after this reading.

## Validation

The prescribed `scompile.py Q03 lem-sfb-fppf-space-atlas-bootstrap` compiled the
module in both sandbox and library modes successfully, with no compiler messages.
Every delivered Lean line is at most 100 characters; `autoImplicit` is disabled.
