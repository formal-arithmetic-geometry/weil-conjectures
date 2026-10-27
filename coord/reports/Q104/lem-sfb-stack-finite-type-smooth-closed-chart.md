## Worker report

The module `Sheaf.AlgebraicGeometry.StackFiniteTypeSmoothClosedChart` states
`CategoryTheory.stack_finiteType_smooth_closed_chart`, with its only theorem proof `sorry`.
No statement correction, new DAG node, or dependency repair is needed.

Hypothesis and clause correspondence:

- An arbitrary scheme S is `{S : Scheme.{u}}`. Explicit universes `u v w` keep the scheme
  universe and the stack object/morphism universes independent. Fields range over `Type u`,
  the same universe as schemes; there is no smaller independent field universe.
- The stack X/S is `F : BasedCategory.{v, w} (Over S)` with
  `hF : IsAlgebraicModuliStack F`, using the existing etale-stack, diagonal and smooth-atlas
  definition. The scheme category is `AlgebraicGeometry.Scheme` throughout.
- Its point x is `x : ModuliPoints F`, the existing quotient of field objects by arrows,
  equivalently common field extension and isomorphism for fibred groupoids.
- Finite type of x is the existential `hx`: a field K, structural map b, and actual functor
  a from its representable discrete groupoid, with `ModuliSpaceTest @LocallyOfFiniteType a`.
  The condition `x ∈ Set.range (moduliPointMap a)` means that this field map represents x:
  Spec K has exactly one point. No finite-type condition on K over the base is added.
- The existential `U : Over S` supplies an S-scheme; `IsAffine U.left` supplies affineness.
  The map q is an actual `BasedFunctor (discreteModuli (yoneda.obj U)) F`.
  `ModuliSpaceTest @Smooth q` is smoothness tested on every etale chart of every scheme
  base change. This predicate includes the required algebraic-space representability.
  Surjectivity of q is not imposed (the node only asks for a smooth chart through x).
- The point is `z : U.left`, with `IsClosed ({z} : Set U.left)`.
  `z ∈ moduliChartPreimage q {x}` says its image is x, using the existing field-valued
  chart-preimage definition, without defining a second scheme-point map.
- The helper `moduliResidueFieldChart q z` is the actual composite of q with the discrete
  Yoneda map of `U.left.fromSpecResidueField z`. Its domain has structural map
  `U.left.fromSpecResidueField z ≫ U.hom`; its field is literally `U.left.residueField z`,
  the quotient of the local ring by its maximal ideal. The following
  `ModuliSpaceTest @LocallyOfFiniteType` is the required property of this particular a.
- R is existentially an `AlgebraicSpace S`. The maps s,t have target the actual
  representable presheaf of Spec kappa(z). `ModuliSelfRelationGroupoid` specifies that R
  is the self-relation of this particular a, not an arbitrary groupoid: `arrows` is a
  vertical natural isomorphism between a s and a t, and `fully_faithful` represents each
  vertical arrow between two test-scheme points uniquely by a section of R. Since F is
  fibred in groupoids, vertical arrows are isomorphisms, so this is exactly the functor of
  triples (x,y,alpha), i.e. Spec kappa(z) times_F Spec kappa(z), with its projections.
- The e,i,c maps and `AlgebraicSpace.IsPresheafGroupoid` state all groupoid laws.
  The `composition` field fixes c to composition of the actual arrows in F, using the
  existing `spaceGroupoidPresentationArrow` transport of endpoints. Thus identities and
  inverses are forced as well; no unrelated groupoid operation is permitted.
- The final universal quantification over every etale scheme chart b of R requires
  `LocallyOfFiniteType` for both actual scheme maps b s and b t. This is precisely local
  finite type of both projections to Spec kappa(z).

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.fromSpecResidueField` and its field instance.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Algebra.Field.Defs`: `Field` (available through the scheme imports).
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `discreteModuli`,
  `discreteModuliMap`, `ModuliTwoIso`, the 2-fibre products and `HasSpaceBaseChange`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliPoints`, `moduliPointMap`,
  `moduliChartPreimage`, `ModuliSpaceTest`. These definitions are not restricted by a DM
  hypothesis; only this node's pre-existing DM closed-set predicate has that restriction.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceGroupoid`: `IsPresheafGroupoid`.
- `Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation`:
  `spaceGroupoidPresentationArrow`, reusing its actual endpoint transport.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, the actual Yoneda
  representable sheaf endowed with its algebraic-space property.

The last four owning definition nodes were added to stmt_deps where not already present,
under the rule allowing existing landed notions. The two new helpers belong to the notion
already explicitly stated by this item: the canonical representative and its self-relation.
Their data are explicit, contain no sorry, and their docstrings carry this item's blueprint id.
There is no second definition of any existing point, chart property, or groupoid law.

Proof-only imports are `SpaceLocalPropertiesChartTest`, `StackChartwiseSmoothEtaleCalculus`,
Mathlib's etale-morphism module and maximal-ideal theorem module. The existing scheme-space
module is public because the statement's self-relation interface uses its construction.
The unstated proof dependencies `lem-sfb-finite-type-field-point-characterization`,
`lem-sfb-self-relation-quotient-embedding`, and
`lem-sfb-stack-diagonal-space-source-representability` have no recorded modules to import;
the natural-language proof names their exact roles. No missing theorem was assumed as a
hypothesis. No missing statement dependency remained.

Edge cases checked before drafting: an empty stack or empty base has no finite-type point,
so hx cannot hold; the output z ensures U is nonempty without an added hypothesis. The generic
point of a local scheme may only become closed after affine shrinking, so no closedness
in a global atlas is required. No Jacobson, Noetherian, separated, finite-presentation,
quasi-compactness, or field characteristic restriction was inserted. For BG the self-relation
retains all automorphisms through the unique-arrow representation, rather than passing to an
orbit relation. The degree-one extension kappa(z)/kappa(z) is permitted, as are arbitrary
field extensions in representing x. The output chart is smooth but need not cover X.

Sources opened: `literature/stacks-project/stacks-morphisms.tex`, the complete lemma
`lemma-point-finite-type` (06FX) and the first proof paragraph of
`lemma-point-finite-type-monomorphism` (06G3). These give the exact affine chart and relation
clauses. The docstring carries all four proof steps of the node, with the scheme/chart-test
identification explicitly preserved. No node fault or STATEMENT-DISPUTED finding.

Searches:

- msearch leanfinder, "A finite type point of an algebraic stack lifts to a closed point in
  an affine smooth chart": 8 hits, only scheme smoothness and residue-field facts; no stack
  chart statement. In particular `isClosed_singleton_iff_locallyOfFiniteType` assumes a
  Jacobson scheme and cannot be used to impose a Jacobson hypothesis here.
- msearch loogle, `"AlgebraicStack", "LocallyOfFiniteType"`: OK, zero hits.
- msearch grep, `AlgebraicStack|finiteTypePoint|StackPoint`: OK, zero Mathlib hits.
- msearch leansearch, "A finite type point of an algebraic stack admits a closed point in
  an affine smooth chart": 8 hits on schemes, local rings and smoothness; no exact statement.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for stack/finite-type point names found the
  existing `ModuliPoints`, `ModuliSpaceTest`, chart-preimage, residue-field chart-point maps,
  and `IsPresheafGroupoid`, all reused. The scheme-only Artin `FiniteTypePoint` is a different
  notion on scheme points, not a definition of a stack finite-type point.
- rg for the item's blueprint id in `lean/WeilConjectures`: no existing declaration.
- rg for the three new declaration names in Mathlib, both project roots, and the upstream
  name index: no existing declaration.

Validation: scompile.py compiled the file in both sandbox and library module positions,
5.1 and 5.2 seconds, with no errors or non-sorry warnings. The deliver2.py --no-push dry run passed preflight and its fresh per-file compile
(commit 202fa3463b8 before this report-only update).

## Second reading by Q104

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
