## Worker report

The module `Sheaf.AlgebraicGeometry.InfiniteFieldReductiveRationalDensity` states
`AlgebraicGeometry.ReductiveTorusCentralizer.rationalPoints_dense_of_isReductive`.
Its only theorem has proof `sorry`; it introduces no new definitions or axioms.
The item node is changed only in `lean`.

The source was read directly from the local Milne PDF: Theorem 17.93(b), printed
p.382, says that reductivity gives unirationality and, for infinite k, rational-point
density. Theorem 25.9(a), p.546, explicitly invokes that density. The latest
blueprint unit `sk-thm-sf-ctf-stability` and its direct-images proof (3) were also
read; this is a supporting lemma of its inherited algebraic-group proof chain.

Clause-by-clause rendering:

- The field is `{k : Type u} [Field k]`, and infinitude is `[Infinite k]`.
- A group scheme over k is `G : Grp (Over (Spec (.of k)))`. Its underlying scheme
  is `G.X.left`, and its structure morphism is `G.X.hom`. `Grp` bundles the
  recorded `CategoryTheory.GrpObj` and hence the group laws.
- Reductivity is exactly the recorded `hG : IsReductive G`. Its first conjunct
  `SolvableGroupStructure.IsAlgebraic G` is `IsAffine G.X.left` together with
  `LocallyOfFiniteType G.X.hom` and `QuasiCompact G.X.hom`. Its second is
  `Smooth G.X.hom`; its third is connectedness after `AlgebraicClosure k` base
  change, using `ConnectedSpace`, which includes nonemptiness.
- The last conjunct of `IsReductive` quantifies over closed normal algebraic
  subgroup schemes U of that geometric base change, requiring connectedness and
  `SolvableGroupStructure.IsUnipotent U`, and concludes
  `Nonempty (U ≅ Grp.trivial _)`. The unipotent predicate includes smoothness and
  a faithful finite-dimensional matrix representation (a closed subgroup
  immersion into `GeneralLinearGroup (ULift (Fin n))`), with a positive power of
  each geometric matrix minus identity equal to zero. The extra algebraicity
  condition on U is automatic for a closed subgroup of an affine finite-type
  group over a field; it does not restrict which subgroups the node excludes.
- Every nonempty Zariski open subscheme is expressed by
  `∀ V : G.X.left.Opens, (V : Set G.X.left).Nonempty → ...`.
  Mathlib's `V.toScheme` is the open subscheme and `V.ι` its open immersion.
- The first conclusion is `∃ p : Spec (.of k) ⟶ V.toScheme,
  p ≫ V.ι ≫ G.X.hom = 𝟙 (Spec (.of k))`. The equation states exactly that p is
  a k-morphism for the inherited structure on V.
- The equivalent density assertion is the second conjunct, `DenseRange` of
  `fun p : Over.mk (𝟙 (Spec (.of k))) ⟶ G.X ↦
  p.left.base (IsLocalRing.closedPoint k)`. The morphism in `Over` already
  includes compatibility with the structure map, so its domain is exactly
  `Hom_k(Spec k,G)`. The spectrum of a field has one point, and its canonical
  closed point gives the image in the underlying Zariski space. This is the
  same set of images as in the node. The conjunction records both equivalent
  formulations, adding no stronger assertion.
- There is no perfectness, splitness, separability, characteristic, or
  algebraic-closedness assumption on k.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and `Grp`
  (def-sc-group-scheme); the project group-scheme docstring in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` confirms this specialization.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (def-sbc-smooth-morphisms).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`
  (def-weil-connected-scheme).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `LocallyOfFiniteType` and
  `QuasiCompact` (def-weil-finite-type-morphism).
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive`
  (def-sfb-reductive-torus-centralizer-terminology); its full definition and the
  definitions `SolvableGroupStructure.IsAlgebraic`, `IsUnipotent`, and
  `MultiplicativeType.baseChange` were read, with no substitute definition.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`
  (def-weil-open-immersion), applied to the canonical open inclusion from
  `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.toScheme`, `Scheme.Opens.ι`.

All recorded statement-dependency modules are public imports. Stated proof
prerequisites are imported privately: `ReductiveTorusSelfCentralizer`, the
pullback module, `ToriMultiplicativeType`, and `Mathlib.AlgebraicGeometry.Scheme`.
The open-factorization Mathlib match (`IsOpenImmersion.lift`, `lift_fac`,
`lift_uniq`) is already covered by the public open-immersion import.
`lem-sfb-cartan-product-dominance`, `lem-sfb-maximal-torus-field-extension`,
`lem-sfb-torus-unirational-parametrization`, and
`lem-sfb-laurent-vector-evaluation-test` have no recorded Lean module in the node
files read for this delivery; there is therefore no module to import for them.
They are proof-only dependencies and are preserved in the stepwise proof docstring.

Edge cases checked before writing: the trivial group and rank-zero tori are
allowed, and the proof's affine-space dimension-zero case is explicitly included.
The empty open is excluded only by the stated nonemptiness premise. There is no
finite-field version: an infinite field is required for polynomial nonvanishing.
Imperfect infinite fields and nonsplit reductive groups remain covered. Arbitrary
characteristic and arbitrary universe u are retained, using the dependency's same
universe for k and its schemes. Rational points of an open are schemes maps over
k, not merely points of the underlying space. Since Spec k is a singleton,
evaluation at its canonical closed point captures each rational point's full image.

Searches for an existing theorem (all through prescribed msearch.py, with the
raw tool output in the sandbox search log):

- LeanFinder, query "Every nonempty Zariski open subset of a reductive group over
  an infinite field contains a rational point": 8 hits, including
  `AlgebraicGeometry.dominant_eq_topologically` and minimal-action open-set lemmas;
  none supplies the reductive-group theorem.
- LeanSearch, query "Rational points of a reductive group over an infinite field
  are Zariski dense": 8 hits, including `Dense`, rational-map domain density,
  rational density in p-adic fields, and dense subsites; no matching theorem.
- Loogle, query `"Zariski", "dense"`: 2 affine-Zariski dense-subsite instances,
  neither a theorem about rational points.
- Mathlib grep, query `unirational|rationalPoints.*dense|dense.*rationalPoints`:
  0 hits.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `rationalPoints.*dense|dense.*rationalPoints|infinite.field.*reductive|infiniteField.*[Dd]ens`:
  no matching density theorem. Searching the item's id in WeilConjectures also
  returned no hit. Full declaration-name search in Mathlib, WeilConjectures,
  and Sheaf returned no collision.
- Broader rational-point searches found
  `Scheme.Hom.denseRange_fieldPoints` in
  `WeilConjectures.AlgebraicGeometry.DensePoints`; its hypothesis is
  `[IsSepClosed k]`, so it is not the present theorem over arbitrary infinite k.
  It is not duplicated here. No private rational-point predicate is defined:
  points are the existing `Over` morphisms and morphisms of schemes.

No new nodes, dependency repairs, statement corrections, or statement disputes
were needed. The existing compact-object example module has been withdrawn;
its node now points upstream, so module/import/exposure conventions follow the
current standing brief and the recorded reductive-group module.

## Second reading by Q13

Final self-check with the node and file open; this is not an independent worker
review. The dispatcher brief forbids starting another agent and assigns the
independent delivery review to the maintainer.

I rechecked the field/infinitude binders, every conjunct of the dependency's
reductivity predicate, the nonempty-open premise, the base-field equation for
its rational point, and the over-category domain of the dense-range map.
The canonical closed point is the unique point of Spec k. Both equivalent
conclusions are included. The only adjustment after the first compile was to
replace an ambiguous inferred `default` by `IsLocalRing.closedPoint k` in the
dense-range map; no mathematical hypothesis or clause changed.

## Validation

Validation uses scompile.py and deliver2.py only. The final scompile.py invocation passed both the sandbox and library-module
checks with exit code 0 and no warnings or errors (10.5 s and 1.5 s).
The dry run and delivery are checked separately by deliver2.py.

The deliver2.py --no-push dry run returned OK: the preflight and per-file
compile passed (dry-run commit 2df696b6103); nothing was pushed by that check.
