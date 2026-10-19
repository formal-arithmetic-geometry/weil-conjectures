## Worker report

Record the already published declaration
`AlgebraicGeometry.Scheme.proEtaleProjectionFormulaMate` in
`Sheaf.Paper.ProjectionFormulaBaseChangeNaturality` with `existing: true`.
There is no new library module and no new definition of the projection map.
Read the live declaration with `scompile.py --source`; it agrees with the
checked-out source. The node copy changes only `lean`.

The exact coefficient specialization is
`proEtaleProjectionFormulaMate f (completedAdicCommRing Y d)
(completedAdicCommRing X d) c a b K P`, where
`d : AdicCoefficientDatum A`. Here the two underlying module categories are
`CompletedAdicModules Y d` and `CompletedAdicModules X d`, respectively.
The scratch compilation checks this specialization with those exact categories,
rather than replacing them by constant-coefficient categories.

Clause-by-clause correspondence:

- The arbitrary scheme morphism is `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  There is no properness, flatness, finite-type, or nonempty hypothesis.
- The completed coefficient sheaves are the actual inverse limits
  `completedAdicCommRing Y d` and `completedAdicCommRing X d`.
  `AdicCoefficientDatum` supplies the Noetherian ring, finitely generated ideal,
  additive torsion of the first quotient, and finiteness and perfectness of all
  positive quotients required by the dependency. Its positive level `n` is `n+1`.
  Forgetting commutativity gives exactly `completedAdicRing`, so the module
  objects here are the node's completed-coefficient module objects.
- The specified identification is the argument
  `c : (proEtaleSheafInverseImage f CommRingCat.{u+1}).obj R ≅ S`,
  evaluated at these two completed sheaves. It is retained as specified data;
  no arbitrary coefficient identification is selected.
- `L` is `proEtaleRingDerivedPullback f R S c`; `R` in the node's adjunction
  notation is `proEtaleRingDerivedDirectImage f R S c`.
  Their fixed adjunction is `proEtaleRingDerivedAdjunction f R S c`.
  This is induced by the uniquely normalized ordinary module adjunction.
- `K` and `P` are unrestricted objects of `DerivedCategory
  (proEtaleRingModules X S)` and `DerivedCategory (proEtaleRingModules Y R)`.
  The specialization typechecks with `DerivedCategory (CompletedAdicModules X d)`
  and `DerivedCategory (CompletedAdicModules Y d)` directly.
- The uncompleted tensors are `a.tensor` and `b.tensor`, for the recorded
  `a : ProEtaleTensorModel Y R` and `b : ProEtaleTensorModel X S`.
  Their `representative` fields identify them with signed total sheaf tensor
  on flat-term K-flat complexes. These are presentations of the derived tensor
  specified by the dependencies, not extra flatness or boundedness conditions
  on `K` or `P`, and not completed tensor products.
- The comparison `c_{F,G}` is
  `(proEtaleCanonicalTensorComparison f R S c a b).hom.app (F,G)`.
  The comparison's defining theorem characterizes it uniquely on every flat
  K-flat representative pair using ordinary tensor pullback and the exact
  pullback factorization. Thus it is the recorded canonical comparison.
- `M` is `a.tensor.obj ((proEtaleRingDerivedDirectImage f R S c).obj K, P)`.
  `N` is `b.tensor.obj (K, (proEtaleRingDerivedPullback f R S c).obj P)`.
  The existing declaration has precisely type `M ⟶ R.obj N`.
- Unfolding `proEtaleProjectionFormulaMate` gives the existing
  `CategoryTheory.derivedProjectionFormulaMate` with these exact operations,
  tensors, comparison, and objects. That definition merely curries the
  bifunctors and calls `CategoryTheory.Adjunction.rightAdjointProjectionMap`.
  Reading that upstream definition shows its component is `adj.homEquiv M N`
  applied to comparison at `(R.obj K,P)` followed by tensor of
  `adj.counit.app K` with the identity of `L.obj P`. This is exactly alpha in
  the node, including its direction.
- `Adjunction.homEquiv_unit` identifies this component with
  `adj.unit.app M ≫ R.map alpha`, the node's explicit ordered composite.
  `Adjunction.homEquiv_symm_rightAdjointProjectionMap_app_app` gives the
  equivalent adjunct description. Both facts are already upstream: no new
  theorem or proof is introduced in this delivery.
- The result is a morphism only. Its declaration makes no assertion that it
  is invertible. No properness, perfection, derived completeness, or choice
  of a complex representative is demanded of the two input objects.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage` publicly
  retains the arbitrary identified-coefficient operations from
  `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction` and
  `Sheaf.AlgebraicGeometry.ProEtaleOperations`. Use their
  `proEtaleRingModules`, `proEtaleRingDerivedPullback`,
  `proEtaleRingDerivedDirectImage`, and `proEtaleRingDerivedAdjunction`.
  The finite-coefficient primary declaration is not substituted for the
  completed-coefficient operations; its public general interface is used.
- `Sheaf.Paper.AdicCoefficientDatum` publicly retains
  `Sheaf.Paper.CompletedAdicCoefficientDatum`: `AdicCoefficientDatum`,
  `completedAdicRing`, `completedAdicCommRing`, `CompletedAdicModules`.
  Read also its generalized finite-function coefficient presentation.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`,
  `SheafOfModules.site_derived_tensor_descent`, supplies the K-flat localization
  tensor description. Its same-universe signature is not imposed on the actual
  pro-etale sites; the next dependency supplies their recorded tensor models.
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`, `ProEtaleTensorModel`,
  `proEtaleCanonicalTensorPullback`, `proEtaleCanonicalTensorComparison`,
  gives the canonical comparison with site object universe `u+1`, Hom universe
  `u`, and coefficient universe `u+1`. No universe equality is added.
- Existing implementation chain: `Sheaf.Paper.ProjectionFormulaArrows`,
  `CategoryTheory.derivedProjectionFormulaMate`; upstream
  `WeilConjectures.CategoryTheory.Adjunction.ProjectionMap`,
  `CategoryTheory.Adjunction.rightAdjointProjectionMap` and its transpose lemma;
  Mathlib `CategoryTheory.Adjunction.homEquiv_unit`.

Source verification: the local literature files named by the node are absent,
so read [Stacks 0B56](https://stacks.math.columbia.edu/tag/0B56) and
[Stacks 0943](https://stacks.math.columbia.edu/tag/0943) directly. They give the
same counit adjunct construction for arbitrary ringed topoi. The blueprint node
specializes its ring sheaves to completed coefficients without completing tensor.

Edge cases: empty schemes and empty site objects introduce no excluded case;
zero coefficient rings and zero input objects introduce no nonzero assumption;
the identity scheme morphism and any specified coefficient identification remain
allowed. No degree or amplitude bound occurs, so arbitrary unbounded inputs and
shifts are included. No assumption that the adic ring itself is complete occurs.
All levels of the datum are positive, including the first quotient.

Searches performed (2026-10-16):

- `msearch.py ... leanfinder`, query “Projection formula morphism on derived
  categories of sheaves of modules defined as adjoint of pullback tensor
  comparison followed by tensor counit”: eight hits on ordinary sheaf pullback,
  its adjunction and unit; no derived completed-coefficient map in Mathlib.
- `msearch.py ... loogle`, query `Adjunction.homEquiv, Functor.prod`: unknown
  identifier `Adjunction.homEquiv`, no hits. This unsuccessful search is not a
  nonexistence claim.
- `msearch.py ... grep`, query
  `projectionFormula|projection_formula|ProjectionFormula` in CategoryTheory:
  zero Mathlib hits.
- `msearch.py ... leansearch`, query “Projection formula morphism derived
  ringed topoi unit counit tensor comparison”: service unavailable, Internal
  Server Error. No nonexistence verdict is inferred from that service.
- `rg` for projection-formula names in upstream CategoryTheory and pro-etale
  source: found `Adjunction/ProjectionMap.lean` and its compatibility lemmas;
  pro-etale six-functor formulas concern other coefficient presentations.
  Searching the exact node id in upstream `WeilConjectures` found no hit.
- `rg` for projection-formula names under project `lean/Sheaf`: found the exact
  generic pro-etale mate in `ProjectionFormulaBaseChangeNaturality.lean` and its
  generic bifunctor wrapper in `ProjectionFormulaArrows.lean`. Read both and
  the upstream construction fully. DAG search confirms that the same helper is
  recorded among the naturality node's declarations. Reuse it, not a copy.

No statement correction, disputed statement, new node, or dependency repair.

Validation: `scompile.py Q20 def-weil-pbc-projection-formula-map
scratchpad/ProjectionFormulaChecks.lean` passed against current server sources
with no warnings or errors. It typechecked both the existing mate specialized
to `CompletedAdicModules` and the explicit alpha/unit composite, and checked
the upstream component formula and `Adjunction.homEquiv_unit`. Local overlay
compilation initially encountered a stale duplicate K-flat declaration; the
wrapper automatically confirmed the current server sources successfully.
No delivered file or dependency was changed to bypass that local cache issue.
The final dry run is `deliver2.py Q20 def-weil-pbc-projection-formula-map --no-push`.

## Second reading by Q20

I reread the node statement, the recorded declaration, every statement dependency,
and Stacks Tags 0B56 and 0943. The item-by-item verdict is:

- The object `f : X ⟶ Y` is rendered by the implicit schemes and explicit morphism
  in `proEtaleProjectionFormulaMate`; it is arbitrary, with no properness,
  finiteness, flatness, or nonemptiness hypothesis. PASS.
- The node's completed coefficient sheaves `A_Y` and `A_X` are rendered by the
  specialization `completedAdicCommRing Y d` and `completedAdicCommRing X d`,
  with `d : AdicCoefficientDatum A`; the recorded datum supplies exactly the
  Noetherian, ideal, torsion, finite, and perfect quotient assumptions. PASS.
- The specified coefficient identification `f⁻¹ A_Y ≅ A_X` is retained as the
  explicit `c` argument. No arbitrary or merely inhabited identification is used.
  PASS.
- The derived pullback, direct image, and their adjunction are respectively
  `proEtaleRingDerivedPullback`, `proEtaleRingDerivedDirectImage`, and
  `proEtaleRingDerivedAdjunction`, with the dependency's normalized module
  adjunction. PASS.
- The arbitrary inputs `K` and `P` are unrestricted derived objects in the two
  completed module categories. The declaration imposes no boundedness, perfectness,
  completeness, or representative choice. PASS.
- The tensor bifunctors are the uncompleted signed-total models `a.tensor` and
  `b.tensor`; the canonical comparison is
  `proEtaleCanonicalTensorComparison`. Its representative characterization gives
  the node's required pullback comparison, including its direction. PASS.
- For `M = R K ⊗^L P` and `N = K ⊗^L L P`, unfolding the existing declaration gives
  the mate of the comparison followed by the counit tensor identity, hence the
  node's `alpha`. The upstream adjunction transpose lemma identifies the component
  with `η_M ≫ R.map alpha`, exactly the displayed `π`; the declaration asserts no
  invertibility. PASS.

The source section states the map for every morphism of ringed topoi and arbitrary
unbounded `E,K`, as the adjoint of the counit tensored with pullback. The node's
completed-coefficient specialization preserves that scope and adds no conclusion.
The empty scheme/site, zero coefficient ring, zero objects, identity morphism,
arbitrary shifts, and the first positive quotient are all admitted; no nonzero or
degree assumption appears. Universes remain the pro-etale object universe `u`,
coefficient universe `u+1`, and morphism universe `u` through the recorded tensor
models.

Searches were repeated with `rg` over Mathlib, upstream `WeilConjectures`, and
project `lean/Sheaf`, plus `msearch.py` LeanFinder/Loogle queries. Only the generic
upstream projection-map ingredients and the project's exact
`proEtaleProjectionFormulaMate` were found; no competing definition matches the
completed-coefficient notion. The source Tags 0B56 and 0943 were opened directly.

No mismatch was found. I changed no Lean module, dependency, statement, or node
field beyond retaining the existing declaration record. The scratch specialization
and explicit alpha/unit composite compile with `scompile.py`; the delivery dry run
is required next.
