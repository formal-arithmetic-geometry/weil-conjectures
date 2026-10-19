## Worker report

`Sheaf.Paper.FiniteSystemPullbackCoherence` states the node on actual schemes,
constant finite coefficient rings, and the published ordinary category of strict
semilinear systems. It supplies the canonical system operations needed to state
the comparison; all theorem proofs are `sorry`, and every definition has real data.
The saved packet's arbitrary functor parameters were removed: its assertion was
false for arbitrary functors, and it omitted the representative and evaluation
clauses. This repairs the Lean rendering, without changing the DAG statement.

The hypotheses and clauses correspond as follows.

- The inverse sequence of finite commutative rings is `A : ℕ → CommRingCat.{u}`,
  `τ : ∀ n, A (n + 1) ⟶ A n`, and `[∀ n, Finite (A n)]`. Index zero labels the
  paper's first term; every coefficient level and every adjacent map is retained.
- The arbitrary scheme morphisms are `j : Y ⟶ Z`, `h : Z ⟶ W`, `k : W ⟶ V`,
  with `Y Z W V : Scheme.{u}`. There are no geometric restrictions.
- The fixed small-site convention is the published `Scheme.ProEt` and
  `ProEt.topology`, with site objects in `u+1`, morphisms in `u`, and coefficients
  lifted to `u+1`. The essentially-small instances supply small representatives;
  no equality between the site object and morphism universes is imposed.
- `finiteSystemRings` is the existing `proEtaleConstantRing`; it is sheafification
  of the constant presheaf on `ULift (A n)`. `finiteSystemRingTransition` is the
  constant-sheaf image of the given ring homomorphism, with `RingHom.ulift`.
  `finiteSystemRingComponent` is the dependency's canonical constant-section
  direct-image map. Its horizontal/vertical naturality is stated explicitly in
  `finiteSystemRingComponent_naturality`, including all coefficient maps.
- `finiteSystems` and `finiteSystemDerived` specialize the dependency's `Systems`
  and `DS`, without defining another category of systems or diagrams in derived
  categories. The sequence ring uses every semilinear horizontal transition.
- `finiteSystemPushforward` is explicit sectionwise precomposition on the sequence
  site with restriction along the canonical ring map. The universal left adjoint
  `finiteSystemPullback` is determined up to the unique adjunction-compatible
  isomorphism. It is not selected from an existence assertion about arbitrary
  functors. Its exactness is `finiteSystemPullback_exact`.
- The comparison of this pullback with the given finite-coefficient level pullback
  is `finiteSystemPullbackEvaluation`. Its existence/uniqueness statement fixes it
  on the actual system unit generators by the published normalized level unit.
  Thus the system operation is the stipulated levelwise module inverse image,
  including its action on maps. `finiteSystemDerivedPullback` is precisely its
  `mapDerivedCategory`, hence acts termwise on arbitrary unbounded complexes.
- `finiteSystemComposition` is the unique conjugate of the right-adjoint
  fibre-product comparison. `finiteSystemComposition_existsUnique` specifies that
  comparison on every section at `(n,U)`, fixing its scalar action and all
  semilinear transitions before deriving. It constructs comparisons for every
  composable pair, including the four pairs in the displayed associativity law.
- `finiteSystemComplexComposition` is `NatIso.mapHomologicalComplex` of that same
  system map: at every degree it is the ordinary module-system comparison.
  The first conjunct of `finiteSystemPullbackCoherence` identifies every component
  of that comparison with the already published canonical module comparison.
  Because its source is a map of entire strict systems, transition compatibility
  is part of its type, not an equality inferred from derived evaluations.
- `finiteSystemDerivedComposition` localizes that specified ordinary comparison
  using `mapDerivedCategoryNatIso` and the canonical composition factorization.
  The second conjunct identifies its evaluation with the inverse of
  `proEtaleConstantRingPullbackComposition`, which has exactly the node's
  direction from composite to iterated pullback. The evaluation identifications
  themselves are the localizations of the unit-normalized ordinary ones.
- The third conjunct is an equality of natural transformations on cochain
  complexes of whole strict systems, before localization. It includes the
  canonical functor associator and the transport by `Category.assoc j h k`.
  The fourth conjunct is exactly the displayed equality at each
  `S : finiteSystemDerived A τ V`, after localization; the same associator is
  identity on its object components. Scheme-map reassociation is transported
  explicitly rather than silently identifying nondefinitionally equal functors.
- There are no normalization, boundedness, constructibility, flatness, or
  coefficient-flatness assumptions. The construction never tensors a transition
  along a coefficient ring map.

Dependency declarations used are `AlgebraicGeometry.Scheme` and `Scheme.ProEt`
from Mathlib's scheme/pro-etale modules; `CategoryTheory.constantSheaf` from
`Mathlib.CategoryTheory.Sites.ConstantSheaf`; `Systems`, `DS`, `systemRing`,
`ringPresheaf`, `evaluation`, and `e` from `Sheaf.Paper.SemilinearSystemModels`,
publicly imported by the recorded `Sheaf.Paper.SemilinearDerivedSections`;
`CategoryTheory.DerivedCategory` and its ordinary localization; and
`proEtaleConstantRing`, `proEtaleCoefficientDirectImageMap`,
`proEtaleConstantRingPullback`, `proEtaleConstantRingAdjunction`,
`proEtaleConstantRingDerivedPullback`,
`proEtaleConstantRingModulePullbackComposition`, and
`proEtaleConstantRingPullbackComposition` from the published pro-etale modules.
The recorded `Sheaf.Paper.IntegralFinitePullbackComposition` publicly imports the
canonical general comparison and its constant-coefficient specialization.
`finiteCoefficientInverseImageMap_isIso` and
`finiteCoefficientModulePullback_exact` are imported from the recorded dependency
modules for the planned proof. All already-stated proof dependencies are imported,
either directly or through those modules; no import cycle is introduced.
The size-convention node's closed upstream `ModuleDerivedCategory` record was
read through `scompile.py --source`; its docstring confirms the site universes.
Here the required `DS` uses the recorded standard ordinary localization of system
modules rather than changing the system-category presentation.

Edge cases checked: the zero ring, empty schemes and empty site objects, identity
scheme maps, nonflat coefficient homomorphisms, the first coefficient level,
noncartesian strict systems, zero objects, and arbitrary unbounded complexes.
The empty-object coefficient map is the unique zero-ring-sheaf map, as in the
recorded constant-ring-map theorem. No coefficient-flatness hypothesis is needed:
the transitions are semilinear maps, and the comparison is constructed in their
abelian system category before passage to complexes and localization.

Searches: the saved packet's searches were retained and checked against current
sources. Additional `msearch.py leanfinder` query “Canonical inverse image
composition on strict semilinear coefficient systems compatible with derived
evaluation and associativity before localization” returned eight ordinary module
localization hits, with no exact theorem. `msearch.py loogle '"mapDerivedCategory"'`
returned twelve generic exact-functor descent declarations, including
`mapDerivedCategoryCompIso` and `NatTrans.mapDerivedCategory`, not the strict-system
statement. `msearch.py grep 'mapHomologicalComplexCompIso|mapHomologicalComplexComp'
Algebra/Homology` returned the two generic complex-composition declarations in
Additive/HomotopyCategory. The saved searches for `pullback_assoc` and
`pullbackComp|semilinear.*system` found ordinary module-sheaf comparisons only.
`rg` for `finiteSystemPullback`, `finiteSystemDerived`, `finiteSystemComposition`
and the node id over the project and upstream Lean trees, and the upstream name
index, found no existing declaration. The integral comparison sequence module was
read: it provides analogous operations for the specialized DVR quotient tower,
which cannot represent an arbitrary sequence of finite commutative rings. Its
construction confirmed the sectionwise sequence-site adjunction route. We use the
existing generic semilinear system and evaluation definitions, not a private copy.

All supporting declarations in this module belong to the same node's canonical
system-pullback construction and are listed in `lean.declarations`. No new notion
node, dependency-interface repair, DAG statement correction, or disputed statement
is needed. The maintainer performs the independent review of this direct delivery.

## Second reading by Q71

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
