## Worker report

The module `Sheaf.AlgebraicTopology.RealizationSingularUnitWeak` states
`SSet.Enhanced.realization_singular_unit_weak`, with `sorry` as its entire proof.
No definition is introduced, no statement correction is needed, and the node copy changes
only `lean`. The theorem docstring gives all eight steps of the recorded evaluation proof.
The source was opened online: Kerodon Theorem the project server (Milnor),
https://kerodon.net/tag/0142, and Corollary the project server,
https://kerodon.net/tag/03X7. The first applies to every simplicial set; the second
identifies weak equivalence with weak equivalence after geometric realization.

Clause-by-clause comparison:

- The fixed universe and arbitrary small simplicial set are `universe u` and
  `(X : SSet.{u})`. All variables are explicitly bound and `autoImplicit` is false.
  Mathlib's `SSet.toTop.{u}` and `TopCat.toSSet.{u}` use compatible universe lifts of
  the topological simplices, so no equality of extra universes or size hypothesis is added.
- `Sing(T)` is the existing `TopCat.toSSet.obj T`, from
  `Mathlib.AlgebraicTopology.SingularSet`. Its full definition is restricted lifted Yoneda
  on the topological simplex functor. `TopCat.toSSetObjEquiv T n` identifies its simplices
  with continuous maps from the real standard simplex; its operators are precomposition
  by `SimplexCategory.toTop.map`, i.e. affine coordinate pushforward. This is exactly
  the singular complex in the statement, so it is used without a second definition.
- The map `u_X` is `sSetTopAdj.unit.app X`. The inspected signature of
  `sSetTopAdj_unit_app_app_down` identifies its value at `a : X.obj m` with
  `SSet.toTopSimplex.inv.app m.unop ≫ SSet.toTop.map (SSet.yonedaEquiv.symm a)`.
  This is the continuous characteristic map of the simplex, sending `t` to `[a,t]`,
  rather than an arbitrary map into the singular complex.
- The conclusion is the dependency's
  `SSet.Enhanced.IsWeakHomotopyEquivalence (sSetTopAdj.unit.app X)`.
  Its first conjunct is `Function.Bijective (componentsMap (SSet.toTop.map f).hom)`:
  the required bijection on path components of the realized unit.
- Its second conjunct quantifies over `r : ℕ`, `1 ≤ r`, and every
  `x : SSet.toTop.obj X`, asserting bijectivity of
  `homotopyGroupMap (SSet.toTop.map f).hom r x`.
  This is exactly postcomposition on relative-boundary cubical homotopy classes.
  Postcomposition preserves concatenation in the first coordinate, so bijectivity
  states the group-isomorphism condition, as explained in that dependency's docstring.
  The basepoint quantifier includes all realization points, not only vertices.
- There are no other binders or hypotheses: in particular no Kan instance, finiteness,
  connectedness or inhabitance assumption. Degree zero is handled by path components,
  and all positive degrees by the second conjunct.

Dependency interfaces inspected and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones` is the public statement-dependency import.
  Its `SSet.Enhanced.IsWeakHomotopyEquivalence`, `componentsMap`, and `homotopyGroupMap`
  provide the exact realization convention recorded by `def-cbc-enhanced-diagrams-cones`.
  The module's recorded main declaration `SSet.Enhanced.coneCategory` and its documentation
  were read; the weak-equivalence helpers in the same recorded declaration list are the
  part of this dependency needed here.
- `Mathlib.AlgebraicTopology.SingularSet`, reexported by that dependency, provides
  `TopCat.toSSet`, `TopCat.toSSetObjEquiv`, `SSet.toTop`, `sSetTopAdj`, and the unit formula.
- Ordinary proof imports retain the DAG's proof plan:
  `Sheaf.AlgebraicTopology.RealizationFiniteLimits` (`SSet.realization_finite_limits`),
  `Sheaf.AlgebraicTopology.KanRealizationSerre` (`SSet.kan_realization_serre`),
  `Sheaf.AlgebraicTopology.RealizationCylinder` (`SSet.realization_cylinder`),
  `Mathlib.Topology.CompactOpen` (`ContinuousMap.curry`, `ContinuousMap.uncurry`, the
  mathlib match for `lem-coef-compact-open-currying`), and
  `Sheaf.CategoryTheory.HomotopyEquivalenceWeak`
  (`SSet.Enhanced.homotopy_equivalence_weak`). Their relevant signatures and docstrings
  were inspected. None imports this new module, so these imports do not create a cycle.

Edge cases checked before writing: for the empty simplicial set, all three relevant
realizations/singular objects are empty, so the component map is the empty bijection
and the universal based assertion is vacuous. For disconnected simplicial sets, the
component conjunct remains present and every component's basepoints are quantified.
The first positive degree includes the possibly noncommutative fundamental group;
postcomposition preserves its multiplication order. The statement imposes no finiteness
or horn-filling restriction. All degenerate simplices use the existing adjunction and
therefore satisfy the characteristic-map formula without any separate choice.

Searches for existing declarations (using `msearch.py`, group Q124, this item):

- LeanFinder: "For every simplicial set the realization of the realization singular
  adjunction unit is a weak homotopy equivalence". Eight hits, including `sSetTopAdj`
  and homotopy-category/nerve adjunction units; none states the weak-equivalence result.
- Loogle: `"sSetTopAdj"`. Three hits: `sSetTopAdj`,
  `sSetTopAdj_unit_app_app_down`, and `sSetTopAdj_homEquiv_stdSimplex_zero`.
  The first constructs the adjunction, the second characterizes its unit, and the third
  is the degree-zero adjunction formula. None proves realization weak equivalence.
- LeanSearch: "The realization of the unit to the singular complex induces bijections
  on path components and homotopy groups". Eight hits, including `sSetTopAdj`,
  `SSet.toTop` and `TopCat.toSSet`; no theorem with the required conclusion.
- Mathlib grep: `(unit|weakEquivalence).*(toSSet|toTop|sSetTopAdj)|` followed by
  `(toSSet|toTop|sSetTopAdj).*(unit|weakEquivalence)`, in `AlgebraicTopology`.
  Eleven hits in `SingularSet`, `SingularHomology.Basic`, and `SimplicialSet.TopAdj`;
  these are formulas and uses of the adjunction. `SingularSet` explicitly lists the
  Quillen-equivalence statement as TODO. The relevant source was read in full.
- `rg` of the upstream `WeilConjectures` and project `lean/Sheaf` for `sSetTopAdj`,
  `singular.*unit`, `realization.*singular`, and `singular.*realization` found no
  matching theorem. Project hits were proof prose in `RealizationWeakEquivalence`,
  `RealizationFiniteLimits`, `KanRealizationMappingClasses`, and a distinct enriched
  coend adjunction in `PinchedRigidificationResolution`.
- Upstream grep for this node id returned no hits. Searches of upstream names and
  upstream/Mathlib/project source for `realization_singular_unit_weak` and
  `realizationSingularUnitWeak` returned no declaration-name collision.

No node faults or disputed statements were found. Compilation and dry-delivery results
are recorded below after validation.


Validation refreshed on 2026-10-17 UTC: the prescribed `scompile.py Q124
lem-cbc-realization-singular-unit-weak` compiled the delivered file cleanly as both
a sandbox module (1.9 seconds) and its library module (1.7 seconds), with no warnings
or errors. The Lean file has no lines over 100 characters. The sandbox node was
compared with the current shared node: only `lean` differs; its signature matches
the file verbatim. No maintenance repair note exists for this item.

The three required searches were rerun on 2026-10-17 using `msearch.py`:
LeanFinder returned eight adjunction or homotopy-category hits; Loogle returned the
same three `sSetTopAdj` declarations; Mathlib grep returned eleven adjunction-formula
hits. None states this theorem. Current upstream and project `rg` searches likewise
found no existing statement or declaration-name collision. The definition dependency
and the five proof-dependency source modules were reopened, including the full
signatures and docstrings. The statement and Lean module needed no changes.

The earlier attempt contained a second-reading section. It has been removed from
this worker report so that the dispatched second reader can supply the independent
reading of the current delivery. No delivery has been pushed. Dry-run results follow.

## Worker recheck

I reread the copied node statement and the theorem signature. The node's
single object is an arbitrary small simplicial set (X) in one fixed universe; this is
rendered by `(X : SSet.{u})`, with `autoImplicit false` and no extra typeclass or
inhabitance hypothesis. The node's singular construction is Mathlib's
`TopCat.toSSet`, whose degree-(n) simplices are continuous maps from the standard
real (n)-simplex; the module imports and uses that construction through
`sSetTopAdj`, rather than defining another singular set. The node's characteristic map
is the adjunction unit `sSetTopAdj.unit.app X`; the inspected unit formula gives the
classical map (t\mapsto[x,t]) on every simplex, including degenerate simplices.

The conclusion is rendered by exactly
`IsWeakHomotopyEquivalence (sSetTopAdj.unit.app X)`. Its first conjunct is the
`Function.Bijective` path-component map after realization. Its second conjunct has
`r : ℕ`, the hypothesis `1 ≤ r`, and every realization point `x`; it is the
`Function.Bijective` postcomposition map on the corresponding based homotopy group.
Thus the signature includes degree zero through components, every positive degree, and
all basepoints. The empty simplicial set makes both component functions empty
bijections and leaves the based quantifier vacuous; disconnected and non-Kan cases are
also included. The signature has no finiteness, connectedness, Kan, or nonemptiness
assumption, matching every explicit sentence of the node. No mismatch or correction
was found.


## Earlier second reading (a previous round; superseded)

Pending the independently dispatched second reader. The preceding worker recheck is
not an independent second reading. This worker has run only dry deliveries and has
not pushed a delivery.


## Second reading by Q124

Independent second reader, 2026-10-17. I opened the sandbox node and Lean module,
the current shared node, the statement-dependency node and its recorded module,
and the five recorded proof-dependency interfaces. I read the actual source pages
[Kerodon 0142](https://kerodon.net/tag/0142), Theorem the project server, and
[Kerodon 03X7](https://kerodon.net/tag/03X7), Corollary the project server.
This item has a Kerodon source, not a Stacks source. The theorem assumes only that
X is a simplicial set; the corollary identifies the simplicial and realized notions
of weak equivalence. There is no ambient Kan, connectedness, or finiteness hypothesis.

My object/hypothesis/conclusion inventory and its Lean rendering:

1. Fix a universe large enough for continuous-map sets; take every small simplicial
   set X. Lean has `universe u` and the sole binder `(X : SSet.{u})`, with
   `autoImplicit false`. `SSet.toTop.{u}` and `TopCat.toSSet.{u}` both remain in u;
   the standard real simplex is lifted by `SimplexCategory.toTop`. No extra universe
   equality, Small instance, or implicit object is assumed. Verdict: exact.
2. For a space T, Sing(T) has continuous maps from the real standard n-simplex,
   with affine precomposition operators. Lean uses `TopCat.toSSet`, reexported by
   `Sheaf.CategoryTheory.EnhancedDiagramsCones`. I read its restricted lifted Yoneda
   definition and `TopCat.toSSetObjEquiv`, and `SimplexCategory.toTop` in Mathlib's
   `TopologicalSimplex`. The equivalence removes only the harmless simplex lift;
   the maps are the coordinate-pushforward affine maps. This explanatory construction
   in the node introduces no additional quantified T in the theorem. Verdict: exact.
3. Realization is the dependency's quotient realization. Lean uses the existing
   `SSet.toTop`, its left Kan extension of topological simplices, rather than a new
   realization. I checked the dependency's node and declarations, including the
   weak-equivalence helpers listed alongside its main `coneCategory`. Verdict: exact.
4. The specified unit sends each x to the characteristic map t ↦ [x,t]. Lean uses
   exactly `sSetTopAdj.unit.app X`. I read `sSetTopAdj` and
   `sSetTopAdj_unit_app_app_down`: its degreewise value is
   `SSet.toTopSimplex.inv.app _ ≫ SSet.toTop.map (SSet.yonedaEquiv.symm a)`.
   Thus it is the characteristic map, with no arbitrary-map parameter. Verdict: exact.
5. The realized unit induces a bijection on path components. Unfolding the imported
   `IsWeakHomotopyEquivalence` gives the first conjunct
   `Function.Bijective (componentsMap (SSet.toTop.map f).hom)` at this unit.
   `componentsMap` is the quotient map on `ZerothHomotopy`, defined by mapping paths.
   Verdict: exact, including the component condition for disconnected spaces.
6. For every positive n and every basepoint of |X|, the induced based homotopy-group
   map is an isomorphism. The second conjunct is
   `∀ (r : ℕ), 1 ≤ r → ∀ (x : SSet.toTop.obj X),
   Function.Bijective (homotopyGroupMap (SSet.toTop.map f).hom r x)`.
   I read `homotopyGroupMap`: it postcomposes the continuous cube and descends through
   the homotopy relation relative to the entire boundary. Its target basepoint is
   the image of x. Postcomposition commutes with concatenation; consequently this
   bijectivity is exactly the required group-isomorphism assertion. The quantifier
   includes every realization point, not only vertices. Verdict: exact.
7. No Kan, finiteness, connectedness or nonemptiness assumption is imposed.
   The Lean theorem has no other binders or typeclass hypotheses. Verdict: exact.

Edge cases: the empty simplicial set has empty realization and singular complex,
so the component map is an empty bijection and the based assertion is vacuous.
A point/terminal simplicial set is included without extra choices. Disconnected,
non-Kan, and arbitrarily large small simplicial sets are included. Degree zero is
covered by path components, and r = 1 is included even when its group is
noncommutative. The possible opposite multiplication convention in Mathlib changes
neither preservation by postcomposition nor bijectivity. No ring characteristic,
scheme, or independent index set occurs in this statement.

Dependency check: the statement uses the recorded
`SSet.Enhanced.IsWeakHomotopyEquivalence` from EnhancedDiagramsCones, not a private
copy. I read the signatures and documentation of `SSet.realization_finite_limits`,
`SSet.kan_realization_serre` and `KanRealizationComparison`,
`SSet.realization_cylinder`, `ContinuousMap.curry`/`uncurry`, and
`SSet.Enhanced.homotopy_equivalence_weak`. They supply respectively the k-space
adjunction and simplex pairs, normalized Kan comparison, ordinary-product cylinder,
locally compact interval currying, and moving-basepoint homotopy equivalences.
They are ordinary proof imports as required. There are no new definition nodes,
dependency modules, statement corrections, or maintenance repair notes in this delivery.

Independent duplicate searches (msearch.py Q124, this item):

- LeanFinder: "The geometric realization adjunction unit induces a bijection of path
  connected components and all based homotopy groups without fibrancy assumptions".
  Eight hits: homotopy-group/component identifications and homotopy-category
  adjunctions, none asserting weak equivalence of this unit.
- Loogle: `"sSetTopAdj"`. Three hits: the adjunction, its characteristic-simplex
  formula, and the degree-zero hom-equivalence formula. I opened the adjunction
  and unit formula; none asserts this theorem.
- LeanSearch: "The adjunction unit from a simplicial set to singular simplices on
  its realization is a weak equivalence". Eight hits, including the adjunction,
  its general unit construction and toTopSimplex; none is the requested theorem.
- Mathlib grep: `sSetTopAdj|toSSet.*[Ww]eak|[Ww]eak.*toSSet`.
  Fourteen hits in SingularSet, SingularHomology.Basic and SimplicialSet.TopAdj;
  these concern the adjunction and its formulas, not weak equivalence.
- My upstream/project/name-index rg searches used `sSetTopAdj`, `Milnor`,
  `singular.*unit`, both orders of singular/realization, and both snake/camel
  spellings of the proposed declaration. No existing theorem or collision was found.
  I additionally opened InfinityCategoryOfSpaces: `singularRealization` is the
  existing composite, `singular_kan` is horn filling, and `topUnit_laws`/`topUnit`
  are enriched functor constructions; none states this weak-equivalence assertion.
  RealizationWeakEquivalence is a Kan-target detection criterion, also distinct.

No mismatch was found and no Lean or node change was needed. The module introduces
no definition, and its single theorem's entire proof is `sorry`. Its source/blueprint
docstrings and all eight proof steps agree with the node, including horn retractions,
representative/homotopy calculations, attached-interval transport and final cancellation.
The recorded `lean.statement` equals the file signature verbatim; only `lean` differs
from the shared node. All variables and universes are bound, and every line is at
most 100 characters.

Validation in this second reading: the prescribed scompile.py command compiled the
single delivered module as a sandbox (3.0 s) and as its library module (2.4 s), exit 0,
with no errors or warnings. Delivery preflight and push results follow below.

Second-reader dry delivery: deliver2.py --no-push returned exit 0 and
`OK (dry run): commit deb0ca1161 passes the preflight and compiles; nothing pushed`.
