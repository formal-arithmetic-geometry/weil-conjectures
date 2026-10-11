## Worker report

The module `lean/Sheaf/AlgebraicGeometry/HypercohomologyConvergence.lean` states the four assertions of lemma-weil-pbc-hypercohomology-convergence for each of the three specified couples. The declarations are `AlgebraicGeometry.Etale.hypercohomology_convergence_first`, `AlgebraicGeometry.Etale.hypercohomology_convergence_baseChange`, and `AlgebraicGeometry.Etale.hypercohomology_convergence_second`. Each proof is `by sorry`. No definitions or additional nodes are introduced.

Hypotheses, in each declaration:

- `X X' Y Y' : Scheme.{u}`, the four named arrows `f f' g g'`, and `sq : IsPullback g' f' f g` are the cartesian square. No properness, finiteness, characteristic, or nonemptiness assumption is added.
- `L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u+1})` is the given bounded-below derived object. `K : CochainComplex.Plus ...` and `e : DerivedCategory.Q.obj K.obj ≅ L.obj` are its chosen complex representative, as in def-weil-pbc-hypercohomology-filtrations.
- `hT` says that every cohomology sheaf of L is torsion, using the recorded `CategoryTheory.Sheaf.IsTorsion`.
- `a : ℤ` and `ha` express H^q(L)=0 for every integer q<a. `hterms` expresses that the chosen representative has zero terms below a; this is precisely the representative chosen in the definition dependency, rather than a restriction on which derived objects the theorem covers.
- `S` and `hS` simply name the exact couple: respectively `hypercohomologyCouple (hypercohomologyFirstFunctor f) K`, `hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K`, and `hypercohomologyCouple (hypercohomologySecondFunctor f' g') K`. The equality binder does not allow a different couple or assume convergence. It permits the rest of each signature to refer to the chosen couple without repeating its full expression.

Clauses, in their order in each signature:

1. Quadrant: the first conjunct is `q < a → IsZero (S.D p q)`. The second says `IsZero ((S.pageCouple r).E p q)` whenever `p<0 ∨ q<a`, for every r:ℕ. Since `pageCouple r` is actual page r+2, this includes E₂ and every later finite page. The existential `Z : S.LimitSubobjects` and the later `IsZero (S.pageInfinity Z p q)` clause give the infinite-page assertion as well.
2. Finitely many terms: a nonzero term on `p+q=n` entails `a ≤ q ∧ q ≤ n ∧ 0 ≤ p ∧ p ≤ n-a`. The following conjunct gives `Set.Finite` for that diagonal support and `Set.ncard ... ≤ (n-a+1).toNat`. The next conjunct separately says every term is zero if n<a. Taking the positive part of the count is the usual natural-number reading of “at most n-a+1, and none if n<a”; the explicit empty-degree conjunct covers the negative-bound case.
3. Stabilization: `max (q-a+1) p < (r:ℤ)+2` implies both `(S.pageCouple r).d p q = 0` and its `dInto` counterpart. The next conjunct identifies both tower subobjects at r with their value at `(max (q-a) (p-1)).toNat`, i.e. actual page `max (2, q-a+2, p+1)`. This is the node's r₀ on every potentially nonzero bidegree. Outside the quadrant E₂ and every subobject are zero; the first available page E₂ supplies the interpretation when the displayed integer r₀ is less than 2. `Z : S.LimitSubobjects` supplies the intersection of cycles and union of boundaries, not an arbitrary limiting page. `Nonempty (S.pageInfinity Z p q ≅ (S.pageCouple ...).E p q)` is equality of those pages up to isomorphism in the abelian category. The subsequent diagonal clause uses `(r:ℤ)+2 ≥ n-a+2` and identifies every such page with the infinite page.
4. Filtration and convergence: for each n, the image filtration `hypercohomologyFiltration (...) K n` is whole for p≤0 and has zero inclusion map for p≥n-a+1. A subobject has zero inclusion precisely when it is the zero subobject; this form avoids an expensive bottom-instance search and agrees with the dependency module. `IsFinite`, `IsExhaustive`, and `IsSeparated` express the three named properties. `BigradedExactCouple.IsInverseLimit` states the universal property of Hⁿ as the inverse limit of Hⁿ/Fᵖ, with existence included and no derived inverse-limit hypothesis. `S.IsRegular` and `S.IsComplete` are the recorded exact-couple predicates. `A : ∀n, S.AlphaColimit n`, `hA`, and the transport equation for `S.imageFiltration` identify the convergent alpha-colimit with the displayed cohomological abutment and precisely its recorded image filtration. `S.ConvergesTo Z A` is the full recorded convergence predicate. The last conjunct gives E∞ ≅ FᵖH^(p+q)/F^(p+1)H^(p+q) through `gradedPiece`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`: `CategoryTheory.hypercohomologyCouple`, `hypercohomologyFiltration`; `AlgebraicGeometry.Etale.hypercohomologyFirstFunctor`, `hypercohomologyBaseChangeFunctor`, `hypercohomologySecondFunctor`. The existing `hypercohomologyFiltrations_spec` covers some conclusions, but does not state the D bound, explicit stabilization bounds and cycle/boundary constancy, cardinal bound, or all four clauses of this node. It therefore is not an exact existing declaration for this item.
- `Sheaf.CategoryTheory.ExactCouple`: `CategoryTheory.BigradedExactCouple`, `pageCouple`, `d`, `dInto`. The initial couple is type 0; pageCouple is indexed by actual page minus two.
- `Sheaf.CategoryTheory.ExactCoupleConvergence`: `cycleBoundaryTower`, `LimitSubobjects`, `pageInfinity`, `AlphaColimit`, `imageFiltration`, `IsRegular`, `IsComplete`, `IsInverseLimit`, `ConvergesTo`.
- `Sheaf.CategoryTheory.Filtration`: `CategoryTheory.DecreasingFiltration` and its `step`, `IsFinite`, `IsExhaustive`, `IsSeparated`, `gradedPiece`.

All are imported through the first dependency's module, which already imports the other three. No private copies, file-local notation, or file-local instances are used. All variables and universe u are bound explicitly.

Edge cases checked: the zero complex and empty schemes; a any integer, including negative; n<a (the entire diagonal and abutment vanish, so the top and zero filtration ranges can overlap); n=a (only (0,a), stable at actual page 2); p<0 or q<a (all finite and infinite entries zero, including when integer r₀<2); boundary p=0 or q=a; negative n-a+1 (the natural cardinal bound is zero); and arbitrary scheme universe u. There is no inverse-limit existence assumption or finiteness bound on the whole cohomological range.

Searches for an existing statement:

- `msearch.py ... leansearch "hypercohomology spectral sequence finite filtration convergence"`: service unavailable (Internal Server Error), recorded as unavailable.
- `msearch.py ... leanfinder "hypercohomology spectral sequence first quadrant finite filtration convergence stabilization"`: eight results, chiefly `DerivedCategory.isZero_of_isLE`, `isZero_of_isGE`, cochain-complex vanishing and factorization facts; no matching convergence statement.
- `msearch.py ... loogle "CategoryTheory.BigradedExactCouple.page, CategoryTheory.BigradedExactCouple.ConvergesTo"`: zero hits, unknown project identifier.
- `msearch.py ... grep "converge|abutment|pageInfinity" Algebra/Homology`: three docstring hits in Mathlib/Algebra/Homology/SpectralObject/HasSpectralSequence.lean, lines 393, 435, 436, no exact-couple convergence statement.
- `rg` for `hypercohomology|HalfPlane|half_plane` in WeilConjectures and lean/Sheaf: related half-plane convergence and the dependency module, no identical theorem. `grep -rn` of the item ID in WeilConjectures finds only the compact-support Leray-filtration docstring in DeligneLaumon/Reduction/FormalSteps.lean; its signature is a different filtration-existence assertion for Weil sheaves, not this node.
- `rg` of the three proposed declaration names in Mathlib, WeilConjectures and lean/Sheaf found no collisions. `tools/lean_names_upstream.py show` was consulted; no attachment for this item supplies its statement.

The blueprint source file is absent from this read-only machine's literature checkout. Its imported statement and proof steps, and the imported `blueprint_sketch` in the node, were read. The public primary-source pages [Stacks 015J](https://stacks.math.columbia.edu/tag/015J) and [Stacks 0BDV](https://stacks.math.columbia.edu/tag/0BDV) were opened: they support finite convergence of bounded-below hypercohomology and cycle/boundary stabilization, respectively. A request for the blueprint's pinned raw file failed to fetch. No statement correction or disputed mathematical assertion is needed; the index translation above is explicit.

Validation: server single-file compile succeeded, exit code 0, in 2.8 seconds, with no warnings. The first attempt failed only at synthesis of the bottom subobject; the zero-inclusion formulation corrected it without changing the claim. Delivery dry run is run after writing this report; the second reader supplies the independent second-reading section.

## Second reading by F1

I read the item node, its source place (blueprint order 1316, with the cited
Stacks convergence lemmas 05TC, 015J, 0BDV and 012W), and all four statement
dependencies.  The node introduces a cartesian square
`X -f-> Y`, `X' -f'-> Y'`, `g : Y' ⟶ Y`, `g' : X' ⟶ X`, then a bounded-below
complex representative `K`, derived object `L`, comparison isomorphism `e`,
torsion cohomology, lower bound `a` (both for cohomology and the representative),
and one of the three named exact couples.  Its four conclusion groups are:

* the `D` and all finite/infinite pages vanish in the lower/negative quadrant;
* on each diagonal, nonzero terms lie in `a ≤ q ≤ n`, `0 ≤ p ≤ n-a`, with the
  finite cardinal bound and total vanishing for `n < a`;
* the stated differential bound, cycle/boundary tower stabilization, existence
  of the limit page, and diagonal page stabilization;
* the explicit finite/exhaustive/separated filtration bounds, inverse-limit
  property, regularity/completeness, convergence data, image-filtration
  identification, and associated-graded comparison.

The three Lean declarations render these objects and clauses exactly.  In
`hypercohomology_convergence_first`, `baseChange`, and `second`, `f`, `f'`, `g`,
`g'`, and `sq` render the square; `K`, `L`, `e`, `hT`, `a`, `ha`, and `hterms`
render the representative and hypotheses; `S` and `hS` select respectively
`hypercohomologyFirstFunctor f`, `hypercohomologyBaseChangeFunctor f g`, and
`hypercohomologySecondFunctor f' g'`.  The conjunctions render the four groups
in the node's order.  `pageCouple r` is the actual page `r+2`, so the Lean
condition `max (q-a+1) p < (r : ℤ)+2` is precisely the node's `r > max(...)`,
and `.toNat` in the tower and infinity clauses gives the node's
`max(q-a+2,p+1)` page.  The zero-arrow formulation of the upper filtration
bound is definitionally the zero subobject and avoids requiring a bottom
instance; it has the same meaning as `F^p = 0`.

No hypothesis is stronger than the node's square, bounded-below/torsion
assumptions, and specified couples, and no extra finiteness, properness,
characteristic, nonemptiness, or universe restriction is present.  The edge
cases `K=0`, empty schemes, negative `a` or `n`, `n<a`, `n=a`, `p=0`, `q=a`,
negative page-index expression before the actual page 2, and arbitrary `u`
are covered by the explicit inequalities and `toNat` convention.  The
zero-inclusion upper bound also covers the overlap when `n<a`.

I searched Mathlib spectral-sequence/exact-couple files, the source
`WeilConjectures/`, and `lean/Sheaf/` (including LeanSearch, LeanFinder/Loogle,
and grep searches).  They contain no exact-couple convergence declaration;
the nearby hypercohomology filtration declaration is not this statement.
There are no new definition or dependency modules and no statement correction.
The module compiles cleanly with `scompile.py` (exit code 0, no warnings), and
the node's recorded `lean.statement` remains verbatim equal to the first
declaration signature.
