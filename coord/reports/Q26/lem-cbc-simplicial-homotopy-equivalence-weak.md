## Worker report

The module `Sheaf.CategoryTheory.SimplicialHomotopyEquivalenceWeak` states
`SSet.Enhanced.simplicial_homotopy_equivalence_weak`. Its only theorem has proof
`sorry`, and its docstring contains all six DAG proof steps. It introduces no new
definition. Only the item's `lean` field changes; its mathematical statement,
statement dependencies and proof dependencies remain unchanged.

Hypotheses and conclusion, clause by clause:

- Small simplicial sets: `{A B : SSet.{u}}`, for an explicitly declared arbitrary
  universe `u`, using the dependency's Mathlib model.
- The node's `u : A → B` and `v : B → A` are named `(f : A ⟶ B)` and
  `(g : B ⟶ A)` so that `u` remains the universe name. These are actual natural
  transformations of simplicial sets.
- The cylinder maps are `(H : A ⊗ Δ[1] ⟶ A)` and
  `(J : B ⊗ Δ[1] ⟶ B)`. Mathlib's cartesian monoidal tensor on `SSet` is the
  degreewise product: the object in each degree is a pair and each simplicial
  operator acts on the two coordinates.
- Endpoint restriction is precomposition with the existing `SSet.ι₀` or
  `SSet.ι₁`. Their definitions are the cartesian lift of the identity and the
  constant zero or constant one vertex of the standard one-simplex.
- For `H`, hypothesis `hH` is the disjunction of
  `(SSet.ι₀ ≫ H = f ≫ g ∧ SSet.ι₁ ≫ H = 𝟙 A)` and
  `(SSet.ι₀ ≫ H = 𝟙 A ∧ SSet.ι₁ ≫ H = f ≫ g)`.
  Category-theoretic `f ≫ g` means the node's `vu`.
- Independently for `J`, hypothesis `hJ` is the disjunction of
  `(SSet.ι₀ ≫ J = g ≫ f ∧ SSet.ι₁ ≫ J = 𝟙 B)` and
  `(SSet.ι₀ ≫ J = 𝟙 B ∧ SSet.ι₁ ≫ J = g ≫ f)`.
  Thus both same-order cases and both mixed-order cases are included.
- The conclusion is the dependency's existing
  `SSet.Enhanced.IsWeakHomotopyEquivalence f`, not a model-category weak
  equivalence. Its definition is exactly the conjunction of bijectivity of
  `componentsMap (SSet.toTop.map f).hom` and, for every `r : ℕ` with `1 ≤ r`
  and every `x : SSet.toTop.obj A`, bijectivity of
  `homotopyGroupMap (SSet.toTop.map f).hom r x`.
- `componentsMap` uses Mathlib's path-component quotient `ZerothHomotopy`.
  `homotopyGroupMap` is postcomposition on boundary-relative cubical homotopy
  classes `HomotopyGroup (Fin r)`, based at `x` and its actual image. As noted
  in the dependency's docstring, postcomposition preserves concatenation, so
  bijectivity is precisely the asserted group-isomorphism condition.
- There is no Kan, quasicategory, connectedness, nonemptiness, or stationary
  basepoint assumption. No extra datum or conclusion was added.

Dependency declarations read and used:

- Statement dependency `def-cbc-enhanced-diagrams-cones`:
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, particularly
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, `componentsMap`, and
  `homotopyGroupMap`. Their complete definitions and docstrings were read.
  Its realization is the existing `SSet.toTop`, imported there from
  `Mathlib.AlgebraicTopology.SingularSet`.
- Existing standard simplex, degreewise product and endpoint inclusions:
  `Mathlib.AlgebraicTopology.SimplicialSet.Monoidal`, including `SSet.ι₀` and
  `SSet.ι₁`, available through the public statement-dependency import. Read
  both definitions, endpoint computation lemmas and degreewise tensor formulas.
- Proof dependency `lem-cbc-quotient-cylinder-continuity` is a Mathlib leaf:
  `Topology.IsQuotientMap.continuous_lift_prod_left` in
  `Mathlib.Topology.CompactOpen`. Read its full signature, including the
  ambient topological-space variables and `[LocallyCompactSpace Y]`.
  Imported without `public`, for the future proof.
- Proof dependency `lem-coef-homotopy-equivalence-weak`:
  `Sheaf.CategoryTheory.HomotopyEquivalenceWeak`, declaration
  `SSet.Enhanced.homotopy_equivalence_weak`. Read its full signature and
  docstring; imported without `public`. It allows moving basepoints and
  arbitrary empty or disconnected topological spaces.

Edge cases checked before writing:

- If `A` or `B` is empty, existence of maps both ways forces both empty.
  The component map is then an empty bijection, and the based conditions have
  no source points. No typeclass excludes this case.
- All four pairs of endpoint orientations are included, including the two
  mixed cases; no simplicial interval reversal is presumed to exist.
  Reversal occurs only after realizing the homotopies, as in the DAG proof.
- Non-Kan simplicial sets, such as standard simplices, remain admissible.
- Degree zero is covered by the separate component clause; group degrees
  are exactly positive integers, represented by naturals satisfying `1 ≤ r`.
- Basepoints range over every point of the realization, not merely vertices.
  Homotopies need not hold a basepoint fixed.
- The arbitrary universe is explicitly bound and both simplicial sets use the
  dependency's single small universe. All object and map variables are bound,
  and `set_option autoImplicit false` is set in the module.

Searches made (all msearch queries use group Q26 and this item; the sandbox
`searches.jsonl` records their raw results):

1. LeanFinder: `A simplicial map with a two-sided inverse up to simplicial
   cylinder homotopy is a weak homotopy equivalence after geometric realization`.
   Eight hits, including `HomotopicalAlgebra.Cylinder.LeftHomotopy.weakEquivalence_iff`
   and generic cylinder inclusions. Read `LeftHomotopy.lean` around lines
   120–145: they require an already supplied weak-equivalence structure and a
   cylinder satisfying it. They do not supply the realization-based theorem.
2. Loogle: `SSet.toTop, ContinuousMap.HomotopyEquiv`. Zero hits.
3. msearch grep: `realiz.*homotop|homotop.*realiz|toTop.*[Hh]omotopy`,
   subdirectory `AlgebraicTopology`. Zero hits.
4. LeanSearch: `Simplicial homotopy equivalences become weak homotopy
   equivalences after geometric realization`. Eight hits: realization and its
   adjunction, simply connected homotopy invariance, generic localization,
   cofibrations, and relative homotopy constructor injectivity. Read
   `SingularSet.lean` lines 60–105, `Topology/Homotopy/Equiv.lean` lines 38–60,
   and the cofibration module header: none is the theorem at hand.
5. Direct `rg` in `WeilConjectures/` for the item id and for
   `simplicial_homotopy_equivalence_weak|homotopy_equivalence_weak|[Hh]omotopy.*[Ww]eak|[Ww]eak.*[Hh]omotopy`
   found no upstream declaration. The exact proposed declaration/module names
   were also searched in Mathlib, upstream sources, `lean/Sheaf`, and
   `dag/lean_names_upstream.json`, with no conflict.
6. Direct `rg` of `lean/Sheaf/CategoryTheory` for homotopy/weak-equivalence and
   endpoint patterns found the supplied definition module and the topological
   proof dependency, plus specialized results concerning nerves, mapping spaces,
   Kan conditions or hammock constructions. None states this arbitrary
   simplicial-cylinder implication. Read the relevant supplied definitions.

Source check: opened Kerodon Construction the project server (0148) online. It realizes a
simplex of the simplicial function object as a continuous family of maps,
compatibly with faces and degeneracies; its one-simplex case is exactly the
realization-homotopy input used here. Requests for 00UB timed out, so I do not
claim a fresh reading of that page. The detailed prism, quotient continuity,
endpoint reversal and topological weak-equivalence steps are taken from the
item's complete recorded proof and reproduced in the theorem docstring.

No statement dispute, correction, missing notion or unusable dependency was found.
No dependency module or new node is needed.

Validation: prescribed `scompile.py Q26 lem-cbc-simplicial-homotopy-equivalence-weak`
on the delivered file completed cleanly, with no errors or warnings. No global
build or direct compilation was run. The only postponed proof is
`SSet.Enhanced.simplicial_homotopy_equivalence_weak`.

## Second reading by Q26

I independently opened the node copy, its source place, the dependency declaration, and
`Sheaf/CategoryTheory/SimplicialHomotopyEquivalenceWeak.lean`.

- The node introduces small simplicial sets `A` and `B`; Lean renders these as
  `{A B : SSet.{u}}` with one explicitly bound universe `u`. Verdict: exact, with no
  universe restriction beyond the node's small simplicial sets.
- The node's maps `u : A → B` and `v : B → A` render as `(f : A ⟶ B)` and
  `(g : B ⟶ A)`. Verdict: exact simplicial maps, with composition order represented by
  Lean's `≫`.
- The node's first cylinder map `H : A × Δ¹ → A` renders as
  `H : A ⊗ Δ[1] ⟶ A`, and the second `J : B × Δ¹ → B` as
  `J : B ⊗ Δ[1] ⟶ B`. Verdict: exact degreewise cartesian products from Mathlib's
  simplicial monoidal structure.
- For `H`, the two endpoint restrictions render as the disjunction
  `ι₀ ≫ H = f ≫ g ∧ ι₁ ≫ H = 𝟙 A` or
  `ι₀ ≫ H = 𝟙 A ∧ ι₁ ≫ H = f ≫ g`. Verdict: both endpoint orders are present,
  independently of the corresponding disjunction for `J`.
- For `J`, the endpoint restrictions render as
  `ι₀ ≫ J = g ≫ f ∧ ι₁ ≫ J = 𝟙 B` or
  `ι₀ ≫ J = 𝟙 B ∧ ι₁ ≫ J = g ≫ f`. Verdict: exact and independent; no orientation
  was silently fixed.
- The conclusion renders as `SSet.Enhanced.IsWeakHomotopyEquivalence f`, using the
  dependency's exact realization definition: bijectivity on path components and, for
  every `r : ℕ` with `1 ≤ r` and every realization basepoint, bijectivity of the
  induced based homotopy-group map. Verdict: exact; no Kan, connectedness,
  nonemptiness, or stationary-basepoint hypothesis was added.

The dependency `def-cbc-enhanced-diagrams-cones` was checked at its declaration and its
`IsWeakHomotopyEquivalence`, `componentsMap`, and `homotopyGroupMap` definitions. The
Mathlib `SSet.ι₀`, `SSet.ι₁`, tensor, and standard simplex declarations were checked in
`AlgebraicTopology/SimplicialSet/Monoidal.lean`. The proof-only dependencies are imported
without restating them: `Topology.IsQuotientMap.continuous_lift_prod_left` and
`SSet.Enhanced.homotopy_equivalence_weak`.

Edge cases checked: empty `A` or `B` (the two maps force both empty, yielding the empty
component bijection and no source basepoints), the initial simplicial set (there is no
zero object in simplicial sets), arbitrary
(non-Kan) simplicial sets, both mixed endpoint orientations, degree `r = 0` excluded by
`1 ≤ r` while components are handled separately, every realization point as a basepoint,
and the single explicitly bound universe. No characteristic, finiteness, or nonemptiness
assumption occurs in the node or file.

Searches for an existing notion or theorem were repeated with LeanFinder and Loogle via
`msearch.py`, direct `rg` over Mathlib, `WeilConjectures/`, and `lean/Sheaf/`, and the
upstream-name index. Hits were generic model-category cylinder/weak-equivalence facts,
standard simplex realization maps, and homotopy-group utilities; none states this
realization theorem for arbitrary simplicial cylinder maps. The dependency declaration is
the sole project definition of the weak-equivalence predicate. Therefore no `existing`
record, new node, or dependency repair is needed.

No mismatch was found and no source or Lean change was necessary. The module compiled
cleanly with the prescribed `scompile.py`; its only postponed proof is the node theorem.


Independent source verification: fetched and read Kerodon 00UB directly after the web
fetch timed out. Its forward assertion is for arbitrary simplicial sets; the Kan
hypothesis belongs only to the converse. Read 0148 online: its realization construction
starts with arbitrary simplicial sets `X,Y` and maps `Δⁿ × X → Y`, and is compatible
with face and degeneracy operators. Thus its `n = 1` case provides the cylinder input
without additional global hypotheses. This source is Kerodon, not Stacks.

Fresh independent queries were:
- LeanFinder: `A map of simplicial sets with a two sided inverse modulo cylinder
  homotopy becomes a homotopy equivalence of topological realizations` (8 hits).
  Read `LeftHomotopy.lean`: the relevant `weakEquivalence_iff` assumes a specified
  `CategoryWithWeakEquivalences` and a cylinder for it; it does not establish the
  realization weak-equivalence structure. Homeomorphism hits start with a topological
  homeomorphism, which is different input.
- Loogle: `SSet.toTop, Homotopy` (0 hits).
- Direct `rg`: `toTop.*[Hh]omotop|[Hh]omotop.*toTop|[Rr]ealiz.*[Hh]omotop|` followed
  by `[Hh]omotop.*[Rr]ealiz|simplicial_homotopy_equivalence_weak` over the upstream
  project, Mathlib AlgebraicTopology, this project's CategoryTheory, and the upstream
  name index. The nerve natural-transformation theorem was opened: it is restricted
  to nerves of ordinary categories and natural-transformation zigzags. The Kan mapping
  results require Kan targets and concern mapping sets. None is this theorem.

The node's `lean.statement` was checked verbatim against the complete theorem signature;
all terms and the universe are explicitly bound. The module contains no definition or
extra theorem, and its source/blueprint docstring reproduces all six proof steps. The
second reading changes only this report.
