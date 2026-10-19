## Worker report

The module `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension`
states `AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed`.
Its sole theorem has proof `by sorry`; no definitions or proofs were added.
The node is unchanged except for its `lean` record.

Hypothesis and conclusion correspondence:

- “Let K be a field” is `(K : Type u) [Field K]`, with the universe explicitly bound.
- “Separably closed” is `[IsSepClosed K]`, not algebraically closed or perfect.
- “Spec K” is `Spec (.of K)`.
- “cd_tor(K) ≤ 0 in the sense of def-sc-etale-torsion-cd” is precisely
  `HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) 0`.
- “For every torsion étale sheaf F” expands by that recorded predicate to
  `∀ F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}, F.IsTorsion → …`.
  `Sheaf.IsTorsion` asks that each local section become finite-order on a covering sieve;
  there is no uniform annihilator or coefficient ring.
- “Every q > 0” expands to `∀ q : ℕ, 0 < q → …`. These are all positive integer degrees;
  no assertion in degree zero or negative degree is added.
- “H^q(Spec K,F) = 0” expands to `Subsingleton` of
  `(AlgebraicGeometry.Etale.cohomology AddCommGrpCat.{u + 1} (Spec (.of K)) q).obj
  ((DerivedCategory.singleFunctor _ 0).obj F)`, the ordinary derived-section group.
  Vanishing of this abelian group is exactly subsingletonness.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`:
  `AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`, recorded by
  `def-weil-pbc-etale-sheaves`: the relevant notion is `CategoryTheory.Sheaf.IsTorsion`
  from `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
  Its full definition was read there. The upstream EtaleSheaves module is absent in
  this machine's source snapshot; the predicate's public dependency is available on
  the server, as confirmed by compilation. The repository's older
  `Sheaf.AlgebraicGeometry.EtaleSheaves` was also read; no duplicate was introduced.
- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and the jointly-surjective-cover signature
  `ofArrows_mem_smallEtaleTopology_iff`, through the cohomological-dimension import.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology` and `rightDerivedGlobalSections`, through the same import.
- Proof imports (ordinary, not public), as required by stage 2:
  `Sheaf.AlgebraicGeometry.AbelianSheavesGModules`, declaration
  `AlgebraicGeometry.Scheme.abelianSheaves_equiv_discreteGModules`, and
  `Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants`, declaration
  `AlgebraicGeometry.Scheme.fieldSections_stalkInvariants`.
  Their signatures and docstrings were read. The proof steps are reproduced in the theorem
  docstring: additive equivalence, sections as trivial-group invariants, exact-resolution
  computation. The remaining proof dependencies are already imported by the dimension module.

Edge cases checked: degree zero is correctly excluded (nonzero constant torsion sheaves can
have nonzero sections); all positive degrees are included. The zero sheaf is included.
Arbitrary torsion groups such as Q/Z need no common annihilator. Infinite disjoint unions
in the site impose no sectionwise torsion restriction. Positive characteristic and imperfect
separably closed fields are included, since `IsSepClosed` imposes neither perfection nor
algebraic closedness. No finiteness or finite-coefficient restriction was introduced.

Searches made using msearch.py (2026-10-15):

- LeanFinder: `torsion etale cohomology of a separably closed field vanishes in positive degrees`:
  eight hits, on formally étale algebras and Hilbert 90, none an exact match.
- Loogle: `IsSepClosed, Subsingleton`: zero hits.
- LeanSearch: `higher etale cohomology separably closed field vanishes`:
  unavailable, Internal Server Error.
- Mathlib grep: `HasTorsionEtaleCohomologicalDimensionLE|subsingleton_H_of_isSepClosed|cohomology.*isSepClosed`:
  zero hits.
- Source and project rg: the item id and the dimension predicate, and searches for
  `separably.closed|isSepClosed|IsSepClosed` in Sites directories. Read
  `WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport.Scheme.subsingleton_H_of_isSepClosed`
  (declaration full name `AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed`):
  this gives Ext-based `Sheaf.H H (n + 1)` vanishing for all abelian sheaves, not the recorded
  ordinary derived-section predicate. The node `def-weil-pbc-etale-cohomology` explicitly
  distinguishes these APIs and leaves their comparison to stage 3. Therefore this is not an
  exact existing declaration for this item. PointCohomology also only supplies Ext results.
  Project search found the bound definition but no separably-closed bound theorem.
- Name search in `dag/lean_names_upstream.json`, Mathlib and the project found no collision
  for the new theorem name.

Validation: scompile.py compiled the module cleanly on the server (nice 19, two threads,
60 seconds per file). The dependency overlay and item each compiled separately; no local
Lean command was run. No statement correction, disputed statement, new node, or dependency
replacement was needed.

## Second reading by NG

I independently opened the item node, its blueprint source, Stacks etale-cohomology.tex
at Tags 04JQ (`lemma-equivalence-abelian-sheaves-point`) and 04JM
(`lemma-global-sections-point`), the sandbox module, and the recorded dependency
signatures. The source assumes a field and a geometric point, with its absolute Galois
group; it assumes no perfection, finite coefficients, or characteristic restriction.
A geometric point and algebraic closure are auxiliary choices in the proof, not extra
hypotheses of the node. The blueprint's arbitrary abelian-sheaf argument agrees with
the node's torsion specialization.

Object/hypothesis/conclusion checklist (H3):

- Object K, an arbitrary field: `(K : Type u) [Field K]`. Exact; `universe u` is bound.
- Hypothesis K separably closed: `[IsSepClosed K]`. Exact; no algebraic-closedness,
  perfection, finiteness, or coefficient-order condition is assumed.
- Scheme Spec K: `Spec (.of K)`. Exact affine spectrum, not a geometric fibre or
  an arbitrarily supplied scheme.
- Bound cd_tor(K) <= 0: `HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) 0`.
  Exact use of the declaration recorded by `def-sc-etale-torsion-cd` in
  `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`; I opened its body.
- Every torsion abelian etale sheaf F: that predicate expands to
  `∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}), F.IsTorsion → ...`.
  Exact category and quantifier. I read the recorded `CategoryTheory.Sheaf.IsTorsion`
  in upstream `Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean` under
  WeilConjectures: every section restricts to finite additive order on a covering
  sieve. This is local torsion, not a common annihilator or sectionwise torsion.
- Small etale site: Mathlib's recorded `Scheme.smallEtaleTopology`; its body and
  `ofArrows_mem_smallEtaleTopology_iff` give schemes etale over X and jointly
  surjective coverings. Exact; no restricted finite etale subsite is substituted.
- Every positive degree q: the bound expands to `∀ (q : ℕ), 0 < q → ...`.
  Exact order after the sheaf and torsion hypothesis; all positive integer degrees
  are natural degrees, so no positive integer case is lost.
- Vanishing H^q(Spec K,F): `Subsingleton ((Etale.cohomology
  AddCommGrpCat.{u + 1} X q).obj ((DerivedCategory.singleFunctor _ 0).obj F))`.
  Exact zero abelian group. I opened upstream LowerShriek: `cohomology` is
  `rightDerivedGlobalSections ... ⋙ DerivedCategory.homologyFunctor ...`, and
  `rightDerivedGlobalSections` is `R(Sheaf.Γ ...)`. This is the required ordinary
  derived-section cohomology of F in degree zero, not compact supports or Ext.

I also opened `abelianSheaves_equiv_discreteGModules` and
`fieldSections_stalkInvariants` in their imported project modules. The former
provides the abelian-group-valued stalk comparison for all abelian sheaves and
arbitrary separable closure; the latter identifies sections over finite separable
intermediate fields with invariant germs and gives naturality. Taking Ks = K and
L = K is permitted. Their larger coefficient universes include the dimension
predicate's `u + 1` choice. The theorem docstring reproduces all three proof steps:
additive stalk equivalence with trivial Galois group, sections as its invariants,
and exactness giving vanishing via a resolution. All recorded proof dependencies
have imports, directly or through the dimension module.

Edge cases: q = 0 is excluded exactly as required; the zero sheaf is included.
There is no integer n or coefficient-ring parameter whose zero case could be lost.
Arbitrary locally torsion groups, including Q/Z without bounded annihilator, are
included. Infinite disjoint unions and the empty object of the site are governed
by the full sheaf topology, not finite-cover or sectionwise-torsion conditions.
Spec of a field is nonempty, so an empty base scheme is not a node case. Positive
characteristic, p-primary torsion, and imperfect separably closed fields remain
included. There is no index-set binder or independent small test universe; K is
universe-polymorphic and the sheaf universe is exactly the recorded dependency's.

Independent H4 searches (2026-10-15): msearch LeanFinder query
`exact global sections etale sheaf separably closed field` returned eight algebraic
etale/formally-etale results, none this statement; msearch Loogle query
`IsSepClosed, "cohomology"` returned zero hits. The worker's LeanSearch service
failure is recorded above. I additionally used rg on upstream WeilConjectures,
Mathlib, and project lean/Sheaf for `subsingleton_H_of_isSepClosed`, both orders of
cohomology/isSepClosed, and both orders of SepClosed/vanish, and searched the Sites
folders for separably-closed variants. I opened upstream FiniteSupport's
`Scheme.subsingleton_H_of_isSepClosed`: it concludes `Subsingleton (Sheaf.H H (n + 1))`,
for Ext-defined `Sheaf.H`, not this dependency's derived-section object. Upstream
Sites/CohomologicalDimension likewise uses `Sheaf.H`; its related bounds are not
an existing exact declaration for this item. This confirms the worker's distinction;
the cohomology comparison is a stage-3 task. The full proposed declaration name
has no collision in dag/lean_names_upstream.json, Mathlib, upstream or lean/Sheaf.
No new definition node or dependency replacement is necessary.

No mathematical or signature mismatch found; no Lean or node changes made.
The module has one named theorem with sole proof `sorry`, no data definitions,
private copies, file-local notation or instances. Its module and theorem docstrings
name the source and blueprint id. The node's `lean.statement` is verbatim the
signature before `:=`; all variables and universes are explicitly bound.
Server-only scompile.py passed cleanly: the dimension overlay and the item each
compiled separately (1.3 s and 1.5 s), nice 19, two threads, 60-second per-file limit.
