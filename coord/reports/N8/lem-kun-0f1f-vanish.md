## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedPointSupportVanishing` states
`AlgebraicGeometry.Etale.isZero_cohomology_of_support_subset_closedPoints`.
Its only theorem has proof `sorry`; no definitions or proofs were added.

Source read: [Stacks Project, Tag 0F1F](https://stacks.math.columbia.edu/tag/0F1F),
Lemma 59.97.3, first assertion and its proof. The source also asserts global generation;
this node explicitly contains only the first assertion. The statement is unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A field `K`: `{K : Type u} [Field K]`.
- `K` separably closed: `[IsSepClosed K]`, the recorded Mathlib notion.
- A scheme `X` over `K`: `(X : Scheme.{u}) [X.Over (Spec (.of K))]`.
  The structure map is `X ↘ Spec (.of K)`.
- Finite type over `K`: `[LocallyOfFiniteType (X ↘ Spec (.of K))]` and
  `[QuasiCompact (X ↘ Spec (.of K))]`, exactly the recorded conjunction.
- An arbitrary abelian sheaf on the small étale site:
  `(F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`.
- Support contained in closed points:
  `(hF : Scheme.etaleSheafSupport F ⊆ closedPoints X)`.
  The existing support uses a nonzero geometric stalk over the underlying point;
  `closedPoints X` is the set of points whose singleton is closed.
- Each degree `q > 0`: `(q : ℕ) (hq : 0 < q)`.
- The conclusion `H^q(X_et,F) = 0` is `IsZero` of the abelian-group object
  `(Etale.cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).obj
  ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  0).obj F)`. This is the precise sheaf-in-degree-zero interpretation in the
  recorded cohomology dependency. The degree cast changes only the indexing type.

Dependency declarations used, with source signatures/docstrings read:

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`.
- `Mathlib.AlgebraicGeometry.Over`: `AlgebraicGeometry.Scheme.Over` and its
  structure map; the mathlib_match is the dependency interface.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the recorded abelian sheaf
  category is `CategoryTheory.Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`;
  `Sheaf` itself is Mathlib's full subcategory of sheaf presheaves.
- `Sheaf.AlgebraicGeometry.EtaleSupport`:
  `AlgebraicGeometry.Scheme.etaleSheafSupport`, together with the existing
  `closedPoints` appearing in that dependency's record.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology` and `rightDerivedGlobalSections`.
  The latter is the total right-derived global sections functor; the former
  composes it with the degree-indexed derived homology functor.

All recorded proof dependencies with modules are imported non-publicly, including
`ClosedPointSheafApproximation`, `EtaleClosedImmersionEssentialImage`,
`ClosedPointField`, `FiniteSupport`, `FiniteCoproductCohomologyAssembly`,
`WeilConjectures.SixFunctors.Finite.Exact`, `LerayBounded`, and the upstream
filtered-colimit cohomology module. Mathlib proof leaves import `Noetherian`,
`Properties`, `ClosedImmersion`, `ResidueField`, and `Finite`.
The theorem docstring gives each of the seven DAG proof steps and its node citations.

Edge cases checked: `q = 0` is deliberately excluded, since a nonzero skyscraper
has nonzero global sections; every positive natural degree is included. The empty
scheme, the zero sheaf, and empty support are allowed. Support need not be finite,
and no torsion, constructibility, smoothness, separatedness, characteristic, or
nonemptiness assumption was introduced. Finite purely inseparable residue extensions
of a nonperfect separably closed base field remain allowed. Universes follow the
recorded support and cohomology interfaces: `Scheme.{u}` and abelian groups in `u+1`;
all binders and universes are explicit and auto-implicit elaboration is disabled by
the project options.

Searches run for this item:

- `msearch.py N8 lem-kun-0f1f-vanish leanfinder` with query
  `Higher etale cohomology vanishes for an abelian sheaf supported on closed points over a separably closed field`:
  eight hits on formal étaleness and cotangent cohomology, no matching theorem.
- `msearch.py ... loogle '"cohomology", "support"'`: zero hits.
- `msearch.py ... grep 'support.*closed|closed.*support|cohomology.*vanish' AlgebraicGeometry`:
  fourteen hits about ideal-sheaf support, no matching theorem.
- `msearch.py ... leansearch` with query
  `Higher etale cohomology vanishes for abelian sheaves supported on closed points over a separably closed field`:
  service unavailable (Internal Server Error); this is not a negative search result.
- `rg` in upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, by the node ID, support/cohomology phrases,
  `etaleSheafSupport`, and the proposed declaration name: no exact existing statement.
  The close upstream result in `WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport`,
  `AlgebraicGeometry.Etale.subsingleton_H_of_isZero_upperStar`, was read in full:
  it requires a finite closed complement with separably closed residue fields and
  vanishing restriction there, so it is a tool for finite support, not this theorem
  for arbitrary closed-point-supported sheaves. Upstream
  `Scheme.subsingleton_H_of_isSepClosed` covers only the spectrum of a field.

No new nodes, dependency repairs, statement corrections, or disputed statements.

Validation: the prescribed `scompile.py` compiled both sandbox and module placement
cleanly (5.9 s and 8.1 s), with no errors or warnings. The required `deliver2.py N8 lem-kun-0f1f-vanish --no-push` dry run printed
`OK (dry run)` for commit `ef6bc15099`: compilation and preflight passed, with only
the independent second reading reserved for the second reader. Nothing was pushed.

## Second reading by N8

I independently opened `dag/nodes/sec-smooth-purity/lem-kun-0f1f-vanish.json`, the
source lemma (Stacks Project Tag 0F1F, Lemma 59.97.3), and
`Sheaf/AlgebraicGeometry/ClosedPointSupportVanishing.lean`.

- The source objects are a separably closed field `K`, a scheme `X` of finite
  type over `K`, and an abelian sheaf `F` on the small étale site. Lean renders
  these as `{K : Type u} [Field K] [IsSepClosed K]`,
  `X : Scheme.{u}` with `[X.Over (Spec (.of K))]`, and
  `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- The source finite-type hypothesis is exactly the pair of properties of the
  structure morphism. Lean has
  `[LocallyOfFiniteType (X ↘ Spec (.of K))]` and
  `[QuasiCompact (X ↘ Spec (.of K))]`; no Noetherian, separated, smooth,
  proper, characteristic, torsion, constructibility, or nonemptiness
  assumption is added.
- The source support condition is rendered exactly by
  `hF : Scheme.etaleSheafSupport F ⊆ closedPoints X`, using the recorded
  `AlgebraicGeometry.Scheme.etaleSheafSupport` declaration and Mathlib's
  `closedPoints`. No alternate support notion is introduced.
- The source conclusion quantifies over every positive cohomological degree.
  Lean binds `(q : ℕ) (hq : 0 < q)` and states `IsZero` of
  `(cohomology AddCommGrpCat.{u + 1} X (q : ℤ)).obj
  ((DerivedCategory.singleFunctor
  (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)`. This is the
  recorded `AlgebraicGeometry.Etale.cohomology` object, i.e. the degree-`q`
  étale cohomology of `F` in degree zero; `IsZero` is the categorical
  formulation of equality with the zero abelian group. The quantifier order
  and positive-degree exclusion agree with the node.

Edge cases were checked: `q = 0` is excluded as in the source; the empty scheme,
zero sheaf, and empty support remain admitted; no assumption of nonempty support
or of a characteristic is present; and the explicit universe `Scheme.{u}` with
coefficient category `AddCommGrpCat.{u + 1}` does not exclude these cases.
The source's global-generation assertion is deliberately absent because the node
contains only the vanishing assertion.

I searched Mathlib, the upstream `WeilConjectures` source, project `lean/Sheaf`,
and `dag/lean_names_upstream.json` using the recorded LeanSearch/LeanFinder,
Loogle, and grep queries (including support/cohomology and the proposed theorem
name). The only close upstream result,
`AlgebraicGeometry.Scheme.subsingleton_H_of_isSepClosed`, concerns a spectrum of
one separably closed field and does not state this closed-point-support theorem.
No exact existing declaration was found. The dependency declarations
`IsSepClosed`, `Scheme.Over`, `LocallyOfFiniteType`, `QuasiCompact`,
`Scheme.etaleSheafSupport`, and `Etale.cohomology` were opened and match the
node's notions.

No mismatch was found, so no Lean or node change was necessary. The module was
recompiled with `scompile.py` successfully (no errors or warnings), and the
worker's dry-run delivery was rechecked after this reading.
