## Worker report

The module `Sheaf.AlgebraicGeometry.IrreducibleLisseStrata` states
`AlgebraicGeometry.Scheme.exists_irreducible_lisse_stratification`. Its only proof is
`sorry`; its docstring carries all three DAG proof steps. No new definition, dependency
module, statement correction, or disputed statement is needed.

Hypothesis and clause correspondence:

- “X”: `(X : Scheme.{u})`, an arbitrary scheme, without a base field or separation condition.
- “Noetherian”: `[IsNoetherian X]`, Mathlib's locally Noetherian and quasi-compact scheme.
- “F an abelian etale sheaf”: `(F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})`.
- “constructible”: `hF : IsConstructibleEtaleSheafOfSets` of the underlying set sheaf,
  obtained by `sheafCompose` with `CategoryTheory.forget AddCommGrpCat`. This uses the
  dependency's finite-stalk notion, rather than the source's finitely generated abelian
  stalk notion (a constant Z sheaf must not qualify).
- “there is a finite partition”: `∃ S : Stratification X`. Its inherited `n : ℕ`,
  `stratum : Fin n → Set X`, `iUnion_stratum_eq_univ`, and
  `pairwise_disjoint_stratum` give finiteness, coverage, and disjointness.
- “locally closed subschemes”: `S.domain i`, `S.immersion i`, `S.isImmersion i`, and
  `S.range_immersion i` realize the subsets as actual immersed schemes; inherited
  `isLocallyClosed_stratum` supplies local closedness. Its constructibility requirement
  adds no restriction here: on a Noetherian scheme every locally closed subset is
  constructible. It does not mean a coproduct isomorphism of schemes.
- “nonempty irreducible”: `IrreducibleSpace (S.domain i)`, whose `toNonempty` field
  includes nonemptiness. No integrality or reducedness is imposed on the strata.
- “each F restricted to S_i locally constant with finite stalks”:
  `∀ i : Fin S.n, ... IsFiniteLocallyConstantEtaleSheafOfSets
  ((etaleSetPullback (S.immersion i)).obj ...)`. The dots denote exactly the same
  underlying set sheaf used in `hF`. The predicate is the conjunction of local
  constancy and finiteness at every algebraically closed geometric stalk. Forgetting
  the abelian group structure expresses precisely the finite-stalk sheaf condition;
  inverse image and forgetting commute canonically.

Dependency declarations read and used:

- `def-weil-pbc-etale-sheaves`: module `Sheaf.AlgebraicGeometry.EtaleSheaves`,
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleSheafOfSets`,
  `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantEtaleSheafOfSets`, and
  `AlgebraicGeometry.Scheme.etaleSetPullback`. Their full signatures and docstrings
  were read, including the local constancy and geometric-stalk definitions.
- `def-weil-pbc-scheme-conventions` is explicitly a convention node with no declaration.
  Its underlying declarations are `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.IsImmersion`. The signature and docstring of `IsImmersion` were
  read in Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean.
- `AlgebraicGeometry.Scheme.Stratification` (imported by EtaleSheaves) is the existing
  source declaration in `WeilConjectures.ConstructibleSheaf.Defs`; its full structure
  and docstring and the inherited `Topology.Stratification` in
  `WeilConjectures.Topology.Stratification` were read. No duplicate partition notion.

Edge cases checked before writing: the empty scheme uses n = 0, so the requirement
that every stratum is nonempty does not exclude it. A nonempty scheme cannot have
n = 0 by coverage. Zero sheaves and singleton stalks are finite and qualify. Nilpotents
are allowed in X and the strata; irreducibility is topological, not integrality.
Repeated or empty pieces cannot satisfy disjointness and IrreducibleSpace simultaneously.
No characteristic is excluded. Universe u is explicit; the coefficient universe u+1
is exactly the existing dependency convention. No auto-bound variables are used.

Source verification: the blueprint node's complete statement and proof were read
on the server at the node's recorded source path (the local literature copy lacks it).
They agree with the DAG statement. The scheme-conventions node and the complete
etale-sheaves dependency module were read locally. No unit statement is changed.

Searches (all service searches recorded by msearch.py in searches.jsonl):

- LeanSearch: “A constructible étale abelian sheaf on a Noetherian scheme has a finite
  partition into nonempty irreducible locally closed subschemes with finite locally
  constant restrictions”; unavailable, Internal Server Error.
- LeanFinder: same query; eight hits, principally
  `AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian`, Noetherian scheme
  properties and constructible subset lemmas. None states the sheaf stratification.
- Loogle: `"IsConstructible", "IsIrreducible"`; zero hits.
- Mathlib grep via msearch.py: `irreducible.*strat|strat.*irreducible`; zero hits.
- rg in WeilConjectures and lean/Sheaf:
  `irreducible.*strat|strat.*irreducible|lem-weil-pbc-irreducible-lisse-strata`;
  found only references in docstrings and a smooth irreducible stratum discussion,
  no existing theorem. The mandated grep of the exact node id in WeilConjectures
  returned no hits.
- rg for `exists_irreducible_lisse_stratification` in dag/lean_names_upstream.json,
  WeilConjectures and lean/Sheaf returned no hits.

Validation: server single-file compilation and deliver2.py --no-push are run for this
module; the independent second reader supplies the second-reading section.

## Second reading by G1

I read the node statement, its source place, and the complete Lean signature item by item.
The node introduces an arbitrary Noetherian scheme `X`, a constructible abelian étale sheaf
`F`, and concludes existence of a finite partition by nonempty irreducible locally closed
subschemes on which the restriction is locally constant with finite stalks. In Lean these
are rendered by `(X : Scheme.{u}) [IsNoetherian X]`,
`F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`, and
`∃ S : Stratification X, ∀ i : Fin S.n, IrreducibleSpace (S.domain i) ∧
IsFiniteLocallyConstantSheaf ((Etale.upperStar AddCommGrpCat (S.immersion i)).obj F)`.
`Stratification` supplies the finite index, pairwise-disjoint coverage, constructible locally
closed strata, and immersed scheme domains; `IrreducibleSpace` includes nonemptiness. The
`IsFiniteLocallyConstantSheaf` clause is the abelian-sheaf local constancy plus finitely
generated geometric stalk condition from `ConstructibleSheaf.Defs`.

The worker signature had instead assumed constructibility of the underlying set sheaf and
concluded finite set-valued pullbacks. That was strictly stronger and changed the object and
stalk notion: a finitely generated abelian stalk need not be a finite set. I repaired the
hypothesis to `IsConstructibleSheaf F` and the conclusion to the abelian
`Etale.upperStar`/`IsFiniteLocallyConstantSheaf` formulation. The module now compiles.
No other hypotheses or clauses were added. Edge cases remain covered: `n = 0` handles the
empty scheme, nonempty schemes cannot have an empty partition by coverage, zero sheaves and
finitely generated stalks are allowed, nilpotents and all characteristics are allowed, and
universes are explicit (`u` and `u + 1`) with no auto-bound variables.

I rechecked the existing-definition searches in the worker report (LeanSearch, LeanFinder,
Loogle, Mathlib grep, and repository `rg`); no theorem for this stratification exists. I also
read the dependency declarations `IsConstructibleSheaf`, `IsFiniteLocallyConstantSheaf`,
`Stratification`, and `Etale.upperStar` in `WeilConjectures.ConstructibleSheaf.Defs` and the
set-sheaf definitions in `Sheaf.AlgebraicGeometry.EtaleSheaves`. The source place and the
node agree with the repaired abelian formulation.

## Reviewer fix (R-ils1106)

The second reading's repair was reverted. It replaced the stmt_dep's recorded notions
(def-weil-pbc-etale-sheaves: `IsConstructibleEtaleSheafOfSets`, `IsFiniteLocallyConstantEtaleSheafOfSets`,
`etaleSetPullback`, finite geometric stalks) by the source's `IsConstructibleSheaf` /
`IsFiniteLocallyConstantSheaf` (def-constructible-*, not stmt_deps), whose stalk condition for
`AddCommGrpCat` is finitely generated. The node says "locally constant with finite stalks", so that
weakened both hypothesis and conclusion (a constant Z sheaf would qualify). The statement is
restored to the worker's form on the underlying set sheaf (`sheafCompose … forget`), the form the
sibling lem-weil-pbc-constructible-noetherian-finite-selection (order 1604) landed with.
