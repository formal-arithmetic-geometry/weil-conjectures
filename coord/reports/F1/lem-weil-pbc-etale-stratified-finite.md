## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleStratifiedFinite` states
`AlgebraicGeometry.Scheme.exists_etale_stratified_finite`, with its sole proof `sorry`.
There are no new definitions or dependency modules.

Hypothesis and clause correspondence:

- The arbitrary schemes X and U are `{X U : Scheme.{u}}`, with explicitly declared universe u.
- X is quasi-compact and quasi-separated: `[CompactSpace X] [QuasiSeparatedSpace X]`.
- U is quasi-compact and quasi-separated: `[CompactSpace U] [QuasiSeparatedSpace U]`.
- The given etale morphism is `(j : U ⟶ X) [Etale j]`; no separatedness is assumed.
- The finite partition is `∃ S : LocallyClosedStratification X`. Its inherited `n : ℕ`,
  `stratum : Fin n → Set X`, `pairwise_disjoint_stratum` and `iUnion_stratum_eq_univ`
  give finiteness, disjointness and coverage, without implying a scheme coproduct isomorphism.
- Locally closed subschemes are S.domain and S.immersion, with S.isImmersion,
  S.range_immersion and S.isLocallyClosed_stratum. No reduction or closure-incidence
  condition is imposed.
- Constructibility is `∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)`.
- U_i = U ×_X X_i is `pullback j (S.immersion i)`; its structure morphism to X_i is
  `pullback.snd j (S.immersion i)`.
- Each structure morphism is finite etale: the conjunction `IsFinite ... ∧ Etale ...`
  for every i. These are precisely the object conditions of the dependency's FEt category;
  no category of finite etale objects needs to be constructed for this assertion.

Dependency declarations read and used:

- def-weil-pbc-scheme-conventions is explicitly a convention record, with no declaration.
  It specifies the Mathlib scheme properties and the immersion interpretation used here.
- def-weil-etale-morphism: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, the affine-local etale ring-map condition.
- def-weil-constructible-subset: `Topology.IsConstructible`,
  `Mathlib.Topology.Constructible`, membership in the Boolean algebra of retrocompact opens.
- def-weil-pbc-finite-etale-category: `CategoryTheory.MorphismProperty.Over` in
  `Mathlib.CategoryTheory.MorphismProperty.Comma`, specialized to `@IsFinite ⊓ @Etale`,
  and `Over.pullback` in `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`.
  Its object condition is rendered directly using `AlgebraicGeometry.IsFinite` from
  `Mathlib.AlgebraicGeometry.Morphisms.Finite` and `Etale`. The functor itself is not
  needed: the theorem concerns the pullback of j before it has become finite.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback` and `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (available transitively).
- Added existing landed def-constructible-stratification:
  `AlgebraicGeometry.Scheme.LocallyClosedStratification`,
  `Sheaf.AlgebraicGeometry.LocallyClosedStratification`, extending
  `Topology.Stratification` from `WeilConjectures.Topology.Stratification`.
  Its complete structure and docstring were read. It has precisely the partition and
  immersion data, without constructibility; constructibility is separately asserted.

Edge cases checked before writing: X empty admits n = 0, with all stratum clauses
vacuous; U empty over nonempty X has finite etale empty restrictions. No nonempty-index,
surjectivity, positive-degree, Noetherian or separated hypothesis is imposed. Identity
morphisms admit one stratum. Nonseparated etale qcqs sources are covered by the stated
gluing argument. Scheme.{u} accommodates arbitrary schemes by choosing u large enough;
the finite indexing is Fin n, so no index-universe restriction is introduced.

Searches for an existing statement:

- msearch.py leanfinder: "An etale morphism between quasi compact quasi separated schemes
  becomes finite etale on a finite constructible locally closed stratification". Eight
  results, concerning etale compositions, loci and sites, none stating this theorem.
- msearch.py loogle: "AlgebraicGeometry.Etale, AlgebraicGeometry.IsFinite". One result,
  `exists_etale_isCompl_of_quasiFiniteAt`, concerning a different local splitting theorem.
- msearch.py grep, AlgebraicGeometry: `stratif.*finite|finite.*stratif|constructible.*[Ee]tale|[Ee]tale.*constructible`.
  Zero Mathlib hits.
- rg in the source WeilConjectures and project lean/Sheaf for stratification and etale /
  constructible patterns found existing stratification structures and sheaf theorems,
  but no theorem stratifying an etale morphism into finite etale restrictions.
- rg for the item's blueprint id in the source found no declaration.
- rg for `exists.*[Ss]tratif|etale.*stratif|stratif.*etale` in source, project and
  dag/lean_names_upstream.json found only unrelated sheaf stratification declarations.

The module docstring carries all four proof steps and their DAG dependency names.
The mathematical assertion agrees with the source; no STATEMENT-DISPUTED issue was found.

## Statement corrected

The citation "Tag 03S9 (lemma-etale-stratified-finite)" in the statement is erroneous.
The source is [Stacks Tag 03S0, Lemma 59.72.1](https://stacks.math.columbia.edu/tag/03S0),
opened and read in full. The mathematical statement is unchanged. The corrected statement
also explicitly cites def-constructible-stratification, the already landed notion of the
finite partition being used. This node is not a blueprint unit's own statement.

The exact stmt_deps/proof_deps citer audit found one citer:

- lem-weil-pbc-etale-free-sheaf-constructible: holds true. Its first proof step applies
  exactly this finite constructible locally closed partition theorem. Correcting the tag
  and recording the existing stratification notion leave that application unchanged.

The immutable source/proof-origin/proof-place fields still contain the inherited 03S9
typo. They are not edited; the correction record and this report identify the true source.

Compilation and dry-run validation are performed using scompile.py and deliver2.py --no-push.
The independent second reader supplies the second-reading section.

## Second reading by F1

I read the corrected node and the Lean file independently. The objects and clauses
match as follows:

- The Lean binders `{X U : Scheme.{u}}` are the two schemes, with one explicit
  universe shared by both; `[CompactSpace X] [QuasiSeparatedSpace X]` and the
  corresponding instances for `U` render exactly the quasi-compact,
  quasi-separated hypotheses.
- `(j : U ⟶ X) [Etale j]` renders the given etale morphism, with no separatedness,
  Noetherian, finite-type, characteristic, or surjectivity assumption added.
- `∃ S : LocallyClosedStratification X` renders a finite partition by the
  dependency's scheme stratification: its `Fin S.n` index, pairwise disjoint
  strata, cover, scheme domains, immersion fields, and image equalities supply
  precisely the locally closed subschemes and partition clauses.
- `(∀ i : Fin S.n, Topology.IsConstructible (S.stratum i))` renders
  constructibility of every stratum.
- For each `i`, `pullback.snd j (S.immersion i)` is the structure morphism from
  `U ×_X S.domain i` to `S.domain i`; the final conjunction
  `IsFinite ... ∧ Etale ...` is exactly the finite-etale conclusion. The use of
  `pullback` and `pullback.snd` is the recorded fibre-product notion.

The empty scheme and `n = 0` are permitted (the indexed clauses are vacuous),
empty `U` is permitted, and identity etale maps are covered. `Fin n` introduces
no index-universe restriction beyond the scheme universe. No characteristic or
nonzero-object case is excluded. The theorem compiled cleanly with only the
intended `sorry` warning suppression.

I searched Mathlib, the source project, and `lean/Sheaf` using the worker's
LeanSearch/Loogle/grep queries and additional `stratif.*finite`,
`etale.*stratif`, and `exists.*stratif` searches. No existing theorem states this
result. The only mismatch was the inherited Stacks tag 03S9; the source is Tag
03S0, Lemma 59.72.1. The node correction records that citation repair and adds
the already landed `def-constructible-stratification` dependency. The Lean
statement itself required no further change.
