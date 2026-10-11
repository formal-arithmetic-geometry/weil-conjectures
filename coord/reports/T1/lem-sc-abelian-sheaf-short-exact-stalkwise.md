## Worker report

The module `Sheaf.Topology.AbelianSheafShortExactStalkwise` states that a short
complex `S` of sheaves of abelian groups on a topological space `X` is short
exact exactly when its image under the stalk functor at every point is short
exact. The binder `{X : TopCat.{u}}` is the topological space, and
`S : ShortComplex (Sheaf AddCommGrpCat X)` supplies the three sheaves and the
composable maps. `S.ShortExact` renders the sequence `0 → F' → F → F'' → 0`.
The right side quantifies every `x : X` and maps `S` along
`Sheaf.forget AddCommGrpCat X ⋙ Presheaf.stalkFunctor (X := X) AddCommGrpCat x`,
so its objects are the stalk abelian groups and its maps are induced stalk maps;
its `ShortExact` is the stalkwise short exactness clause. No hypotheses or
clauses are added or omitted.

The module imports Mathlib's sheaf and stalk definitions and the recorded
presheaf-module stalk module `Sheaf.Topology.PresheafModuleStalkFunctor`; the
statement uses Mathlib's ordinary abelian-group stalk functor, which is the
specialization of the recorded stalk notion to the constant integer ring.
The definition node `def-sc-topological-abelian-cohomology` is represented by
Mathlib's `CategoryTheory.Sheaf.H'` in
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`. The stalk dependency
`def-weil-pbc-module-stalk` is represented by
`PresheafOfModules.moduleStalkFunctor` in
`Sheaf.Topology.PresheafModuleStalkFunctor`.

The statement is supported by the recorded Mathlib criteria
`TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`,
`TopCat.Presheaf.mono_iff_stalk_mono`, and the local-surjectivity/stalk
surjectivity lemmas recorded for
`lem-sc-abelian-sheaf-epi-iff-stalk-epi`; these are proof dependencies of the
node. No declaration with the complete short-exactness criterion exists in
Mathlib or the source repository.

Edge cases checked: an empty topological space makes the universal stalk clause
vacuous and there are no points to test; the zero short complex maps to the zero
short complex at every point; and a one-point space reduces the assertion to
short exactness of one abelian-group sequence. The stalk functor has the same
universe as the sheaf category, so no points or coefficient groups are excluded.

Searches made: `msearch.py leanfinder` for short exact stalkwise abelian sheaves
returned no exact declaration; `msearch.py loogle` for
`TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`, mono and epi stalk criteria
returned the three component criteria; grep of Mathlib topology/sheaf files
found `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact` at
`Topology/Sheaves/Abelian.lean:103`, `TopCat.Presheaf.mono_iff_stalk_mono` at
`Topology/Sheaves/Stalks.lean:582`, and the local-surjectivity criteria at
`Topology/Sheaves/LocallySurjective.lean:80,125`; grep of
`WeilConjectures/` and `lean/Sheaf/` found no complete criterion.

## Earlier second reading (a previous round; superseded)

I reread the node and module independently. The topological-space binder is
`X`, the sheaf objects and maps are exactly the three components of `S`, and
`S.ShortExact` expresses both endpoint conditions and middle exactness. The
right side quantifies all points and uses the stalk functor after forgetting a
sheaf to its presheaf, so it states short exactness of the induced stalk
sequence. The empty-space, zero-sequence, and one-point cases remain included.
The theorem proof is `sorry` as required for stage 2, and no local notation,
private definition, or extra hypothesis is used.

## Second reading by T1

I read the node statement and the Lean signature item by item. The object
``$X$ a topological space'' is rendered by `{X : TopCat.{u}}`; the three
abelian sheaves and their composable maps are rendered together by
`S : ShortComplex (Sheaf AddCommGrpCat X)`. The source sequence
`0 \to F' \to F \to F'' \to 0` and its short-exactness clauses are rendered by
`S.ShortExact`. The stalk at each point is rendered by
`Sheaf.forget AddCommGrpCat X ⋙ Presheaf.stalkFunctor (X := X)
AddCommGrpCat x`, and the conclusion's universal quantifier is rendered by
`∀ (x : X)`. The stalk sequence and all its endpoint and middle exactness
clauses are rendered by the mapped `ShortComplex`'s `.ShortExact`. Thus the
Lean says exactly the node statement, with no extra hypothesis or omitted
clause; the universe `u` is shared by `X`, sheaves, and points.

The edge cases remain covered: for an empty `X` the stalk condition is
vacuous, for a zero short complex both sides hold, and for a one-point space
the criterion is the single stalk sequence. No characteristic, finiteness,
Noetherian, or nonemptiness assumption is present, so zero objects and empty
spaces are included.

I searched the project and upstream source with `rg`, and ran the configured
`msearch.py` LeanFinder/Loogle searches for short-exact stalk criteria. The
only relevant Mathlib declarations are the separate exact, mono, and epi
stalk criteria; no complete short-exact criterion exists. The dependency
records were checked: `def-sc-topological-abelian-cohomology` records the
existing sheaf-cohomology notion, while `def-weil-pbc-module-stalk` records
the general presheaf-module stalk functor whose additive-group specialization
is the stalk functor used here.

No mismatch was found, so no source, node, or Lean change was required. The
module compiled cleanly with `lcompile.py`; its only unfinished declaration is
the required `sorry` proof.
