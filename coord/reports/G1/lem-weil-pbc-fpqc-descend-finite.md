## Worker report

The module `Sheaf.AlgebraicGeometry.IsFiniteOfFpqcCover` states
`AlgebraicGeometry.isFinite_of_fpqc_cover`, with its proof left as `sorry`.
There are no new definitions, dependency modules, or statement corrections.

Clause-by-clause correspondence:

- Schemes X and S: `{X S : Scheme.{u}}`; morphism f: `(f : X ⟶ S)`.
- An arbitrary indexing set I: `{I : Type v}`, with v explicitly declared and independent
  of the scheme universe. No finiteness or nonemptiness is imposed on I.
- Schemes S_i and morphisms g_i: `(S' : I → Scheme.{u})` and `(g : ∀ i, S' i ⟶ S)`.
- The family is an fpqc covering: `hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S`.
  This is precisely the recorded match of `def-weil-pbc-fpqc-covering`, expressing flatness,
  joint surjectivity and quasi-compactness of the covering family. Individual g_i need
  not be quasi-compact.
- The base change f_i is the second projection: `pullback.snd f (g i)`, with domain
  `pullback f (g i)` and codomain `S' i`. Scheme pullbacks exist by Mathlib instances.
- Every f_i is finite: `h : ∀ i, IsFinite (pullback.snd f (g i))`.
- The conclusion that f is finite: `IsFinite f`.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; the category morphism is a locally ringed-space morphism.
- `def-weil-pbc-fpqc-covering`: `AlgebraicGeometry.Scheme.fpqcPrecoverage`,
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`, the quasi-compact precoverage of flat morphisms.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and its second projection
  `CategoryTheory.Limits.pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; available through the imports.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, affine with finite maps on affine-open sections.
  Its sibling `IsIntegralHom` was also read; only `IsFinite` occurs in this signature.

Edge cases checked before writing: the empty indexing set is allowed; an empty family can
cover only an empty base, in which case a morphism into it has empty source and is finite.
An empty source X is allowed over any base. Infinite covering families and non-quasi-compact
members are allowed: the quasi-compact condition is on the family as a whole. No field,
Noetherian, separation, finite-type, or characteristic restriction is inserted. The theorem
uses the chosen fibre product, not an independently parameterized square. Universes u and v
are explicitly bound; there are no quantifiers over test schemes that could become vacuous.

Searches made on 2026-10-11:

- msearch.py leansearch: "A morphism of schemes is finite if every base change along an fpqc
  covering family is finite"; service unavailable (Internal Server Error).
- msearch.py leanfinder: "A morphism of schemes is finite if its base changes along every
  member of an fpqc covering family are finite"; eight results include IsFinite, stability
  under base change, comp_iff, and QuasiCompactCover.of_finite; no exact family descent theorem.
- msearch.py loogle: "AlgebraicGeometry.IsFinite, CategoryTheory.Limits.pullback.snd";
  three hits: IsFinite.instSndScheme (the opposite direction), an etale-neighbourhood theorem,
  and Scheme.Hom.finrank_pullback_snd; none is this statement.
- msearch.py grep: "IsFinite.*(descend|fpqc)|ofArrows.*fpqc" in Mathlib/AlgebraicGeometry;
  no hits.
- rg on the source repository for the item id: no hits. Searches for fpqc/descendsAlong in
  its FlatDescent module locate `IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact`.
  This is descent along one surjective flat quasi-compact map, not along the stated family.
- Read the complete source `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc` module:
  `Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology` handles arbitrary properties P and
  arbitrary pullback squares along a covering sieve. Its full signature differs from the
  node's fixed IsFinite predicate, precoverage-family hypothesis, and chosen projections.
  It can support the future proof, but does not itself have the exact node statement.
- rg on project lean/Sheaf for fpqc/descent and for isFinite_of_fpqc/finite_of_fpqc/IsFinite.*fpqc,
  and on dag/lean_names_upstream.json for the proposed name: no existing exact declaration.
  Related modules concern closed immersions, etaleness and finite locally free descent.

Source checked directly at https://stacks.math.columbia.edu/tag/02LA, because the literature
sources are not present in this remote clone. The source identifies finite with integral plus
locally finite type, and descends both properties. The declaration docstring reproduces all
four proof steps with the dependency node ids and source tags. No statement fault or dispute
was found.

Validation: server single-file compilation and deliver2.py --no-push dry run (results recorded
by the tools). The independent second reading is intentionally left to the assigned reader.

## Second reading by G1

The node's objects and clauses, matched in order, are:

- Schemes `X S : Scheme.{u}` and a morphism `f : X ⟶ S`; Lean has exactly
  `{X S : Scheme.{u}} (f : X ⟶ S)`, using Mathlib's `Scheme` and `Scheme.Hom`. Verdict: exact.
- An arbitrary index type `I`; Lean has `{I : Type v}`, with no finiteness or nonemptiness
  hypothesis. Verdict: exact, including the empty-family case.
- A family of schemes `S_i) and arrows `g_i : S_i ⟶ S`; Lean has
  `(S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)`. Verdict: exact.
- The fpqc covering hypothesis; Lean has
  `hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S`. Mathlib defines this as the
  quasi-compact precoverage intersected with the jointly-surjective flat precoverage. This
  is the source's condition: each arrow is flat and every affine open of `S` is a finite
  union of images of affine (equivalently quasi-compact-open) pieces. Verdict: exact; no
  individual quasi-compactness is added.
- For each `i`, the base change `f_i : X ×_S S_i ⟶ S_i`; Lean uses exactly the chosen
  categorical fibre product and second projection `pullback.snd f (g i)`. Verdict: exact.
- Every base change is finite; Lean has
  `h : ∀ i, IsFinite (pullback.snd f (g i))`, using Mathlib's affine-local `IsFinite`.
  Verdict: exact.
- The conclusion that `f` is finite; Lean concludes `IsFinite f`. Verdict: exact, with
  the same quantifier order and no extra assumptions.

I checked `descent.tex` directly: Definition `definition-fpqc-covering` (Topologies,
Tag 022B) and Lemma `lemma-descending-property-finite` (Descent, Tag 02LA). The source
states precisely the finite-family affine-open covering condition and says finite is fpqc-local
on the base. Empty index sets, empty schemes, empty source schemes, and zero-dimensional
cases are not excluded by the Lean binders; the empty-family case is possible only over an
empty base, as in the source. Universes `u` and `v` are explicit.

Searches were repeated on 2026-10-11. LeanSearch was unavailable (Internal Server Error),
so it produced no verdict. LeanFinder returned only `IsFinite`, stability under base change,
and general `DescendsAlong` infrastructure, with no exact family theorem. Loogle returned no
match for `IsFinite` with `Presieve.ofArrows`. Grep in Mathlib, `WeilConjectures`, and
`lean/Sheaf` found no exact `isFinite_of_fpqc_cover`; the source repository instead has the
more general `Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology` and the instance
`IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact`, neither of which has this
node's fixed signature. The dependency declarations were opened and matched: `Scheme`,
`Scheme.Hom`, `Scheme.fpqcPrecoverage`, `pullback.snd`, and `IsFinite`.

No mismatch was found, so no Lean or node statement was changed. The module compiled cleanly
with `scompile.py`; its only remaining proof is the required named theorem
`AlgebraicGeometry.isFinite_of_fpqc_cover` with `sorry`.

