## Worker report

The module states `AlgebraicGeometry.exists_etale_local_finite_multiple_points_elementary`.
It uses `X S : Scheme`, a morphism `f` with `[LocallyOfFiniteType f]`, a point `s`,
`n : ℕ`, and `x : Fin n → X`. The hypothesis `hxs` renders `f (x i) = s` for every
index. The hypothesis `hxi` renders isolatedness in the scheme-theoretic fibre by
requiring the singleton of the corresponding point under `f.fiberHomeo s` to be open.
The conclusion supplies `U`, `φ : U ⟶ S`, and `u`; `Etale φ`, `φ u = s`, and
`Function.Bijective (φ.residueFieldMap u).hom` render the elementary etale neighbourhood
and residue-field isomorphism. It supplies opens `V i` of `pullback f φ`; finiteness is
`IsFinite ((V i).ι ≫ pullback.snd f φ)`. The unique-point clause is `∃! v` with
membership in `V i` and second projection `u`. The final clause says each such point
has first projection `x i` and that the induced residue-field map is bijective.

Dependencies used are Mathlib declarations `AlgebraicGeometry.Scheme`,
`AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.Scheme.Hom.fiber`,
`AlgebraicGeometry.Etale`, `AlgebraicGeometry.Scheme.residueField`,
`CategoryTheory.Limits.pullback`, and `AlgebraicGeometry.IsFinite`.

Edge cases checked: `n = 0` is represented by `Fin 0`, so the family of opens and all
indexed clauses are vacuous; singleton isolatedness uses the fibre topology and works
for arbitrary points and empty fibres. No field, characteristic, or universe restriction
is added.

Searches: `msearch.py leanfinder` for an etale neighbourhood making finitely many
quasi-finite points finite (no exact match); `msearch.py loogle` for
`AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt` (only a one-point weaker result);
`msearch.py grep` and `rg` over Mathlib and WeilConjectures for 02LL and the theorem name
(no existing declaration); `rg` over `lean/Sheaf` (no existing declaration).

## Earlier second reading (a previous round; superseded)

Read the node and module independently. `f`, `s`, `x`, `hxs`, and `hxi` match the node's
hypotheses. `U`, `φ`, `u`, etaleness, the residue-field bijection, each open `V i`,
finite composite, unique point over `u`, first projection, and residue-field bijection
match clauses (i)--(iii). `Fin n` includes the empty case. No mismatch found.

## Second reading by J1

Read the node and Lean independently, and checked Stacks 02LL in
`/home/ubuntu/c1-stacks-review/more-morphisms.tex:11974-12011`; the local tags table
identifies 02LL with this label. The preceding paragraph explicitly permits
nonseparated morphisms. There is no ambient Noetherian, field or characteristic
hypothesis. No statement correction is present or needed.

Objects, hypotheses and conclusions, item by item:

- Schemes X and S: `{X S : Scheme.{u}}`; morphism: `(f : X ⟶ S)`. Exact.
- Locally of finite type: `[LocallyOfFiniteType f]`. Exact, not finite type or separated.
- Base point: `(s : S)`. Exact.
- Finitely many points: `(n : ℕ) (x : Fin n → X)`. Exact; no distinctness assumed.
- Common image s: `(hxs : ∀ i, f (x i) = s)`. Exact.
- Each point isolated in X_s: `hxi` asserts openness of its singleton in `f.fiber s`
  using `(f.fiberHomeo s).symm ⟨x i, hxs i⟩`. Exact, in the fibre topology.
- Scheme U, morphism φ and marked point: `∃ (U : Scheme.{u}) (φ : U ⟶ S) (u : U)`.
  Exact; U need not be affine.
- Elementary étale neighbourhood: `Etale φ ∧ φ u = s ∧
  Function.Bijective (φ.residueFieldMap u).hom`. Exact. Bijectivity of this ring map
  means it is an isomorphism; `φ u = s` identifies its source residue field with κ(s).
- Open subschemes of X_U: `∃ (V : Fin n → (pullback f φ).Opens)`. Exact.
- Clause (i), finite over U: `∀ i, IsFinite ((V i).ι ≫ pullback.snd f φ)`. Exact.
- Clause (ii), exactly one point above u: `∀ i, ∃! v : ↑(pullback f φ),
  v ∈ (V i : Set ↑(pullback f φ)) ∧ pullback.snd f φ v = u`. Exact: ambient points
  with membership correspond bijectively to points of the open subscheme.
- Clause (iii), projection and induced residue-field isomorphism: for every point
  satisfying that membership and second-projection equation, the last conjunction
  asserts `pullback.fst f φ v = x i` and bijectivity of its `residueFieldMap`.
  Exact, since clause (ii) supplies precisely one such point. The equality identifies
  κ(first projection v) with κ(x i); restriction to an open preserves residue fields.

Dependency declarations checked against their node statements and source signatures:
`Scheme`/`Scheme.Hom` in Scheme.lean; `LocallyOfFiniteType` in FiniteType.lean:43;
`Scheme.Hom.fiber` and `fiberHomeo` in Fiber.lean:38,103; `Etale` in Etale.lean:41;
`Scheme.residueField` and `Scheme.Hom.residueFieldMap` in ResidueField.lean:45,123;
`pullback`, `pullback.fst`, `pullback.snd` in HasPullback.lean:95,111,115;
`IsFinite` in Finite.lean:39. Opens and inclusion are Mathlib's restriction scheme and
`Scheme.Opens.ι` (Restrict.lean:46,52). These are the recorded notions, with no extra
instance requirement beyond Mathlib's scheme pullbacks. No new definition nodes or
additional dependency modules are necessary.

Edge cases: Fin 0 admits the empty family; the identity neighbourhood supplies the
remaining conclusion. For an empty X or empty fibre, a nonempty selected family cannot
satisfy the hypotheses; n = 0 is still covered. An empty S has no s, as in the source.
Repeated points are allowed. No zero ring, characteristic, nontriviality, algebraic
closure or field restriction is introduced. `universe u` is arbitrary and all scheme
objects and pullbacks live in Scheme.{u}; it imposes no fixed universe bound. All
variables and universes are bound.

Independent searches (2026-10-11): LeanFinder query "simultaneous elementary etale
neighbourhood finite open subschemes isolated fibre points same residue fields"
returned etale-locus results, no exact theorem. LeanSearch query "isolated points in a
scheme fibre admit an etale base change with finite open neighbourhoods and unchanged
residue fields" was unavailable (Internal Server Error); no verdict assigned to that
service. Loogle query `AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt` returned the
quasi-finite-at-point APIs. Direct `rg` for `02LL`, `multiple.points`, elementary
etale neighbourhoods and `exists_etale_isCompl` in Mathlib, WeilConjectures and
repository lean/Sheaf found no exact declaration. Opened the related
`exists_etale_isCompl_of_quasiFiniteAt` in ZariskisMainTheorem.lean:49: it assumes
separatedness and lacks both uniqueness and residue-field clauses, so cannot replace
this statement. The landed FinitePiecePersistence module is the persistence lemma,
not this simultaneous existence assertion.

Mismatch repaired: H8, the original proof docstring compressed six node steps into
three sentences and omitted the dependency names and residue-field/persistence
verifications. Expanded it to all six steps with their cited nodes and the n = 0
case. The Lean signature and node's verbatim `lean.statement` were already correct
and were retained. No definitions or proofs added; the sole theorem still uses sorry.
All imports serve the statement and all Lean lines are at most 100 characters.
