## Worker report

The module `Sheaf.AlgebraicGeometry.StableModuliRegularUniversalAtlas` states
`AlgebraicGeometry.stableModuli_regular_universal_atlas`, with its proof `sorry`.
The helper `AlgebraicGeometry.stableAtlasCurveComparison` is a real construction:
it compares the two actual pullbacks using the cartesian squares of the recorded
stable-family arrows. It takes no arbitrary curve isomorphism as extra data.

The previous worker's stage-1 refusal does not apply: the current stage-2 brief
§0 explicitly permits formalizing an accepted split. The node is in the stage-2
queue, has no Lean record, and has no repair note. Its accepted split and all
non-`lean` fields are preserved. No new nodes or dependency replacements are needed.

Hypothesis and clause correspondence:

- Genus at least two: `(g : ℕ) (hg : 2 ≤ g)`. The category is the dependency's
  `StablePointedModuli (Spec (.of (ULift.{u} ℤ))) g 0`, so the base is the integers,
  the genus is the geometric arithmetic genus, and the unpointed label set is empty.
  `ULift.{u} ℤ` permits schemes in every universe; it changes no arithmetic base.
- A scheme U carrying a stable family: the existential `U : StablePointedModuli ...`
  contains the scheme `U.base.left`, curve `U.curve`, projection `U.projection`,
  stability, and genus. It therefore specifies the actual map U to the moduli
  groupoid by precisely the object convention in the recorded dependency.
- Smooth and finite type over Z: `Smooth U.base.hom`,
  `LocallyOfFiniteType U.base.hom`, and `QuasiCompact U.base.hom`.
- Representable, surjective, etale: for every stable family X, the first conjunct
  gives T and cartesian arrows `a : T ⟶ X`, `b : T ⟶ U` such that
  `Nonempty (IsLimit (BinaryFan.mk a b))`, `Etale a.base.left`, and
  `Surjective a.base.left`. Its scheme is `T.base.left`, over `X.base.left`.
  A limiting binary fan in this particular total category is exactly the scheme
  presentation of X times over the moduli groupoid U. Indeed, a map from any test
  scheme to that 2-fibre product is a pair of base maps and a curve isomorphism.
  Pull back X to the test scheme: this gives a stable family W and two cartesian
  arrows W to X,U. The fan limit gives its unique arrow to T. Conversely, every
  such arrow gives exactly that pair and isomorphism. Thus the limit property is
  the functor-of-points representation, including all curve automorphisms; it
  neither passes to isomorphism classes nor forgets the given projection.
- Every stable family C/S, with arbitrary S: `∀ X : StablePointedModuli ...` has
  no Noetherian or finiteness restriction on `X.base.left`. The same binary fan
  is its asserted T. The `square : IsPullback ...` in each of a,b identifies
  `T.curve` with the respective pullbacks of X and U. The helper constructs the
  universal over-T curve isomorphism from those two squares. Thus the last clause
  of the node is included in the first conjunct, not a second unrelated cover.
- Nerve level n: `∀ n : ℕ`, with `N` and `p : Fin (n + 1) → (N ⟶ U)` and
  `Nonempty (IsLimit (Fan.mk N p))`. A cone is a stable family with (n+1)
  cartesian arrows to U. On every test scheme it is the tuple of U-maps and
  coherent curve isomorphisms defining the iterated 2-fibre product. Its limit
  represents that functor, by the same test-family argument as for the binary fan.
  Hence `N.base.left` is U_n; its curve is the common pulled-back curve.
- Smooth, finite type, Noetherian, regular U_n: respectively `Smooth N.base.hom`,
  `LocallyOfFiniteType N.base.hom ∧ QuasiCompact N.base.hom`,
  `IsNoetherian N.base.left`, and `IsRegularScheme N.base.left`.
- Every projection to U is etale: `∀ i : Fin (n+1), Etale (p i).base.left`.
- Dense smooth-family open: `∃ V : N.base.left.Opens, Dense (V : Set N.base.left)`
  and, for every T and base map a,
  `Smooth (pullback.snd N.projection a.left) ↔ Set.range a.left ⊆ V`.
  This functor-of-points characterization specifies the smooth-family locus,
  rather than the smooth locus in the total curve or an unrelated dense open.
- Overlap, triple overlap, cocycle: n=1,2 are included, and for all i,j,k the
  `stableAtlasCurveComparison (p i) (p j)` isomorphisms compose to the i,k
  comparison. The arrows have the correct common base because each p is a
  cartesian stable-family arrow. Identity comparisons follow directly from the
  real construction; no arbitrary cocycle is substituted.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `AlgebraicGeometry.StablePointedModuli`, its `Hom`, `Hom.square`, `forget`,
  and `pullback`. Its total category has exactly the required cartesian arrows;
  its definition of maps from schemes as families justifies the fan interface.
  No alternate moduli groupoid or genus predicate is introduced.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`,
  with `QuasiCompact` from `Morphisms.QuasiCompact`, as the recorded dependency
  explicitly specifies for finite type.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.snd`; `IsPullback.isoPullback` and
  `isoPullback_hom_snd` construct the canonical comparison in `Over`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`,
  namely local Noetherianity together with stalkwise regularity.

All available proof dependencies are imported privately, including the recorded
`CategoryTheory.unramifiedModuliDiagonal_iff_etaleAtlas` and
`Algebra.isRegularRing_of_smooth`, and the Mathlib modules of the proof's matched
affine cover, coproduct, finite morphism, affine product, finite-type permanence,
Noetherianity, open-immersion etaleness, and affine ring-map comparison lemmas.
The arithmetic nodal-stack, stable-open, stable-Isom, chart calculus, point-topology,
framed smoothing and chart-density nodes currently have neither Lean records nor
Mathlib matches, so their modules cannot be imported. They are proof dependencies,
not missing statement prerequisites. They remain named step by step in the theorem
docstring, for later proof work.

Edge cases checked before writing: n=0 is the singleton fan, whose representing
scheme is U up to its unique compatible isomorphism. n=1 and n=2 give the required
overlap and triple overlap. All repeated factor indices are permitted in the
cocycle. Empty test bases give empty scheme pullbacks and the usual unique
cartesian comparison; no nonempty assumption excludes them. No characteristic,
algebraic-closure choice or invertibility of automorphism orders is imposed.
The arbitrary base X can be non-Noetherian, disconnected or nonreduced. Genus
0 and 1 are intentionally excluded by the node, and g=2 is included. The open
may be empty on an empty nerve scheme; density has its usual vacuous meaning.

Searches for an existing statement:

- `msearch.py ... leanfinder`, query “Stable genus at least two curves admit an
  etale universal atlas smooth of finite type over the integers with regular nerve
  schemes and dense smooth curve locus”: eight hits, all scheme etaleness,
  smoothness or standard-smooth algebra facts; no stable-moduli atlas theorem.
- `msearch.py ... leansearch`, query “A stable curve moduli stack over the integers
  admits a representable etale surjective atlas smooth and of finite type over
  the integers”: eight hits, all general smoothness, etaleness or etale-site facts.
- `msearch.py ... loogle`, query
  `AlgebraicGeometry.StablePointedModuli, AlgebraicGeometry.Smooth`:
  zero hits; the external index does not know the project's stable-family name.
- `msearch.py ... grep`, query `stable.*[Aa]tlas|[Aa]tlas.*[Ss]table`, restricted
  to Mathlib/AlgebraicGeometry: zero hits.
- `rg` with that pattern in `lean/WeilConjectures`: no hits; with the exact node
  id there: no hits. In `lean/Sheaf` the hits were algebraic-space chart commentary
  and `UnpointedStableCoarseProjective`. The latter was opened in full: its base
  is an arbitrary field and its conclusion concerns coarse projective moduli and
  a field atlas, without the arithmetic regular nerve or arbitrary-family scheme
  presentation here. It therefore cannot serve as an existing declaration.
- `rg` for both new declaration names in Mathlib, `lean/WeilConjectures`,
  `lean/Sheaf` and `dag/lean_names_upstream.json`: no existing names.

The local Stacks sources were read at theorem-stable-smooth-proper (0E9C),
lemma-stable-curves-smooth, lemma-stable-curves-deligne-mumford,
lemma-stable-quasi-compact and lemma-smooth-dense-in-stable. The arithmetic
smoothness and density agree with the node. No statement correction or disputed
statement is needed.

Validation: `scompile.py Q14 lem-sfb-stable-moduli-regular-universal-atlas <module>`
compiled both the sandbox and named library module cleanly (5.5s and 3.5s).
The initial helper elaboration needed explicit source and target annotations for
`Over.isoMk`; these were added, with no change to the theorem statement.

## Second reading by Q14

This is a second in-thread pass, not a claim of an independent worker review:
the dispatcher explicitly forbids starting other agents. The maintainer's
independent delivery review remains to be done. I reopened the live node, the
stable-family category definition and the delivered module, and checked every
clause against the mapping above. In particular the binary-fan limit is tested
against arbitrary stable families and therefore all test schemes by pullback;
it encodes the pair sheaf rather than merely existence of a covering. The nerve
fan similarly retains isomorphism coordinates. The two cartesian squares give
the universal over-base comparison, whose composition is the stated cocycle.
The dense open is characterized for every base change rather than just closed
points. No mathematical mismatch was found. Only explicit `Over.isoMk` type
annotations changed during compilation. All theorem proofs remain `sorry`;
the helper's data is constructed from the recorded pullback universal property.
