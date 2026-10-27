## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreeAmpleReflection` states
`AlgebraicGeometry.Scheme.Modules.isAmple_of_tensorPullback_finiteLocallyFree_surjective`.
Its sole proof is `sorry`. It defines no notions and changes only the item's `lean` field.
There is no repair note and no statement correction or disputed statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes and morphism `f : Y → X`: `{X Y : Scheme.{u}} (f : Y ⟶ X)`.
  The arbitrary universe `u` is explicitly bound.
- Finite locally free: `[f.IsFiniteLocallyFree]`. The recorded class extends exactly
  `IsFinite f`, `Flat f`, and `LocallyOfFinitePresentation f`; these are the three
  properties spelled out in the node's second sentence.
- Surjective on underlying points: `[Surjective f]`, whose field is `Function.Surjective f`.
- The supplied invertible module: `(L : X.Modules) [L.IsInvertible]`, with the existing
  locally rank-one definition, rather than an independently chosen line bundle.
- Its tensor pullback: `(tensorPullback f).obj L`, the existing sheafified
  `O_Y ⊗_{f⁻¹ O_X} f⁻¹ L` construction.
- Absolute ampleness of that very pullback: hypothesis
  `hL : @IsAmple Y ((tensorPullback f).obj L) ((invertible_pullback_tensor f).1 L).2`.
  The final proof argument is the already proved invertibility of the pullback,
  not an additional assumption or an arbitrary invertibility witness.
- Conclusion: `IsAmple X L`. Both occurrences resolve inside
  `AlgebraicGeometry.Scheme.Modules`, to the absolute affine-section predicate,
  including quasi-compactness, rather than the projective-over-a-field predicate
  `AlgebraicGeometry.IsAmple`.
- There are no base scheme, properness, normality, Noetherianity, constant degree,
  characteristic, nonemptiness, or reducedness assumptions.

Recorded statement dependencies used (declarations and docstrings read in full):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree` (and the recorded degree variant read).
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the normalized adjunction
  and public upstream tensor-pullback construction; in particular the statement uses
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`, whose actual definition was read
  in `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple` and `nonvanishingLocus`.

The existing `invertible_pullback_tensor` theorem is publicly imported because its
first clause supplies the proof argument of `IsAmple` in the public signature.
The other stated proof dependencies are plain imports: Mathlib's `FlatRank` (locally
constant rank), `Proper` and `QuasiFinite` (finite morphisms are closed with finite
fibres), `Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine`,
`Sheaf.CategoryTheory.RingedSiteModules`, and upstream `AffineCapSectionOpen`.
The proof dependency `lem-sfb-finite-locally-free-pullback-section-norm` currently has
neither `lean` nor `mathlib_match`, so no module can yet be imported for it. It is
not a statement dependency and no new notion is needed to state this item. Its exact
role is retained in step 3 of the proof docstring; the maintainer can add its import
when that node is stated, as required by stages/2-statements.md §3(7).

Source and edge-case checks:

Read `literature/stacks-project/divisors.tex`, the norms section from its definition
through the proof of finite-locally-free-has-norm, including 0BCY, 0BD0 and 0BD2.
The docstring follows all four accepted proof steps. Empty `X` is allowed: absolute
ampleness has compactness and a vacuous pointwise condition. For nonempty `X`, a
surjection rules out degree zero at each point. Varying positive rank is allowed:
the norm is applied on a clopen rank stratum and the section is glued with zero on
its complement. Degree one includes identities. Disconnected schemes, nonreduced
fibres (e.g. dual numbers), and characteristics dividing the rank remain covered;
the determinant norm and positive tensor exponent do not require separability or
inverting the degree. No separate quasi-compactness hypothesis is needed because
it is part of pullback ampleness and descends topologically along the surjection.

Searches for reuse:

- `msearch.py ... leanfinder "An invertible sheaf whose tensor pullback by a finite
  locally free surjective scheme morphism is ample is itself ample"`: 8 hits on
  morphism base-change properties, no ampleness reflection theorem.
- `msearch.py ... leansearch "If the pullback of an invertible sheaf along a finite
  locally free surjection of schemes is ample then the original invertible sheaf
  is ample"`: 8 hits on pullback and base-change properties, no matching theorem.
- `msearch.py ... loogle "IsAmple, IsFiniteLocallyFree"`: 0 hits; unknown `IsAmple`.
- `msearch.py ... grep "IsAmple|ample.*(reflect|descen)|isAmple.*(finite|pullback)"
  AlgebraicGeometry`: 0 Mathlib hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, for `IsAmple`, ampleness
  reflection/descent, and the node id: no exact match. The related theorem
  `AlgebraicGeometry.isAmple_iff_tensorPullback_of_isFinite_surjective` in
  `Sheaf.AlgebraicGeometry.FiniteSurjectiveAmpleReflection` requires proper source
  and target over a Noetherian ring. `FiniteNormalAmpleDescent` proves existence
  of some ample line on a normal integral target. Neither states this node.
  Upstream `AmplePullback` is the opposite implication. The alternative upstream
  `AlgebraicGeometry.IsAmple` requires projectivity over a field and is unsuitable.
- Exact-name and node-id search across the two library roots found no existing
  declaration of this theorem. All notions in the signature reuse the records above.

Validation: the prescribed `scompile.py N8 lem-sfb-finite-locally-free-ample-reflection`
compiled both the sandbox and actual library module successfully (11.6 s and 5.5 s),
with no errors or warnings. All binders and universes are explicit and `autoImplicit`
is disabled. Only the named theorem is postponed; the delivery contains no definitions.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
