## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveSpace.HyperplaneCohomologyTailBound`
states `AlgebraicGeometry.ProjectiveSpace.hyperplane_cohomology_tail_bound`, with
one postponed proof and no new definition. The natural-language statement and
six-step proof of the item are preserved. The theorem docstring includes all six
steps, including the compatible twist comparisons, the finite injection composites,
the kernel/image argument, propagation of a plateau, and the dimension countdown.
The source is Stacks Project, Varieties, Tag 08AG, `lemma-bound-quotients-free`,
read in `literature/stacks-project/varieties.tex`, especially the three middle
cohomology paragraphs. The statement extracts their cohomology thresholds, not the
closing regularity assertion of that paragraph.

Hypotheses and clauses, matched individually:

- The field is `(k : Type u) [Field k]`; there is no characteristic or infinitude
  restriction. `(n : ℕ) (hn : 1 ≤ n)` is the dimension assumption.
- `X = P^n_k` is written directly as `ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))`.
  The lifted coordinate type has exactly `n+1` coordinates at the scheme universe.
- `E` is a module on that scheme, and `hE : RingedSpace.IsCoherent ... E` is the
  full finite-type plus finite-type-kernel condition of Stacks 01BV. It uses the
  coherence predicate now exposed by the recorded `CoherentFiniteType` module,
  rather than just its quasi-coherent-finite-type conjunction.
- Every `E(d)` is `E ⊗ₘ twist ... d`, the existing sheaf tensor product and twist.
  There is no duplicate twist or cohomology definition.
- `s : Γ(twist ... 1, ⊤)` and `hs : s ≠ 0` are the nonzero linear form. Global
  sections of `O(1)` on projective space are precisely linear forms.
- `{H : Scheme.{u}}`, `i : H ⟶ X`, and `[IsClosedImmersion i]` give the closed
  immersion. `hH : i.ker = Hom.zeroLocus (homOfGlobalSection _ s)` says its defining
  ideal is the zero-scheme ideal of this very section, not an arbitrary hyperplane.
- `e : H ≅ P^(n-1)_k` is the fixed identification. `he` says it is over `k` with
  the structure map on `H` induced by `i`. `htwist` supplies for every integer `d`
  the isomorphism `i^*O_X(d) ≅ e^*O_(P^(n-1))(d)`. These are the twist comparisons
  stated in the node, not arbitrary isomorphisms between cohomology groups.
- `G` is written directly as `(Scheme.Modules.tensorPullback i).obj E`; `hG`
  assumes precisely its coherence. No independent module or arbitrary pullback
  comparison is introduced.
- `hinj : ∀ d : ℤ, Mono (regularHyperplaneMultiplication k n E d s)` means
  multiplication by the actual `s` is injective on every twisted module. The
  canonical map has degrees `d, 1+d`, which parametrizes exactly all `D-1,D`.
  A monomorphism of sheaves of modules is the asserted injective sheaf map.
- `(m : ℤ)` is unrestricted. `hregular` quantifies all natural degrees `q` with
  `1 ≤ q` and `q ≤ n-1`, and sets `H^q(H,G(m-q))` to zero. It uses the ambient
  pulled-back twist; `htwist` identifies it with the named twist on `H`.
- The first conjunct quantifies every natural `q` and integer `t`, with exactly
  `2 ≤ q` and `m ≤ t`, and asserts the requested vanishing of `H^q(X,E(t))`.
- In the second conjunct, `Module.finrank k` is applied to the degree-one
  `RingedSpace.moduleCohomology` object for `E(m)`, after `ModuleCat.restrictScalars`
  along `Scheme.globalSectionsRingHom k`. This is the canonical `k`-vector space
  structure induced by `X → Spec k`, not an arbitrary module structure or the
  dimension over the global-functions ring. The natural dimension is explicitly
  cast to `ℤ` before addition to `m`. Its finiteness follows from coherence and
  projective coherent finiteness, and is not an extra hypothesis.
- That conjunct quantifies every integer `t ≥ m+h` and asserts the requested
  vanishing of `H^1(X,E(t))`. There is no additional conclusion.
- All vanishings use `Subsingleton` on the underlying module-cohomology type,
  equivalent to the module being zero. The cohomology is the right-derived
  module-global-sections functor of the recorded dependency, throughout.

Dependency declarations read and used:

- `Field` (Mathlib); `Module.finrank` in `Mathlib.LinearAlgebra.Dimension.Finrank`.
- `AlgebraicGeometry.RingedSpace.IsCoherent`, from the recorded
  `Sheaf.AlgebraicGeometry.CoherentFiniteType` public import of
  `WeilConjectures.AlgebraicGeometry.Coherent`.
- `AlgebraicGeometry.ProjectiveSpace.twist` in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`.
- `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` in
  `WeilConjectures.AlgebraicGeometry.PQFCohomology`, exposing
  `AlgebraicGeometry.RingedSpace.moduleCohomology` (the actual functor used).
- `AlgebraicGeometry.IsClosedImmersion` in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `AlgebraicGeometry.Scheme.Modules.tensorPullback`, exposed by the recorded
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` module.
- `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus` in
  `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`.
- `AlgebraicGeometry.ProjectiveSpace.regularHyperplaneMultiplication` in
  `Sheaf.AlgebraicGeometry.CoherentRegularHyperplaneRestriction`.
- `Scheme.Modules.tensorObj` in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, using the established
  scoped notation `⊗ₘ` to keep the scheme-module category explicit during elaboration.
- `AlgebraicGeometry.Scheme.globalSectionsRingHom` in
  `WeilConjectures.AlgebraicGeometry.Cohomology.Defs` supplies scalar restriction.

The last two definition-node dependencies (zero scheme and canonical hyperplane
maps) are already landed. Their ids were added to `stmt_deps` under brief-stage2
§5 to cite the constructions used in the existing hypothesis, including the
omitted zero-scheme citation noted by the stage-1 reviewer. No new node or
statement correction is needed.

Proof dependencies are imported as ordinary imports:
`fixed_hyperplane_restriction_cohomology` in
`Sheaf.AlgebraicGeometry.FixedHyperplaneRestrictionCohomology`;
`mRegular_coherent_consequences` in
`Sheaf.AlgebraicGeometry.ProjectiveSpace.MRegularConsequences`;
`ProjectiveSpace.finite_H`, currently in
`WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveFinite` (also import the
recorded `Cohomology.Projective` module); and
`ProjectiveSpace.exists_subsingleton_H_tensor_twist` in
`WeilConjectures.AlgebraicGeometry.Cohomology.Serre`. Their full signatures and
proof docstrings were read. They supply the proof plan, not new hypotheses.

Edge cases checked before writing:

- `n=1`: `H ≅ P^0_k`; the regularity range is empty. Positive cohomology on `H`
  still vanishes, so the proof route applies. `n=0` is excluded exactly as in the node.
- `E=0` and `G=0`: permitted. Injectivity and both conclusions have their expected
  meanings; no nonzero-module hypothesis is present.
- `h=0`: the second bound starts at `m` itself; the zero source propagates along
  the surjections. No strict inequality is accidentally substituted.
- Negative `m` and negative twists: all degree parameters are integers; only
  cohomological degrees and the finite dimension are natural numbers.
- Finite fields and all characteristics: `s` is prescribed and regularity is
  assumed. No appeal to existence of an infinite-field hyperplane is made.
- The case `max(t,D)=t` in the higher-cohomology argument uses Serre vanishing
  immediately. The plateau propagation includes the first index `d` so its
  source is exactly `H^1(E(d-1))`.
- Arbitrary field universe `u` is bound explicitly. The scheme and module sizes
  follow the shared interfaces; the coordinate lift changes no projective dimension.

Searches for an existing statement:

- `msearch.py leanfinder`: “A coherent sheaf on projective space with m regular
  hyperplane restriction has higher cohomology vanishing at m and first cohomology
  vanishing at m plus its dimension”. Eight results, all abstract projective
  objects, resolutions or Tor vanishing; no matching geometric tail bound.
- `msearch.py loogle`: `"cohomology", "Projective"`. Twelve results on K-projective
  complexes and projective resolutions; none states the bound.
- `msearch.py grep`: `hyperplane|mRegular|tail_bound`, Mathlib `AlgebraicGeometry`.
  Zero hits. The wrapper retained the exact search outputs in `searches.jsonl`.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `hyperplane_cohomology_tail|cohomology_tail_bound|lem-sfb-hyperplane-cohomology-tail-bound`:
  no existing statement. Broader hyperplane/regularity searches identified the
  canonical maps and the two existing proof-dependency statements used above.
- DAG search read the already-landed `def-pc-zero-scheme` and
  `def-sfb-regular-hyperplane-restriction-maps`; neither was duplicated.

No `STATEMENT-DISPUTED` issue was found. The item is not a blueprint unit's own
statement; its source extraction and all hypotheses are unchanged.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
