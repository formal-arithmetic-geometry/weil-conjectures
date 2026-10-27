## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothFibreAffineRingAtPrime` states
`AlgebraicGeometry.smooth_fibre_affine_ring_at_prime`, with its proof `sorry`.
It introduces no definitions and changes only the item's `lean` field.
Source read: `literature/stacks-project/morphisms.tex`, lemma-smooth-at-point,
Tag 01V9, particularly the affine translation of (2) to (1). This translation
itself needs no finite-presentation or flatness assumption on the original map.

Clause-by-clause correspondence:

- The morphism of schemes is `{X S : Scheme.{u}} (f : X ⟶ S)`; its point is
  `(x : X)`. The base point `s = f(x)` is written `f x` throughout.
- Commutative coordinate rings are `(R A : Type u) [CommRing R] [CommRing A]`.
  The induced ring map φ is encoded as `[Algebra R A]`, with φ = `algebraMap R A`.
  This is arbitrary ring-map data, not a smoothness or finiteness assumption.
- The affine open charts `W = Spec A ⊆ X` and `V = Spec R ⊆ S` are
  `(iA : Spec (CommRingCat.of A) ⟶ X)` and
  `(iR : Spec (CommRingCat.of R) ⟶ S)`, with `[IsOpenImmersion iA]`
  and `[IsOpenImmersion iR]`. Their images are the opens W and V. Conversely,
  any specified affine open chart supplies precisely such an open immersion;
  arbitrary open immersions from spectra are charts on their images.
- `hsquare : iA ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iR`
  says both that `f(W) ⊆ V` and that its restriction to the charts is Spec φ.
  This is exactly the induced ring map: open immersions are monomorphisms, so
  the factorization is unique, and Spec is fully faithful. Conversely, the
  node's induced map satisfies this square. No independent arbitrary map is used.
- The prime representing x is `(q : PrimeSpectrum A)` with `(hx : iA q = x)`.
  Its contraction p is `PrimeSpectrum.comap (algebraMap R A) q`.
  In particular `iR p = f x` follows from hx and hsquare, so V contains s;
  no additional containment hypothesis is necessary.
- The residue field k is
  `(PrimeSpectrum.comap (algebraMap R A) q).asIdeal.ResidueField`.
  The implicit algebra in `Algebra.IsSmoothAtPrime` is on `p.asIdeal.Fiber A`.
  This is the required project convention in `coord/STATE.md`, FIBRE RING:
  `Ideal.Fiber` is `κ(p) ⊗[R] A`, with scalar map `λ ↦ λ ⊗ 1`.
  `Algebra.TensorProduct.comm R A k` identifies the node's `A ⊗[R] k`
  with this algebra, sending `1 ⊗ λ` to `λ ⊗ 1`. Thus the scalar structure
  and localization-smoothness assertion are exactly the node's.
- The prime Q is
  `PrimeSpectrum.preimageEquivFiber R A (PrimeSpectrum.comap (algebraMap R A) q)
    ⟨q, rfl⟩`.
  Its definition in `Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean`
  is literally `RingHom.ker` of the tensor lift of `Ideal.ResidueField.mapₐ`
  and `IsScalarTower.toAlgHom`. On a pure tensor λ ⊗ a it is the induced
  residue-field image of λ times the residue of a. Tensor symmetry identifies
  this with the node's specified ρ(a ⊗ λ) = ā λ̄. Thus this is the specified
  kernel, not an arbitrary prime lying above q and not a choice of a map.
- The scheme fibre and its map are `f.fiber (f x)` and
  `f.fiberToSpecResidueField (f x)`. Mathlib defines these as the pullback
  and its second projection along `S.fromSpecResidueField (f x)`.
- The unique fibre point over x is `f.asFiber x`, defined by the inverse of
  `f.fiberHomeo (f x)` at `⟨x, rfl⟩`. The source's uniqueness is built into
  that homeomorphism, rather than added as a new hypothesis.
- Smoothness on an open neighbourhood is exactly
  `hsmooth : ∃ N : (f.fiber (f x)).Opens,
    f.asFiber x ∈ N ∧ Smooth (N.ι ≫ f.fiberToSpecResidueField (f x))`.
  This is smoothness of the restriction to N, without asserting smoothness
  of the whole fibre or merely formal smoothness of its stalk.
- The conclusion `Algebra.IsSmoothAtPrime k Q` unfolds, in the recorded
  upstream declaration, to `∃ h : p.asIdeal.Fiber A, h ∉ Q.asIdeal ∧
    Algebra.Smooth k (Localization.Away h)`. This supplies precisely the
  requested h outside the kernel and the smooth localized ring map.

Dependency declarations used (full signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`: `Ideal.Fiber` and
  `PrimeSpectrum.preimageEquivFiber`, including its kernel formula.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `fiberHomeo`, `asFiber`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap` and `Scheme.Spec.residueFieldIso`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `WeilConjectures.RingTheory.SingularIdeal`: `Algebra.IsSmoothAtPrime`.
- `Mathlib.RingTheory.Smooth.Basic`: `Algebra.Smooth`.

The proof-dependency modules are imported without `public`: AffineScheme
(stalk localization and the chart square), Pullbacks (open fibre products and
`pullbackSpecIso`), OpenImmersion (principal localization), RingHomProperties
(`HasRingHomProperty.Spec_iff`), Prime.Topology (basic-open basis),
`WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField` and
`WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC`
(residue-map naturality). Smooth.lean already supplies restriction invariance.
All recorded proof dependencies have a declaration or Mathlib match; none is
omitted because of an import cycle.

Edge cases checked before writing:

- Empty X or the zero coordinate ring A admits no x/q satisfying the chart
  data. The theorem is correctly vacuous in those cases, exactly as the node.
  Empty S likewise admits no f with a point x in X.
- No finite presentation of A over R, flatness, Noetherianity, or assumptions
  on characteristic are inserted. The smooth neighbourhood, rather than an
  unstated global finiteness property, is the hypothesis used to find h.
- The fibre prime exists for every q, since p is its actual contraction.
  Its kernel is prime because the canonical tensor residue map has field
  codomain. No separate prime hypothesis on Q is added.
- The neighbourhood need only be smooth near the marked point, and need not
  be affine, quasi-compact, or the whole fibre. Intersecting with the affine
  fibre chart and taking a basic open is precisely the source proof.
- All schemes and their coordinate rings use the same arbitrary universe u;
  residue fields and Ideal.Fiber remain in u. There are no test-object
  quantifiers in a smaller universe, and `autoImplicit` is disabled.

Searches, all through the prescribed wrappers or read-only rg:

- `msearch.py ... leanfinder` query: "A smooth scheme fibre near a point
  implies that its affine tensor product fibre algebra is smooth at the kernel
  of the map to the residue field". Eight hits: standard-smooth chart existence,
  relative-dimension variants, `Algebra.IsSmoothAt`, and smooth base change.
  None is this result for arbitrary charts without global finite presentation.
- `msearch.py ... loogle` query: `Algebra.IsSmoothAt, PrimeSpectrum`.
  Zero hits.
- `msearch.py ... grep` query:
  `fiberToSpecResidueFieldIso|exists_notMem_smooth|smooth_appLE`.
  Ten hits in Smooth, SmoothFiber, Fiber, Normalization and Smooth/Locus.
  Read the fibre isomorphism and the localization theorem: the latter requires
  `[FinitePresentation R A]`, absent in this node. `Algebra.IsSmoothAt` alone
  is only formal smoothness of the localization, not the recorded notion.
- `msearch.py ... leansearch` query: "A smooth scheme fibre near a point gives
  smoothness at the residue-field kernel prime of the affine fibre algebra".
  Eight hits: scheme smoothness constructors, formal smoothness/locus,
  the fibre definition and finite-presentation consequences. No exact match.
- Read-only `rg` in `lean/WeilConjectures` for the item's blueprint id found
  no declaration. Searches for `IsSmoothAtPrime` and smooth fibre statements
  found `flat_smooth_fibre_smooth_at_prime`, whose hypothesis is the desired
  ring smoothness, not its derivation from scheme fibre smoothness.
- Read-only `rg` in `lean/Sheaf` for the proposed name and smooth fibre/affine
  wording found consumers in `FlatSmoothPointBaseChange` and other smoothness
  statements, no declaration of this comparison. Read the singular-ideal and
  fibre-prime implementations rather than introducing copies of them.

Validation: prescribed `scompile.py Q46 lem-trf-smooth-fibre-affine-ring-at-prime
<module>` passed: sandbox and library module, 2.0 s and 2.1 s, exit code 0,
no errors or unexpected warnings. No direct Lean/Lake build or git operation
was run in the shared repository.

No statement correction, new nodes, dependency repairs, or disputed mathematical
claims are needed.

## Second reading by Q46

A separate pass by this worker reopened the node and the finished module;
the dispatcher explicitly forbids starting another agent. The maintainer's
independent review is supplied by the normal delivery process, not claimed here.
The pass checked the chart images, the induced-map square, hx, the contraction
prime, both tensor scalar maps, the actual kernel formula in preimageEquivFiber,
the unique fibre point, the existential smooth neighbourhood and the full
principal-localization conclusion. In particular it checked that the use of
`Ideal.Fiber` follows the explicit project tensor-order convention and preserves
ρ after symmetry, and that no finite-presentation hypothesis slipped in.
The dependency interfaces are all usable without changes. No mismatch was found
and no change to the mathematical node or theorem was made during this pass.
