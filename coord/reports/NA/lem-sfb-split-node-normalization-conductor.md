## Worker report

The module `Sheaf.AlgebraicGeometry.SplitNodeNormalizationConductor` states the entire
unchanged node in three theorems, all with whole-proof `sorry`:
`AlgebraicGeometry.splitNode_affine_normalization`,
`AlgebraicGeometry.splitNode_normal_domain_identity`, and
`AlgebraicGeometry.splitNode_normalization_conductor`.
All helper definitions contain actual data and are public, with explicit binders and universe `u`.
They only spell out the coordinate rings, inclusion maps, and concrete pullback occurring in
this node; there is no new independent mathematical notion and no dependency repair.

Clause-by-clause reading of the general assertion:

- A reduced Noetherian commutative ring is `(T : Type u) [CommRing T]
  [_root_.IsReduced T] [IsNoetherianRing T]`.
- The complete, nonrepeating list of minimal primes is `(t : ℕ)
  (p : Fin t → PrimeSpectrum T)`, `Function.Injective p`, and
  `Set.range (fun i ↦ (p i).asIdeal) = minimalPrimes T`.
  `PrimeSpectrum T` supplies the prime instances on the quotient rings.
- The fraction fields are exactly `FractionRing (T ⧸ (p i).asIdeal)`.
  `Fractions T p` is their product; `Components T p` is the product of the recorded
  `integralClosure (T ⧸ (p i).asIdeal) (FractionRing (T ⧸ (p i).asIdeal))`.
- `componentMap` is explicitly the product of the quotient maps followed by the algebra
  maps into the individual integral closures. `inclusion` is the coordinatewise inclusion
  in the product of fraction fields. `fractionMap` is their composite.
- The first conjunct of `splitNode_affine_normalization` equates integrality over this
  structural map (`RingHom.IsIntegralElem`) with membership of every coordinate in the
  corresponding `integralClosure`. This states equality with the integral closure of T
  in the product, without introducing an alternate integral-closure definition or an
  arbitrary algebra structure.
- The existential scheme isomorphism identifies the recorded `Scheme.reducedNormalization`
  of `Spec T` with `Spec (Components T p)`. Its following equation identifies its
  structural morphism with `Spec.map (CommRingCat.ofHom (componentMap T p))`.
- For every `s : T`, the `es` isomorphism identifies the inverse image of
  `PrimeSpectrum.basicOpen s` with the spectrum of the localization of `Components T p`
  at `componentMap T p s`. Its equation is the restriction square with the very same `e`.
  The actual localized inclusion `Localization.awayMap (inclusion T p) ...` is injective,
  and its range is exactly the elements integral over the localized structural map
  `Localization.awayMap (fractionMap T p) s`. Thus both the scheme chart and the
  integral-closure description commute with restriction. Localizing the product also
  automatically removes coordinates on which s is zero and localizes the other closures.
- The separate normal-domain theorem retains Noetherian T and uses `[IsDomain T]
  [IsIntegrallyClosed T]`. It gives an isomorphism to `Spec T` whose hom is the actual
  normalization map: under this identification the map is the identity.
- There is no nonempty restriction on `Fin t`: `t = 0` gives the product over an empty
  index type, a singleton ring, i.e. the zero ring. The covering condition then forces
  the reduced ring T to be zero. This uses Mathlib's existing empty product convention.

Clause-by-clause reading of the split-node assertion:

- `(R : Type u) [CommRing R] [IsDomain R]` and
  `IsField R ∨ IsDiscreteValuationRing R` say precisely field or DVR; the domain
  instance is part of either alternative, not an added mathematical hypothesis.
- `Node R` is literally `MvPolynomial (Fin 2) R ⧸ Ideal.span {X 0 * X 1}`,
  with its explicit coefficient type. `Polynomial R × Polynomial R` is E.
- `branchEvaluation` evaluates at `(u,0)` and `(0,v)`. The equation
  `j.comp (nodeQuotient R) = branchEvaluation R` characterizes the canonical Q → E
  on every polynomial, in particular the stipulated images of u and v. The analogous
  equation for `ε` specifies evaluation at the common origin.
- `Function.Injective j` and the formula for membership in `j.range` identify Q with
  exactly those branch pairs having equal constants. `origins` is the product of
  the two `Polynomial.evalRingHom 0` maps.
- The normalization isomorphism and its structural equation identify E with the
  componentwise normalization algebra using the existing scheme normalization notion.
- `j.Finite` is finiteness as a Q-module. The next conjunct says every element of E
  is the evaluation of a polynomial over Q at `(1,0)`, exactly E = Q[e].
- The ideal I is characterized by `a ∈ I ↔ ∀ b, j a * b ∈ j.range`, exactly the
  conductor definition in the node. It is then equated with the ideal spanned by
  the classes of u and v.
- `Set.image j (I : Set (Node R))` is equated with
  `(Ideal.span {Polynomial.X}).prod (Ideal.span {Polynomial.X})`, precisely
  uR[u] × vR[v]. `I.map j` is equated with that same product ideal, so IE = I
  under the specified injection. We do not conflate an ideal of Q with an ideal of E.
- The two quotient ring equivalences identify Q/I with R and E/IE with R × R;
  their equations on quotient classes specify the actual origin evaluations.
- `conductorPullback R` uses Mathlib's `RingHom.eqLocus` on E × R, imposing exactly
  `origins b = (r,r)`. The ring equivalence Q → this pullback has value `(j a, ε a)`,
  specifying the canonical map and the diagonal rather than an arbitrary equivalence.
  Its membership condition also specifies the induced diagonal on conductor quotients.
- `Smooth (Spec.map ... Polynomial.C)` states that each branch is smooth over R.
  The origin is `Spec R` with the zero-section morphism induced by evaluation at zero;
  the second smoothness clause uses its composite with the branch structure map.
  The two copies of the branch and of its origin have identical structural morphisms,
  so one clause for each common formula states smoothness of both copies. This does
  not assert that the closed origin immersion into an affine line is smooth.

Dependency declarations read and used:

- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, with
  `RingHom.IsIntegralElem` from its exported `IsIntegral.Defs`; their membership
  definition is precisely roots of monic polynomials for the given ring map.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`, sectionwise
  reducedness, exported through the normalization imports. For rings the general theorem
  uses the existing root `IsReduced` class.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`, extending
  local and principal ideal ring structures with nonzero maximal ideal, with `IsDomain`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalizationComponent`,
  `Scheme.reducedNormalization`, and `Scheme.fromReducedNormalization`. These are the
  actual disjoint union of function-field normalizations of reduced induced components.
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`; the two-variable presentation uses
  the existing `MvPolynomial` and quotient constructions, and evaluations use Mathlib's
  `Polynomial.evalRingHom`, `Polynomial.eval₂`, and `MvPolynomial.eval₂Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.

The recorded proof dependencies already stated are available through the ordinary proof
imports: `Mathlib.AlgebraicGeometry.Noetherian`,
`Mathlib.RingTheory.Spectrum.Prime.Topology`, `Mathlib.RingTheory.Localization.Integral`,
`Mathlib.RingTheory.PrincipalIdealDomain`, `Mathlib.RingTheory.Polynomial.IsIntegral`,
`Mathlib.AlgebraicGeometry.AffineSpace`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
The recorded normalization and finite affine coproduct constructions are exported by
`ReducedNormalization` and its `Mathlib.AlgebraicGeometry.Limits` import.
`lem-sfb-normalization-generic-residue-affine-charts` has no recorded declaration, so
there is no module to import for this proof-only dependency. It is named explicitly
in the proof docstring; the statement uses no hypothetical interface from it.

Sources read: local `literature/stacks-project/morphisms.tex`,
`lemma-description-normalization` (035P), `lemma-normalization-in-terms-of-components`
(0CDV), and `literature/stacks-project/models.tex`,
`lemma-etale-local-at-worst-nodal` (0CDD). The latter gives the actual uv = 0 chart;
the extra explicit algebra calculations are the node's recorded agent proof. These
sources support the unchanged node. No disputed statement or correction was needed.

Edge cases checked before finalizing:

- T = 0 and t = 0: both product rings are zero and both spectra are empty. No field
  structure is demanded for an empty family of quotient fraction rings.
- T a field or a normal Noetherian domain: the one-component normalization is the
  identity. A product of fields keeps every component, so connectedness is not imposed.
- s = 0: all localized rings in the restriction clause are zero and the open is empty.
  s = 1: the principal open is the whole spectrum. A zero divisor s can kill selected
  fraction-field factors; the ambient localization, rather than a field-only localization,
  handles this case.
- R of characteristic 2: the idempotent computation uses no division by 2; the formula
  b = q + de and the monic equation remain valid.
- A nonexcellent DVR: normalization of the explicit node is finite by its two module
  generators, independently of any general finiteness theorem for normalization.
- Both origin schemes are copies of Spec R, smooth over R, including the DVR base.

Searches for existing statements and constructions (2026-10-24):

- `msearch.py ... leanfinder "normalization reduced noetherian ring product fraction fields
  minimal primes split node conductor quotient xy"`: eight hits, mostly Kummer–Dedekind
  conductor results, no affine normalization plus split-node calculation.
- `msearch.py ... loogle "integralClosure, Polynomial, RingHom.range"`: zero hits.
- `msearch.py ... leansearch "normalization of reduced noetherian ring is product of
  integral closures of minimal prime quotients"`: eight hits, including finite minimal
  primes, normal closures and relative-normalization properties; no complete statement.
- `msearch.py ... grep 'conductor|normalization.*minimal|integralClosure.*[Pp]i' RingTheory`:
  18 hits, including `Mathlib.RingTheory.Conductor`; that conductor is the conductor
  of a singly generated subalgebra R<x> inside an extension, not this specified Q → E.
  The statement therefore uses the node's explicit conductor membership formula and
  Mathlib's existing ideal constructions.
- `rg` in `lean/WeilConjectures` for this node id: no hits. Searches in both
  `lean/WeilConjectures` and `lean/Sheaf` for split nodes, conductor, affine normalization,
  and product integral closures found reduced-normalization and affine-chart modules,
  completed nodal rings, and other conductor results. None contains this node's complete
  statement or its explicit polynomial conductor calculation. The existing
  `ComponentwiseNormalizationAffineCharts` was read; its generic affine description
  does not contain the localization and explicit split-node clauses, and its DAG node
  is dropped according to this item's accepted review, so it is not imported.
- Name searches in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no existing `AlgebraicGeometry.SplitNodeNormalization`
  namespace or the three new theorem names. Existing occurrences of `componentMap`
  or `fractionMap` are in other namespaces and describe other objects.

Validation: `scompile.py NA lem-sfb-split-node-normalization-conductor <module>`
compiled both sandbox and final library module cleanly (11.4 s and 14.1 s), under the
fixed 60-second per-file limit. Initial elaboration diagnostics were repaired by
annotating the coefficient type in the uv ideal, using `CommRingCat.ofHom` explicitly,
and writing the ideal-to-set coercion explicitly. Only the sandbox was edited.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
