## Worker report

The module `Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound` states
`AlgebraicGeometry.Etale.gabber_strictLocal_torsion_bound`. Its only theorem has proof
`sorry`; it introduces no new definition, construction, hypothesis, or auxiliary node.
The node is changed only in `lean`.

Source checked directly: Illusie, *Around the Thom-Sebastiani theorem*,
[author PDF](https://www.imo.universite-paris-saclay.fr/~luc.illusie/Illusie-nearby-cycles28.pdf),
Theorem 1.14 and Corollary 1.15, printed pp. 15–16 (PDF pages 15–16).
The theorem assumes a Z/m-algebra and a locally finite type map with fibre dimension
bounded by N. The corollary concerns every module sheaf on the source strict
localization and higher direct images along the induced map. No invertibility,
Noetherianity, finite coefficient ring, or constructibility hypothesis is added.
The source corollary agrees with the node; no statement correction is needed.

Hypotheses and clauses:

- `m : ℕ` and `hm : 1 ≤ m` mean the positive integer m.
- `Λ : Type (u + 1)` and `[CommRing Λ]` mean a commutative coefficient ring.
  `hΛ : ∀ a : Λ, (m : Λ) * a = 0` is exactly mΛ = 0, equivalently the
  unital Z/m-algebra condition. It does not assert that Λ is finite.
- `{X S : Scheme.{u}}`, `f : X ⟶ S` and `[LocallyOfFiniteType f]` give precisely
  the stated morphism and local finite type hypothesis, with no quasi-compactness
  hypothesis on f.
- `N : ℕ` gives an integer N ≥ 0. `hN : ∀ s : S, topologicalKrullDim (f.fiber s)
  ≤ (N : WithBot ℕ∞)` bounds every scheme-theoretic fibre's topological dimension.
  The conclusion is stated for each supplied bound N, which gives exactly the
  conclusion for a witness to the node's existential bound.
- `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and `x : Spec (.of Ω) ⟶ X` give an
  arbitrary geometric point. The image geometric point s is the composite `x ≫ f`.
- `Scheme.strictHenselizationScheme x` and
  `Scheme.strictHenselizationScheme (x ≫ f)` are X_(x) and S_(s).
  `Scheme.strictHenselizationMap f x` is the existing canonical induced map:
  its unique characterization includes the structural square and compatibility
  with the distinguished geometric-point evaluation maps. It is not an arbitrary
  map commuting with the structural maps.
- `G : Sheaf (Scheme.strictHenselizationScheme x).smallEtaleTopology
  (ModuleCat.{u + 1} Λ)` quantifies over every constant-coefficient module sheaf
  on the small etale site. It is not restricted to an ambient restriction or to
  a constructible sheaf.
- `q : ℤ` and `hq : 2 * (N : ℤ) < q` express exactly q > 2N.
- `DerivedCategory.Plus.singleFunctor ... 0` places G in degree zero;
  `rightDerivedLowerStarPlus ... (Scheme.strictHenselizationMap f x)` applies
  the existing bounded-below derived direct image; and
  `DerivedCategory.Plus.homologyFunctor ... q` takes its q-th cohomology sheaf.
  `IsZero` of that object is precisely R^q f_(x)*G = 0 in the target module-sheaf
  category, not just a vanishing of global sections or of a selected stalk.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`
  (pullback along the canonical residue-field point).
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, defined as the
  order Krull dimension of irreducible closed subsets.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, used in the inline
  geometric-point encoding of def-weil-geometric-point. The corresponding
  `Scheme.SpecToEquivOfField` signature/docstring in ResidueField.lean was also read.
- `Sheaf.AlgebraicGeometry.StrictHenselization`:
  `AlgebraicGeometry.Scheme.strictHenselizationRing`, `strictHenselizationScheme`
  and `strictHenselization_properties`; the scheme is the spectrum of the
  canonical affine pointed-neighbourhood coordinate-ring colimit.
- `Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift` is the recorded module
  for lem-weil-pbc-strict-henselization-functoriality. It publicly imports
  `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`, whose
  `AlgebraicGeometry.Scheme.strictHenselizationMap` is used directly. Its
  `strictHenselizationMap_existsUnique` and `strictHenselizationMap_over`
  signatures and docstrings were read. The recorded `strictHenselizationClosedLift_over`
  and its docstring were also read; no dependency repair is needed.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`, read via
  `scompile.py --source`: identifies the module-sheaf encoding, the derived,
  bounded below and bounded categories and homology functors. The same encoding
  is used here. Its `torsionCohomology` is not needed because G[0] is the input.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, defined by restriction along etale
  base change. The recorded derived declaration is supplied by the publicly
  imported `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus`, whose full signature
  and docstring were read via `scompile.py --source`. It is exactly
  `(lowerStar A f).rightDerivedFunctorPlus`.

Every recorded proof prerequisite with a module is imported, using non-public imports
when needed only for the future proof. Mathlib geometry/limits proof prerequisites
are supplied by the separated, affine, flat-mono, affine-scheme and directed-category
imports (and their public imports). The complete nine-step node proof, with its
prerequisite IDs, appears in the theorem docstring. The following proof-only nodes
have no Lean module recorded at this reading and therefore have no import yet:
`lem-trf-gabber-nearby-cycle-dimension-bound`, `lem-trf-oriented-point-cohomology`,
`lem-pe-constant-left-module-inverse-image`, `lem-trf-ind-etale-strict-local-invariance`,
`lem-pe-left-module-derived-evaluation-forget`.
They are not needed to state this theorem.

Edge cases checked before writing:

- m = 1 and the zero ring are allowed; all unital Λ-modules are then zero.
- No invertibility of m is imposed, so residue characteristics dividing m remain covered.
- An infinite Λ annihilated by m is allowed. The future proof reduces to finite Z/m;
  it does not apply finite-ring constructible approximation to Λ itself.
- N = 0 yields vanishing in all positive degrees, including locally quasi-finite f.
- Empty fibres have dimension bottom in WithBot ℕ∞ and satisfy the inequality.
- Empty X gives an empty geometric-point quantification; empty S forces this case.
- The strict inequality excludes q = 2N; the theorem makes no claim in degree zero.
  Integer q covers precisely the same permitted degrees as natural q since N ≥ 0.
- No global finite type, separatedness, quasi-compactness, or constructibility
  assumption has been added. The strict-local map is affine for proof purposes.
- Scheme and geometric-field universes are u, and coefficient modules have the
  established u+1 size. No test-object quantification uses an independent smaller
  universe. Every variable and universe is explicitly bound; autoImplicit is false.

Searches for an existing declaration (fresh msearch logs in searches.jsonl):

- LeanFinder: “For a locally finite type morphism with fibre dimension bounded by N,
  torsion etale higher direct images on strict localizations vanish above 2N”.
  Eight results about etale morphisms/localization, no cohomological bound
  (digest dbed0ea0f16260ef).
- Loogle: `"rightDerived"`. Twelve general derived-functor declarations, including
  HasRightDerivedFunctor and totalRightDerived; no strict-local theorem
  (digest a76fcf1e7b9a51a3).
- Mathlib grep through msearch: `Gabber|strict.*local.*cohomolog|cohomologicalDimension`
  in AlgebraicGeometry: zero hits (digest 4f53cda18c2baa0c).
- LeanSearch: “Gabber strict local etale higher direct images torsion vanish above
  twice fibre dimension”. Eight etale or complex boundedness results; none matches
  (digest 0440997adb373528).
- Direct rg of WeilConjectures and lean/Sheaf for Gabber, strict-local bounds and
  strictHenselizationMap: unrelated Gabber results and the existing canonical map;
  FiniteTypeTorsionUniversalStar is the downstream universal local-existence bound,
  not this fixed-fibre-dimension theorem. It is deliberately not imported.
- Direct rg of upstream WeilConjectures for the exact item ID, and of
  dag/lean_names_upstream.json for the ID/bound: no existing binding.

No STATEMENT-DISPUTED flag, node fault, new node, or dependency repair.

## Second reading by Q57

This is a fresh in-thread rereading of the node and final Lean file. The dispatcher
expressly forbids starting another agent, so no independent reader is claimed here;
the maintainer's independent review remains to be done.

Rechecked the positive m binder, annihilation of all Λ elements, arbitrary locally
finite type f, natural nonnegative N, every scheme-theoretic fibre via f.fiber, and
its dimension in WithBot ℕ∞. Rechecked the arbitrary algebraically closed geometric
point x, the composite x ≫ f, and the canonical strict-local map from the recorded
functoriality interface. Rechecked that G is any Λ-module sheaf on X_(x), that q is
strictly greater than 2N, and that the conclusion is IsZero of the target cohomology
sheaf after derived pushforward of G[0]. No hypothesis or clause is missing, and no
cohomological-dimension bound or invertibility assumption is smuggled in. The source
corollary and theorem were open for this comparison. No mismatch required a change.

## Validation

Compilation and delivery preflight results are recorded below after the wrapper runs.

`scompile.py Q57 lem-trf-gabber-strict-local-torsion-bound <module>` passed:
sandbox compilation 27.5 s and library-path compilation 7.0 s, with no errors
or warnings. No global build was run.
