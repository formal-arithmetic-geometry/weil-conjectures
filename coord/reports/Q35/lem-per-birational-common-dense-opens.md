## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.BirationalCommonDenseOpens` states
`AlgebraicGeometry.exists_common_dense_opens_isIso_of_generic_stalks`, with its entire
proof postponed as `sorry`. It is Stacks Project, Morphisms, Tag 0BAC(2),
`lemma-birational-birational`, with birationality expanded according to
`definition-birational` (Tag 0BAA). I read the local source in
`literature/stacks-project/morphisms.tex`, lines 12970–13120. The node's orientation
is Y → X, consistently reversing the letters in Stacks. The optional base in
Stacks is irrelevant to this common-open conclusion and is not part of the node.

Each hypothesis and conclusion is rendered as follows:

- Schemes and the given morphism: `{X Y : Scheme.{u}} (f : Y ⟶ X)`.
  Universe `u` is explicit and arbitrary.
- Locally of finite presentation: `[LocallyOfFinitePresentation f]`.
- Finitely many irreducible components of X and of Y: respectively
  `hX : (irreducibleComponents X).Finite` and
  `hY : (irreducibleComponents Y).Finite`.
- The map bijects the component generic points:
  `hgeneric : Set.BijOn f (genericPoints Y) (genericPoints X)`.
  Mathlib defines `genericPoints Z` as the points whose singleton closure is an
  irreducible component of Z. Thus this uses exactly the recorded generic-point
  and irreducible-component definitions. `Set.BijOn` includes mapping into the
  target set, injectivity on the source set, and surjectivity onto the target set.
- For every such source generic point, the induced local-ring map is an
  isomorphism: `hstalk : ∀ η ∈ genericPoints Y, IsIso (f.stalkMap η)`.
  The signature read in Scheme.lean is
  `f.stalkMap η : X.presheaf.stalk (f η) ⟶ Y.presheaf.stalk η`.
  This is the given induced map, rather than an unspecified ring isomorphism.
- The two open subschemes: `∃ (U : Y.Opens) (V : X.Opens)`; Mathlib's
  `Scheme.Opens.toScheme` equips them with the restricted structure sheaf.
- Density on both sides: `Dense (U : Set Y) ∧ Dense (V : Set X)`.
- Image containment: `∃ hUV : U ≤ f ⁻¹ᵁ V`, equivalently f(U) ⊆ V.
- The restriction is an isomorphism: `IsIso (f.resLE V U hUV)`.
  In Mathlib.AlgebraicGeometry.Restrict, `Scheme.Hom.resLE f V U hUV`
  is the composite of the inclusion U → f⁻¹V with the usual restriction of f;
  `resLE_comp_ι` states that its composite with V.ι is U.ι ≫ f.
  Thus the conclusion specifies the canonical restriction of the given f.
- There are no separatedness or reducedness binders, and hUV is only an
  inclusion; no equality U = f⁻¹V is required.

Dependency declarations read and used:

- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-sbc-locally-finite-presentation`:
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation,
  `AlgebraicGeometry.LocallyOfFinitePresentation`, the affine-local ring-map
  finite-presentation class recorded in the dependency.
- `def-weil-irreducible-components`: Mathlib.Topology.Irreducible,
  `irreducibleComponents`, defined as `{s | Maximal IsIrreducible s}`.
- `def-sc-generic-point`: Mathlib.Topology.Sober, `IsGenericPoint` (singleton
  closure equals the specified subset); `genericPoints` packages its application
  to components, so no new generic-point notion is introduced.
- `def-weil-locally-ringed-space-morphism`:
  Mathlib.Geometry.RingedSpace.LocallyRingedSpace,
  `AlgebraicGeometry.LocallyRingedSpace.Hom`; scheme morphisms extend it and
  `Scheme.Hom.stalkMap` is its induced stalk map.
- `def-weil-open-immersion`: Mathlib.AlgebraicGeometry.OpenImmersion,
  `AlgebraicGeometry.IsOpenImmersion`; the open-subscheme inclusions supplied by
  Mathlib.AlgebraicGeometry.Restrict are instances of this property.

The statement dependency modules are public imports. Proof-only imports are
Mathlib.AlgebraicGeometry.Properties (scheme sobriety),
Mathlib.AlgebraicGeometry.AffineScheme (affine basis, Spec square and stalk
localizations), Mathlib.RingTheory.FinitePresentation (finite generation of the
surjection kernel), and Mathlib.RingTheory.Spectrum.Prime.Topology (minimal primes
and components). The locally-finite-presentation affine-ring lemma and principal
localization open immersion are in the already public imports. The only proof
dependency without a recorded declaration is
`lem-per-birational-generic-localization`, so it has no module to import yet; it
is identified in the five-step proof docstring. It is not a statement prerequisite.

Edge cases checked before writing:

- Both schemes empty: take the empty opens; they are dense in the empty spaces
  and the empty restriction is an isomorphism. A bijection on component generic
  points cannot identify an empty scheme with a nonempty scheme, by sobriety and
  existence of components.
- Identity on any scheme with finitely many components: take both full opens.
  This includes Spec(k[ε]/ε²), so nilpotents are permitted.
- The line with doubled origin mapping to the affine line is locally of finite
  presentation, bijects generic points, and identifies the generic local rings.
  It admits common dense opens despite being nonseparated. A single branch is
  already a dense open isomorphic to the full target; its inclusion in the full
  preimage is strict. This checks that the conclusion does not accidentally
  assert an isomorphism on the full preimage.
- Several components meeting each other: finite unions of the other closed
  components have open complements containing the selected generic points.
  The resulting pairwise disjoint opens justify the node's gluing argument.
- Stacks' non-finite-presentation birational examples do not violate this
  statement; the finite-presentation binder remains essential to killing the
  finitely generated kernel on an open.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “A locally finitely presented birational morphism
  of schemes with finitely many irreducible components identifies dense open
  subschemes without reducedness or separatedness”. Eight hits: dominant-map
  extensionality, IsPreimmersion, rational-map dense domain, the finite
  presentation class and related facts; no common-open existence theorem.
- `msearch.py ... loogle`: `AlgebraicGeometry.LocallyOfFinitePresentation,
  genericPoints`. Zero hits.
- `msearch.py ... grep`: `birational|dense.*[Ii]so|[Ii]so.*dense`, subdirectory
  AlgebraicGeometry. Twenty-one hits, principally the PartialIso/Birational
  definitions and dense-site material. I read Birational/Birational.lean;
  PartialIso describes the desired sort of object but gives no spreading theorem
  from the generic-stalk hypotheses.
- `rg` over upstream WeilConjectures for birational/common-dense/genericPoints,
  and `grep -rn` for this item id: no matching upstream statement. The upstream
  ChowLemma/Reduction generic-point covering lemmas are different statements.
- `rg` over project lean/Sheaf for birational/common-dense/genericPoints/0BAC:
  the existing BirationalDenseOpenIso theorem requires separatedness and gives an
  isomorphism on a full preimage (Tag 0BAJ), so cannot replace this node.
  NormalModificationCodimensionOne has additional properness and other
  hypotheses. Neither is duplicated.
- Checked proposed declaration names against dag/lean_names_upstream.json and
  project sources; no existing declaration of the new name.

No new nodes, dependency repairs, statement corrections, or disputed statements.
The original node is changed only in `lean`. Compilation through the prescribed
scompile.py wrapper passed for both sandbox and library contexts (2.1 s and
2.0 s); no errors or warnings were printed.

## Second reading by Q35

I reopened the node and the completed signature for a separate second pass.
The two finite-component hypotheses, the direction Y → X, the BijOn condition,
and the actual contravariant stalk map all agree with the node. I checked the
resLE argument order against its full signature: target open V first, source
open U second, followed by the inclusion proof. Its source is U.toScheme and
its target is V.toScheme. The two density conjuncts and the existential inclusion
proof give exactly the stated conclusion. There are no separatedness,
reducedness, nonemptiness, or full-preimage-equality assumptions. No mismatch was
found and no statement was changed. This is the writer's second pass, not a
claim of an independent agent review; the dispatcher explicitly forbids starting
other agents, and the maintainer supplies the independent delivery review.
