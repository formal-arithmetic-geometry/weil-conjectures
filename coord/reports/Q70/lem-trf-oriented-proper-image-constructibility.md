## Worker report

The module `Sheaf.Paper.OrientedProperImageConstructibility` states
`AlgebraicGeometry.OrientedProperImage.proper_image_constructibility`. Its only
postponed proof is this theorem, with all thirteen steps of the DAG proof included
in its docstring. All helper definitions have actual data. The mathematical node
statement is unchanged.

Hypothesis and clause correspondence:

- Schemes X, Y, S are `Scheme.{u}`. Noetherian S is `[IsNoetherian S]`, precisely
  locally Noetherian plus quasi-compact, matching the two recorded dependency notions.
- The maps are `h : X ⟶ Y`, `g : Y ⟶ S`, and f is the actual composite `h ≫ g`.
  Finite presentation for each map is rendered by `LocallyOfFinitePresentation`,
  `QuasiCompact`, and `QuasiSeparated`, exactly the scheme-conventions dependency.
  Properness is `[IsProper h]`, the recorded Mathlib property.
- The finite commutative coefficient ring is `Λ : Type v` with `[CommRing Λ]`
  and `[Finite Λ]`. `N : ℕ`, `(N : Λ) = 0`, and `IsUnit (N : Γ(S, ⊤))` say
  it is killed by an integer invertible on S. A natural-number magnitude represents
  any integer annihilator, with the same unit condition; positivity is not imposed.
- `sourceMorphism h g` is exactly `squareModules g (h ≫ g) h (𝟙 S)` with its
  canonical composition-with-identity equation. `.modulePush` is the actual right
  adjoint of constant-module inverse image, and `.push` its recorded K-injective
  right derived functor. No arbitrary functor is quantified or chosen.
- `cohomology` explicitly uses `HasDerivedCategory.standard`, the same localization
  as `Site.derived`, so its object is the actual derived cohomology sheaf.
- The first conjunct quantifies over all `VanishingDerived (h ≫ g) Λ` objects L
  and assumes `IsBounded` for the standard derived t-structure. Every integral-degree
  cohomology object is assumed constructible, and the conclusion asserts the same
  for every integral-degree cohomology object of the actual derived direct image.
- `IsConstructible` is only an abbreviation applying
  `OrientedConstructibleSheaf.IsConstructible` after `constructibilityTransport`.
  That transport uses the canonical identity-base-change comparison on triples,
  restriction along the commutative-ring sheafification unit to fixed scalars,
  sheafified left Kan extension along that site isomorphism, and the recorded
  fixed-ring/constant-ring module equivalence. Thus it retains the dependency's
  finite constructible locally closed source/base stratifications and finite local
  module values. It introduces no alternative constructibility criterion.
- Under `IsFinite h`, `PreservesFiniteLimits` and `PreservesFiniteColimits` express
  exactness of this very module direct-image functor. The following equivalence is
  constructibility of every module sheaf F iff constructibility of its direct image;
  F is not assumed constructible in the reverse implication.
- The last clause quantifies over arbitrary algebraically closed Ω, Ξ, geometric
  y and t, and an oriented specialization c. `fieldPoint x` is the canonical point
  of Spec Ω composed with the scheme-induced étale morphism x; `fieldPointComp`
  supplies the prescribed associativity/base-change comparison.
- The fibre index is the subtype `{x : Spec (.of Ω) ⟶ X // x ≫ h = y}`. For a finite
  morphism this has exactly one element for each topological point of the geometric
  fibre (every residue field is Ω); nilpotents produce no repeated points. The
  conclusion includes finiteness of this actual index.
- `fibreOrientation` transports c using the actual equation xh=y and the canonical
  composition isomorphisms. `stalk` is constant-module inverse image along the
  existing universal oriented lift of these actual geometric points.
- The final `Nonempty` asserts a natural isomorphism of functors from sheaves on
  V_f to punctual-site modules, between the stalk of direct image and the product
  of precisely these stalks. Applying to any F gives its requested product formula.
  The punctual site is the dependency's one-object presentation of sets, so its
  constant-module category is canonically the category of coefficient modules.
  This conclusion is an isomorphism statement, not a choice used to define data.

Dependency declarations used:

- `Sheaf.Paper.OrientedNearbyCycles`: `etaleBaseChange`, `etaleComposition`, `lift`,
  `moduleMorphism`, `Coeff`, `vanishingDatum`, `VanishingDerived`, `IsBounded`, and
  `squareModules` (the recorded morphism induced by a commutative square).
- `Sheaf.Paper.OrientedConstructibleSheaf`: `ProductSite`, `productTopology`,
  `Modules`, `IsConstructible`, with the original finite-stratification definition.
- `Sheaf.Paper.OrientedProductPointsConservative`: `geometricEtalePoint`,
  `punctualSite`, `sheaf_isTopos`; its node is added as an already recorded statement
  dependency because the helpers use its canonical point construction.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`;
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points use the
  dependency's inline algebraically closed field and morphism encoding, equivalently
  `Scheme.SpecToEquivOfField` from `Mathlib.AlgebraicGeometry.ResidueField`.
- The scheme-conventions dependency fixes no declaration; its finite-presentation
  convention is used literally as the three Mathlib properties above.
- Every recorded proof-dependency module is imported. Proof-only imports use plain
  `import`; unrecorded proof nodes do not require fabricated modules.

Edge cases checked before writing: empty schemes and empty geometric fibres (the
empty product of modules is zero); the zero coefficient ring; nilpotent finite
fibres (the geometric points count supports rather than lengths); non-surjective
finite h (detection requires no surjectivity); arbitrary positive and negative
cohomology degrees and bounded objects with arbitrary finite support interval.
The schemes have universe u and coefficients an independent v, with only the
canonical `ULift` from the recorded framework. No equality of these universes is
imposed. Arbitrary field extensions representing geometric points in universe u
are included. The Ω-valued lifts suffice for finite geometric fibres even for
purely inseparable finite maps, since Ω is algebraically closed.

Searches for existing statements and helpers:

- msearch LeanFinder: “proper direct image constructible sheaves oriented product
  vanishing topos finite stalk product”: eight unrelated limit and condensed-sheaf
  results; no matching declaration.
- msearch Loogle: “PreservesFiniteLimits, PreservesFiniteColimits”: no hits, unknown
  identifier reported by that service.
- msearch grep: “constructible|Constructible” in Mathlib CategoryTheory: no hits.
- msearch LeanSearch: proper direct image preserving constructibility on a vanishing
  topos, finite exactness and finite stalk products: exact-functor definitions and
  ordinary étale pullback facts only; no oriented direct-image theorem.
- rg on upstream WeilConjectures, project lean/Sheaf and dag/lean_names_upstream.json:
  no existing theorem for this item or declarations with the new full names.
  Ordinary proper/finite étale constructibility results use a different topos and
  are proof inputs, not replacements for this node. Existing oriented point and
  constructibility constructions are imported and retained.
- Read the full recorded dependency signatures/docstrings and opened Orgogozo's
  cited paper, §§9.1.1--9.1.2 and Lemma 8.3.3. The first is the proper fibre formula;
  the second gives constructibility; the last underlies finite detection.

No statement correction, disputed statement, new independent notion, or dependency
replacement is needed. The extra declarations are the canonical transport and stalk
helpers of the owning theorem, listed in its `lean.declarations`.

Validation: scompile passed both its sandbox check (17.2 s) and the final library-module
check (24.9 s), without errors or warnings. Server delivery preflight and dry run
are run before pushing.

## Second reading by Q70

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
