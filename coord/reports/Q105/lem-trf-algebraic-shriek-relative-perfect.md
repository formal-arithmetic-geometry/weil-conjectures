## Worker report

The module `Sheaf.TraceFormula.AlgebraicShriekRelativePerfect` defines the chosen
polynomial relative dualizing complex and states
`AlgebraicGeometry.algebraicShriek_relative_perfect`, with proof `sorry`.
The mathematical statement is unchanged. There are no new nodes or dependency repairs.

Source read: `literature/stacks-project/dualizing.tex`, Tag 0BZW,
`lemma-relative-dualizing-algebraic`, statement and full proof, parts (1) and (2)(a).
Its proof uses the chosen polynomial model from the preceding algebraic upper-shriek
construction. Flatness implies perfectness of the ring map; neither the source nor
the Lean requires an lci hypothesis.

Hypotheses and clauses, matched with the node:

- Commutative rings R and A: `{R A : CommRingCat.{u}}`. The arbitrary universe u
  can contain any given pair of rings; no independent smaller test-module universe
  is introduced. Both Noetherian hypotheses are `[IsNoetherianRing R]` and
  `[IsNoetherianRing A]`.
- The specified ring map is `φ : R →+* A`; flatness is `hφflat : RingHom.Flat φ`
  and finite type is `hφfinite : RingHom.FiniteType φ`.
- An arbitrary finite polynomial presentation is `n : ℕ`,
  `p : MvPolynomial (Fin n) R →+* A`, `hp : Function.Surjective p`, and
  `hc : p.comp MvPolynomial.C = φ`. Compatibility is an equality of ring maps;
  an unrelated surjection is not accepted.
- `S : AlgebraicShriekCalculus` supplies the existing normalized derived
  coinduction. This is choice of model data, not an additional ring hypothesis:
  the recorded calculus existence theorem supplies such data, and this theorem
  holds for every such calculus. No data are extracted from that postponed
  theorem. Its `coinductionModel` specifies ordinary Hom_P(A,I), multiplication
  action `(a h)(a') = h(a'a)`, and evaluation-at-one counit.
- `algebraicShriekRelativeComplex S n p` is exactly the coinduction of `P[0]`
  along p, shifted by `(n : ℤ)`, so it is RHom_P(A,P)[n] in D(A), with that
  coinduced A-action. It is a full construction using the supplied functor.
- Pseudo-coherence is `DerivedCategory.IsPseudoCoherent` of this object, using
  the dependency's bounded-above finite-free representative definition unchanged.
- Bounded cohomology is `∃ c d : ℤ, c ≤ d ∧ ∀ i, i < c ∨ d < i → IsZero ...`;
  finite generation of every cohomology module is the separate
  `∀ i, Module.Finite A ((DerivedCategory.homologyFunctor ... i).obj K)`.
  Neither clause replaces the other.
- Finite R-Tor amplitude is `∃ a b : ℤ, a ≤ b ∧
  DerivedCategory.torAmplitudeIn (ModuleCat R) a b
  ((algebraicShriekRestriction φ).obj K)`. The upstream definition quantifies
  every ordinary R-module F in degree zero and tests cohomology of the actual
  derived tensor. The bounds are outside that universal quantifier.
- The actual scalar map is expressed on all representatives E of K and all
  K-injective replacements `η : E ⟶ I`. It asserts existence of a chain map
  `α : A[0] ⟶ CochainComplex.moduleHomComplex E I` whose degree-zero map,
  after the standard degree-zero single-object identification, is precisely
  `a ↦ a • CochainComplex.HomComplex.Cochain.ofHom η`, and asserts `QuasiIso α`.
  A chain map from A[0] is determined by that degree-zero linear map, so α is
  the canonical scalar map, not an arbitrary map or an unnormalized isomorphism.
  Since I is K-injective, Hom(E,I) represents RHom_A(K,K); localization inverts
  α exactly when α is a quasi-isomorphism. All E, I, η and their conditions are
  quantified inside the conclusion, so no chosen representative, resolution,
  boundedness, or existence assumption is added to the hypotheses. Replacements
  exist for every E by the imported ordinary module K-injective framework.
  This is an equivalent resolution-level rendering of the node's last clause.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; its signature/docstring and the
  standard localization size were read. Cohomology and shift use the existing
  derived category, never a separate localization.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, its inverting theorem,
  K-injective localization construction, and comparison signatures were read.
  This ringed-site declaration is publicly imported by the calculus. The last
  clause uses its defining K-injective Hom-complex description in ordinary
  module coordinates; it does not introduce a second derived-Hom functor.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, including its
  equivalence with finite generation of every ideal.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with
  `Flat.SpecMap_iff` and `Flat.iff_flat_stalkMap`, were read for the original
  scheme-flat dependency. For the ring statement the exact existing ring-flat
  node is additionally cited, using `Mathlib.RingTheory.RingHom.Flat`:
  `RingHom.Flat`, defined by `Module.Flat` for the ring map's algebra structure.
- `Sheaf.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`,
  including its complete finite-free representative definition.
- `Sheaf.TraceFormula.AlgebraicShriekCalculus`:
  `AlgebraicGeometry.AlgebraicShriekCalculus`, `coinduction`, `coinductionModel`,
  `coinductionAdj`, `algebraicShriekD`, `algebraicShriekRestriction`, and
  `nonempty_algebraicShriekCalculus`; the structure and its normalizations were
  read in full. The calculus node is added to statement dependencies because
  the statement directly uses its already published data.
- `Sheaf.Algebra.Homology.ModuleHomComplex`:
  `CochainComplex.moduleHomComplex`; its complete real terms/differential were
  read. Its owning node `def-sc-module-total-hom-complex` is added to statement
  dependencies. Mathlib's existing `HomComplex.Cochain.ofHom` is the zero-cocycle
  of a chain map.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`; and
  `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, with its evaluation and
  uniqueness declarations read. Their existing nodes are additionally cited.
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`:
  `DerivedCategory.torAmplitudeIn`; `FlatModel` and the ordinary ModuleCat
  functorial flat-resolution instance supply its canonical derived tensor.

The already stated proof prerequisites
`Sheaf.TraceFormula.FlatPolynomialQuotientPerfect` and
`Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion` are ordinary imports.
The other three proof prerequisites (upper-shriek bounded coherence, internal
coinduction adjunction, and perfect derived biduality) have no recorded Lean
module on the read base, so no fictitious import is supplied. Their exact roles
are preserved in the theorem's four-step proof docstring.

Edge cases checked: n = 0 uses Fin 0 and shift zero, with no positivity binder;
R or A the zero ring is allowed (IsZero and Module.Finite accept the zero
cohomology), and the scalar map is then the zero-category isomorphism; R = A
with the identity presentation is included; redundant polynomial generators are
allowed by arbitrary n and p; singular flat finite-type algebras, including
non-lci algebras, have no excluded hypothesis. The tensor test includes the zero
module and arbitrarily large modules after enlarging the arbitrary common
universe. Cohomology support intervals may be singletons, and no nonzero
cohomology is asserted.

Searches actually run (the launcher log records the exact queries and results):

- LeanFinder: “For a flat finite type Noetherian algebra A over R the derived
  coinduction RHom_P(A,P) shifted by n is pseudo coherent with bounded finite
  cohomology finite Tor amplitude and scalar endomorphism isomorphism”. Eight
  hits, including ordinary formally-smooth flatness, Ext and Tor vanishing;
  none is the statement.
- LeanSearch: “Relative dualizing complex of flat finite type Noetherian ring
  homomorphism has finite Tor amplitude and scalar endomorphism isomorphism”.
  Eight ordinary flatness and scalar-extension hits; no relative-duality result.
- Loogle: `Module.Flat, RingHom.FiniteType`: zero hits.
- msearch grep: `relative.dualizing|relativelyPerfect|RelativelyPerfect` under
  Mathlib/Algebra: zero hits.
- Direct rg of upstream WeilConjectures for relative-duality/coinduction names:
  an étale smooth-duality module, no ordinary algebraic theorem. Exact item-id
  search returned no declaration; the upstream name index has no matching name.
- Direct rg of lean/Sheaf found the normalized AlgebraicShriekCalculus and
  existing ModuleHomComplex, RingPseudoCoherent, flat-polynomial perfectness,
  and generic Tor-amplitude framework; these are reused.

Validation: the required scompile.py wrapper compiled the delivered module in
both its sandbox and actual library module context, with no errors or warnings.
Initial diagnostic probes showed that the upstream closed-derived-category
instance is not available for the calculus's standard localization universe;
using the explicit K-injective Hom model preserves that size and the exact map.
All probes were removed from the delivered module. No statement correction,
STATEMENT-DISPUTED flag, new mathematical definition node, or hollow data occurs.

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
