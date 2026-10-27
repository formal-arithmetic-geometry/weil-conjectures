## Worker report

The module `Sheaf.AlgebraicGeometry.ArtinLocalTestAlgebra` states the node in
three theorems in namespace `AlgebraicGeometry.ArtinDeformation`. Every proof
is `sorry`. There are no definitions, auxiliary axioms, new nodes, dependency
repairs, or changes to the natural-language statement.

Sources read: `literature/stacks-project/formal-defos.tex`,
`lemma-factor-small-extension` (Tag 06GE), lines 279–310, and
`lemma-fiber-product-CLambda` (Tag 06GH), lines 450–505; and
`literature/stacks-project/artin.tex`, `equation-predeformation-category`
(Tag 07T4), lines 225–265. The node's eight proof steps supply the explicit
localization reduction and the simple-filtration argument; these are preserved
in the theorem docstrings. The source's shorthand about a composite of small
extensions is rendered with the node's final isomorphism, including automorphisms.

Hypothesis and clause correspondence:

- `R k : Type u`, `[CommRing R]`, `[IsNoetherianRing R]`, `[Field k]`,
  `[Algebra R k]`, `[Algebra.FiniteType R k]` are the Noetherian commutative
  base, field, specified structure map, and finite-type field algebra.
  The named instances `hR hk` are explicitly included in every theorem.
  A common arbitrary universe is the dependency's size convention; there is
  no independent smaller universe for the tested rings.
- Objects and arrows are exactly `TestCategory R k` and its categorical arrows.
  Its `ring`, `residue`, and `map` retain the R-algebra and specified residue
  marking. Objects are Artinian local and arrows preserve that marking and are
  automatically local. No abstract replacement test category is introduced.
- `artin_local_test_algebra` first asserts, for every test B,
  `∃ N : ℕ, 0 < N ∧ maximalIdeal (ring B) ^ N = ⊥`.
- Its second conjunct quantifies over the specified diagram and over
  `hs : Function.Surjective (map f₂)`. `fibreProductAlgebra f₁ f₂` is the
  dependency's literal subalgebra of pairs with equal image, with componentwise
  operations and canonical R-structure. `IsTestAlgebra` for
  `fibreProductResidue` states Artinianness, locality, surjectivity of the
  marked residue map, and equality of its kernel with the maximal ideal.
  `Function.Surjective (map (fibreProductFst ... hs))` is the projection clause.
- `IsSmallExtension f₂ → IsSmallExtension (fibreProductFst ... hs)` is the
  small-extension clause. The additive equivalence of the two actual kernels,
  characterized by `(e x).val = x.val.val.2`, is the canonical same-kernel
  identification, rather than an arbitrary equivalence. Its inverse necessarily
  sends j to (0,j). This characterization and residue compatibility also retain
  the residue-field action when the kernels are small.
- `exists_small_extension_factorization` takes the given arrow f and its
  surjectivity. `ComposableArrows (TestCategory R k) n` is a finite chain of
  exactly n arrows. The left endpoint equality makes its source the given B;
  `eC : T.right ≅ C` is the terminal marked isomorphism. Every adjacent arrow
  `T.map (homOfLE (Fin.castSucc_le_succ i))` is small. The composite, including
  endpoint transport and `eC.hom`, is required to equal f itself.
  `(n = 0 ↔ IsIso f)` is the exact isomorphism criterion; n : ℕ includes n ≥ 0.
- Its second conjunct, for nonzero `RingHom.ker (map f).toRingHom`, gives a
  chain of positive length whose right endpoint equals C, with no terminal
  isomorphism beyond transport by this equality. This is precisely B₀ = C
  with the identity final arrow, and its composite again equals f.
- `localization_marked_structures` uses
  `IsLocalization (ker (algebraMap R k)).primeCompl Λ`. The prime-ideal proof
  is supplied explicitly by the existing `RingHom.ker_isPrime`; no prime or
  maximality assumption is imposed. This is Mathlib's interface for the
  specified localization R_p, also satisfied by `Localization.AtPrime p`.
  Any model of that same localization gives the identical assertion.
- `IsNoetherianRing Λ ∧ IsLocalRing Λ` is the first localization conclusion.
  The unique q extends the given map to k; `q.Finite` means exactly that k is
  a finite Λ-module with that extended scalar structure.
- The unique extensions a on each marked test A and complete marked local C
  restrict to the original R-structure and commute with their actual residue
  augmentations. The last two conjuncts say every original R-arrow commutes
  with the extended structures. For complete rings the equation quantifies over
  local R-algebra maps preserving the specified residue augmentations, exactly
  the morphisms of the complete marked local category.
  This is the category identification on unchanged underlying rings and maps:
  extending an R-object is unique; restricting a Λ-object and extending back
  recovers its structure by the same uniqueness; Λ-arrows restrict to R-arrows
  and R-arrows preserve the extensions. Locality, residue identifications,
  maximal-ideal-adic completeness and continuity are properties of exactly the
  same rings, markings and maps. Thus neither category clause is omitted or
  replaced by existence of an unrelated abstract equivalence.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`:
  `IsTestAlgebra`, `TestCategory`, `ring`, `testLocal`, `testArtinian`,
  `residue`, `map`, `IsSmallExtension`, `fibreProductAlgebra`,
  `fibreProductResidue`, `fibreProductTest`, `fibreProductFst`,
  `CompleteLocalAlgebra`. Their full source signatures and docstrings were read.
  The already supplied `nilpotence_exists` and `fibreProduct_isTestAlgebra`
  were also inspected: neither is a match for the whole node.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
  `Mathlib.Algebra.Field.Defs`: `Field`.
  `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType` is the affine algebra
  rendering of finite type. The scheme declarations recorded by
  `def-weil-finite-type-morphism` (`LocallyOfFiniteType`, `QuasiCompact`) were
  read; the current item concerns rings and requires no scheme formalism.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`
  and `IsLocalization.AtPrime`, via their general `IsLocalization` interface.
  `Mathlib.RingTheory.Finiteness.Defs`: `RingHom.Finite`.
  `Mathlib.CategoryTheory.ComposableArrows.Basic`: `ComposableArrows`,
  `left`, `right`, `hom` encode the finite chain without defining it again.
- Proof imports, all read: `RingTheory.exists_ideal_filtration_length_one`
  in `WeilConjectures.AlgebraicGeometry.ArtinianIdealLengthOneFiltration`;
  `isArtinianRing_iff_isNilpotent_maximalIdeal` and
  `isArtinianRing_iff_isFiniteLength` in `Mathlib.RingTheory.HopkinsLevitzki`;
  `Module.length_eq_add_of_exact` in `Mathlib.RingTheory.Length`;
  `IsLocalization.isNoetherianRing` in
  `Mathlib.RingTheory.Localization.Submodule`; `IsLocalization.lift` and
  `IsLocalization.ringHom_ext` in `Mathlib.RingTheory.Localization.Defs`;
  `finite_of_finite_type_of_isJacobsonRing` in
  `Mathlib.RingTheory.Jacobson.Ring`. Proof-only modules are ordinary imports.

Edge cases checked before writing: the residue-field test has maximal ideal
zero (positive exponent 1); the zero ring cannot be a marked test with residue
field k; identity and nonidentity isomorphisms both allow n = 0 with their
actual final isomorphism; a nonzero kernel forces positive chain length;
identity second leg in a fibre product gives zero projection kernel and is
not small; small extensions exclude zero kernels; no characteristic or
separability assumption is made; R → k can have nonmaximal prime kernel, e.g.
R = ℤ_(p), k = ℚ = R[1/p], where localization at zero is ℚ and k is a
finite-type R-algebra. Thus we never
strengthen the hypothesis to a maximal kernel. No exception for n = 0 or for
nontrivial residue extension is lost.

Searches performed (logged in the sandbox searches.jsonl):

- LeanFinder: "Artinian local algebras pullback surjective small extension
  factorization localization residue field" returned eight related results
  including `IsArtinianRing.localization_surjective`; none states this node.
- LeanSearch: "Artinian local ring fiber product small extension factorization"
  returned eight Artinian/quasi-finite facts, including the nilpotence
  criterion; none includes the marked category, factorization and localization.
- Loogle: "IsLocalRing, Localization.AtPrime" returned zero hits.
- msearch grep: `smallExtension|SmallExtension|fiberProduct` in RingTheory
  returned zero hits.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for `ArtinDeformation|SmallExtension|small_extension`
  found the supplied test-category API and unrelated small-extension lemmas
  about other notions, no full statement. Searching the exact item id in
  `lean/WeilConjectures` returned no match. Searching for small-extension
  factorizations, localization of tests and fibre-product kernels found no
  replacement for these clauses.

Validation: scompile.py compiled both the sandbox module and its actual library
module cleanly. `autoImplicit` is false; every universe and variable is bound.
The initial compile diagnosed an implicit prime-ideal instance, fixed by using
`RingHom.ker_isPrime` explicitly in the localization submonoid. No extra
hypothesis, statement correction, or disputed statement was needed.

## Second reading by Q159

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
