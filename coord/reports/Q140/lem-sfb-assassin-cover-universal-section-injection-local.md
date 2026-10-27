## Worker report

The module `Sheaf.RingTheory.AssassinCoverUniversalSectionInjectionLocal` states
`Algebra.universallyInjective_of_local_assassinCover`, with its sole proof `by sorry`.
It states the existing node exactly; there is no statement correction, new definition,
or dependency repair. Source read: literature/stacks-project/flat.tex, Tag 05DG,
lemma-base-change-universally-flat-local, together with the preceding 05DE/05DF argument.
The proof's N tensor_R S' typo is already corrected in the accepted node; the statement
and this delivery consistently use N tensor_S S'.

Hypotheses and conclusion, clause by clause:

- Commutative local rings R and S: `[CommRing R] [CommRing S] [IsLocalRing R]
  [IsLocalRing S]`. Mathlib local rings are nontrivial and have exactly one maximal ideal.
  Their maximal ideals are `IsLocalRing.maximalIdeal R` and the corresponding ideal of S.
- Local homomorphism R to S: `[Algebra R S] [IsLocalHom (algebraMap R S)]`.
  For local rings reflection of units is equivalent to carrying the maximal ideal into
  the maximal ideal, or its inverse image being exactly the base maximal ideal.
- Essential finite presentation: the independent carrier B, `[CommRing B] [Algebra R B]
  [Algebra B S] [IsScalarTower R B S] [Algebra.FinitePresentation R B]`, and
  `(W : Submonoid B) [IsLocalization W S]` exhibit precisely the node's presentation
  S = W^{-1} B as an R-algebra. The scalar tower records compatibility, not a further
  mathematical restriction. No finite-generation restriction is placed on W.
- N is an S-module: `[AddCommGroup N] [Module S N]`. The base module and its inherited
  action are `[Module R N] [IsScalarTower R S N]`.
- N is finitely presented over S: `[Module.FinitePresentation S N]`.
- N is flat over R: `[Module.Flat R N]`. There is no Noetherian assumption on R or S.
- S to S' is a homomorphism of commutative rings: `[CommRing S'] [Algebra S S']`.
  Its flatness is exactly `hflat : (algebraMap S S').Flat`. S' need not be local.
- The closed-fibre module is
  `N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) • (⊤ : Submodule S N))`.
  This is N / m_R N: mapping the ideal into S and multiplying the full S-submodule
  generates exactly all finite sums of r*n with r in m_R. This quotient has its actual
  S-module structure; no surrogate quotient or supplied fibre is used.
- Primes q of S are `q : PrimeSpectrum S`. Lying over m_R is
  `q.asIdeal.comap (algebraMap R S) = IsLocalRing.maximalIdeal R`.
- Element-annihilator association, with no Noetherian hypothesis, is membership of
  `q.asIdeal` in `RingTheory.annihilatorAssociatedPrimes S` of that quotient.
- Coverage is exactly `∃ q' : PrimeSpectrum S',
  PrimeSpectrum.comap (algebraMap S S') q' = q`. This is membership in the image of
  the underlying map of affine spectra, not a stronger surjectivity hypothesis.
- The canonical S-linear map is `(TensorProduct.mk S N S').flip (1 : S')`, sending
  n to n tensor 1. `restrictScalars R` makes it the required R-linear map, and
  `rTensor L` sends n tensor l to (n tensor 1) tensor l. `Function.Injective` is exactly
  the requested conclusion, for every additive group and R-module L.
- Ring, presentation, target-ring and module universes u, v, p, w, z are independent.
  L ranges over `Type (max u v p w z t)` with arbitrary enlargement t; every module
  can be placed in such a universe, so no test-module cardinal bound is imposed.
  All binders and universes are explicit, with `set_option autoImplicit false`.

Dependency declarations used (the recorded sources and their docstrings were read):

- def-weil-pbc-finitely-presented-algebra: `Mathlib.RingTheory.FinitePresentation`,
  `Algebra.FinitePresentation` (surjection from finitely many polynomial variables with
  finitely generated kernel).
- def-weil-pbc-module-localization: `Mathlib.Algebra.Module.LocalizedModule.Basic`,
  `LocalizedModule`; the algebra presentation uses the corresponding ring-localization
  universal-property predicate `IsLocalization` from Mathlib.RingTheory.Localization.Defs,
  not a new definition. The recorded fraction construction and IsLocalization express
  the same localization; its denominators may form any submonoid.
- def-sc-finitely-presented-module: `Mathlib.Algebra.Module.FinitePresentation`,
  `Module.FinitePresentation` (finite generating set and finitely generated relations).
- def-weil-pbc-flat-ring-map: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`,
  and `Mathlib.RingTheory.Flat.Basic`, `Module.Flat` (the latter is reexported).
- def-weil-affine-spectrum: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`
  and `Spec.map`; only their underlying points and maps enter the statement, namely
  `PrimeSpectrum` and `PrimeSpectrum.comap`. The scheme's underlying map is contraction.
- def-weil-pbc-annihilator-associated-primes:
  `WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes`,
  `RingTheory.annihilatorAssociatedPrimes`. The actual definition is prime ideals equal
  to `(⊥ : Submodule S M).colon {z}` for some z, not weak association.
- def-weil-pbc-module-tensor-product has no lean record and needs none: its mathlib_match
  is TensorProduct in Mathlib.LinearAlgebra.TensorProduct.Defs, together with the
  recorded canonical `mk`, `lift`, and `LinearMap.rTensor` APIs. The delivered statement
  uses `TensorProduct.mk` and `LinearMap.rTensor` directly; Tower supplies scalar actions.

Available proof-dependency modules are imported privately: Mathlib.RingTheory.FiniteType
(`Algebra.FiniteType.isNoetherianRing`), Localization.Submodule
(`IsLocalization.isNoetherianRing`), Spectrum.Prime.Topology
(`PrimeSpectrum.localization_comap_isEmbedding`, `localization_comap_range`), Flat.Stability
(`Module.Flat.baseChange`), and Flat.FaithfullyFlat.Algebra
(`Module.faithfullyFlat_iff` and `Module.FaithfullyFlat.tensorProduct_mk_injective`).
The two stage-1 proof prerequisites lem-sfb-fibre-regular-localization-spectrum and
lem-sfb-fibre-regular-localization-universal-injection have no recorded Lean declarations
in the read clone; they are named explicitly in the complete proof docstring, and no
nonexistent import is introduced. Neither is needed to type this statement.

Edge cases checked before writing:

- N = 0: the annihilator-associated set is empty, coverage is vacuous, and the domain
  tensor module is zero, so the conclusion holds even for S' = 0.
- S' = S with the identity algebra: coverage holds and the canonical map is an isomorphism.
- S' = 0 and nonzero finite N: the empty spectrum cannot cover its nonempty associated
  closed fibre (closed fibre is nonzero by Nakayama; it is finite over a Noetherian fibre).
  Thus the theorem does not incorrectly force an injection into zero.
- L = 0: both outer tensor products vanish. L arbitrary, including L = R and residue
  modules, is retained. R and S cannot be zero under the stated local-ring convention;
  this agrees with the node's exactly-one-maximal-ideal requirement.
- R a field, arbitrary characteristics, and local polynomial/localization algebras are
  included. W may contain any denominators; incompatible zero localization of a local
  nontrivial S simply cannot satisfy the presentation hypotheses.

Searches for an existing statement:

- msearch.py leanfinder, query "Local flat base change covering associated primes of a
  closed fibre gives a universally injective module map": OK, eight results, including
  instFlatAtPrime, Algebra.HasGoingDown.of_flat, Module.flat_of_isLocalized_maximal,
  and Module.FaithfullyFlat.of_specComap_surjective. These are ingredients or stronger
  faithful-flat hypotheses, not the claimed closed-fibre theorem.
- msearch.py loogle, query "Module.Flat, IsLocalHom, associatedPrimes": OK, zero hits.
- msearch.py grep, query "universally.*[Ii]njective|assassin|closed.*[Ff]ibre" in
  RingTheory/Flat: OK, zero hits.
- rg in both lean/WeilConjectures and lean/Sheaf for associatedPrimes, universal
  injectivity, assassin coverage and essentially finite presentation found general tensor
  criteria, Tag 046Y's local injective/flat-cokernel criterion, Tag 05FQ's projective-source
  residue criterion and associated-prime lemmas. None states 05DG. In particular Tag 05FQ
  assumes projectivity over R, which this node does not assume.
- Exact blueprint-id search in both source trees found no existing declaration.
- The node's existing Mathlib searches were read too: all found ingredients only.

Validation: scompile.py compiled the sandbox module and its final library module path
cleanly against the published live build. No warning or error was printed.
There is no STATEMENT-DISPUTED flag or remaining node fault.

## Second reading by Q140

A separate second pass reread the node, source Tag 05DG, and complete delivered module.
This was a self-review, as the dispatcher explicitly prohibits starting another agent;
the maintainer's independent review remains required. The comparison verified all six
source hypotheses: locality, essential finite presentation, module finite presentation,
base flatness, extension flatness, and precisely the associated-prime image condition.
The presentation is supplied as witness data, with its scalar tower, exactly as the node
spells it out; it is not replaced by finite presentation of S itself. The quotient is an
S-submodule quotient, so its associated primes are genuinely ideals of S. The restriction
of scalars is applied to the canonical tensor-with-one map before rTensor L, preserving
both the required R-linearity and the order of tensor factors in the node. No hypothesis
on S' being local, or on R/S being Noetherian, occurs. All source hypotheses and the
single universal-injectivity conclusion match. No mathematical mismatch was found. The source chapter title in the new docstrings was
corrected from More on Algebra to More on Flatness; no statement correction was made.
