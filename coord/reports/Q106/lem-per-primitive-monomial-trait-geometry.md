## Worker report

The module `Sheaf.AlgebraicGeometry.PrimitiveMonomialTraitGeometry` states
`AlgebraicGeometry.primitive_monomial_trait_geometry`. Its only theorem proof is `sorry`.
It reuses the existing quotient and coefficient map through the new definition node
`def-per-monomial-trait-model`; no Lean definition is duplicated and the item statement
is unchanged. I read ILO, Expose XVI,
Definition 3.5.11 and Lemma 3.5.13(i), printed pp.250--251, directly in the supplied PDF
(extracted text). The source asserts integrality, regularity, and smooth generic fibre, and
leaves (i) as an exercise. The docstring records all eight proof steps of the DAG node.

The hypotheses and clauses correspond as follows:

- The commutative Noetherian local domain R is `(R : Type u) [CommRing R] [IsDomain R]
  [IsLocalRing R] [IsNoetherianRing R]`. Its dimension one is `hdim : ringKrullDim R = 1`.
  No DVR instance, excellence, henselianity, completeness, or characteristic hypothesis is added.
- The chosen uniformizer is `(π : R)` and
  `hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}`. Dimension one already excludes a
  field and forces this generator to be nonzero; no extra nonzero assumption is needed.
- The integer n >= 1 is `(n : ℕ) (hn : 1 ≤ n)`.
- The nonnegative exponent tuple is `a : Fin n → ℕ`. The single existential
  `ha : ∃ i : Fin n, a i ≠ 0 ∧ IsUnit (a i : FractionRing R)` states that one and the
  same exponent is nonzero and invertible in K. All other exponents may be zero.
- K is Mathlib's canonical fraction field `FractionRing R`, with its canonical
  `algebraMap R (FractionRing R)`. Taking this specified fraction field does not restrict
  the mathematical assertion; every fraction field of R is canonically R-isomorphic to it.
- B is the existing `AlgebraicGeometry.monomialTraitAlgebra R π n a`, whose full definition
  was read: `MvPolynomial (Fin n) R ⧸ Ideal.span {(∏ i, MvPolynomial.X i ^ a i) -
  MvPolynomial.C π}`. This is the exact quotient in the node, including the empty factors
  associated with zero exponents. No arbitrary presentation or existential choice is used.
- The first conclusion is `IsNoetherianRing (monomialTraitAlgebra R π n a)`.
- The second is `IsDomain (monomialTraitAlgebra R π n a)`.
- The third is `IsRegularRing (monomialTraitAlgebra R π n a)`. This is the ring clause
  of `def-weil-regular-scheme`, using its unchanged Mathlib match; the node asks for ring
  regularity, not an alternative predicate for schemes.
- The last clause uses `Smooth (pullback.snd f η)` where
  `f = Spec.map (CommRingCat.ofHom (monomialTraitAlgebraMap R π n a))` and
  `η = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))`.
  Thus the asserted morphism has domain the actual categorical fibre product
  `Spec B ×_(Spec R) Spec K` and codomain `Spec K`. It is exactly the generic fibre
  of the canonical structure morphism, rather than an unrelated smooth K-scheme.

Dependency declarations read and reused:

- `def-weil-regular-scheme`: imported through `Sheaf.AlgebraicGeometry.IsRegularScheme`,
  which defines `AlgebraicGeometry.IsRegularScheme` using the existing scheme classes.
  Its ring clauses are `IsRegularRing` and `IsRegularLocalRing` in
  `Mathlib.RingTheory.RegularLocalRing.Defs`; their complete class signatures were read.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, with `isNoetherianRing_iff_ideal_fg` identifying ideal finite generation.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`, whose affine-local smooth ring-map definition was read.
- `def-weil-polynomial-ring`: `Mathlib.Algebra.Polynomial.Basic`, `Polynomial`.
  The many-variable polynomial model uses the existing `MvPolynomial` construction in
  `Mathlib.Algebra.MvPolynomial.Basic`, already used by the canonical quotient definition.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`, the supremum of lengths of chains of primes.
- `def-sc-discrete-valuation-ring`: its Mathlib match is `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`; the class and
  `IsDiscreteValuationRing.irreducible_iff_uniformizer` were read. Its module is imported
  for proof step 1. The theorem retains the node's explicit trait assumptions.
- New definition dependency `def-per-monomial-trait-model` (existing declarations):
  `Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart`,
  `AlgebraicGeometry.monomialTraitAlgebra` and `AlgebraicGeometry.monomialTraitAlgebraMap`.
  The new definition node records precisely these two declarations in `lean.declarations`,
  not the chart theorem. The source and docstrings of both definitions were reread.
  The quotient and map have only `[CommRing R]` as an instance assumption. The new node
  depends only on the existing multivariate polynomial and affine-spectrum definition
  nodes, so it introduces no dependency cycle. The module import resolves those existing
  definitions as permitted by the return's `existing: true` option; the chart theorem
  is no longer a statement dependency.

All stated proof dependencies are imported (without `public` when only needed for proofs):
polynomial regularity, polynomial UFD, prime-ideal Eisenstein, formal partial derivatives,
the unit-derivation hypersurface criterion, independent cotangent generators for regular
quotients, and the regular-local hypersurface criterion. Their recorded signatures were read
from `Mathlib.RingTheory.RegularLocalRing.Polynomial`,
`Mathlib.RingTheory.Polynomial.UniqueFactorization`,
`Mathlib.RingTheory.Polynomial.Eisenstein.Criterion`, `Mathlib.Algebra.MvPolynomial.PDeriv`,
`Sheaf.RingTheory.HypersurfaceDerivationRegular`, and
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`.

Edge cases checked before drafting: n=0 is excluded exactly as in the node; n=1, a=(1)
gives B=R and a smooth point generically. Exponents (1,0) give a polynomial ring over R,
so imposing positivity of every exponent would have been wrong. In equal characteristic p,
an exponent divisible by p is not a unit in K, but the tuple may contain it if a different
exponent is prime to p. In mixed characteristic (p), the exponent p is allowed in K even
when it is not a unit of R; `IsUnit` is deliberately tested in `FractionRing R`.
In characteristic zero, tuples such as (2,2) are allowed, without a gcd-one hypothesis.
The zero ring and field cases for R are excluded by the existing domain and dimension-one
assumptions, not by added binders. The quotient is not assumed nontrivial: that is asserted
by its `IsDomain` conclusion. One explicit arbitrary universe u accommodates every R;
the finite-variable quotient and canonical fraction field live in that same universe.

Searches made with `msearch.py`, recorded in the sandbox's `searches.jsonl`:

- LeanFinder: "A monomial minus a uniformizer over a DVR defines an integral regular ring
  with smooth generic fibre". Eight results, including `StandardEtalePair` and Weierstrass
  preparation; none has this statement.
- Loogle: `IsRegularRing, MvPolynomial`. Only
  `MvPolynomial.isRegularRing_of_isRegularRing`, which concerns the polynomial ring before
  quotienting and is a proof input, not the requested theorem.
- Mathlib grep: `monomial.*regular|regular.*monomial|monomialTrait`, in `RingTheory`.
  No hits.
- LeanSearch: "A monomial hypersurface over a discrete valuation ring is integral and
  regular with smooth generic fibre if an exponent is invertible". Eight results include
  `MvPolynomial.isRegular_X_pow`, `IsRegular.monomial`, `Algebra.mvPolynomial`, and
  algebraic integrality results. Regular *elements* and integral *extensions* are different
  predicates from regular rings and integral domains; none states the requested theorem.
- `rg` of the upstream `WeilConjectures` tree and project `lean/Sheaf` for
  `monomial.{0,50}(trait|uniformizer|regular)|primitive.monomial`, the node id, and
  `monomialTrait` found the existing quotient and map in `RegularLogSmoothMonomialChart`.
  The remaining hits concern toric valuations, log regular charts, and regular sections.
  The node id has no upstream match. A DAG search for the two construction names identifies
  their definitions in the monomial-chart theorem module, without a definition node.
  No duplicate theorem was found.
- The proposed full declaration name `AlgebraicGeometry.primitive_monomial_trait_geometry`
  was checked by `rg` against the upstream name index, upstream Lean and project Lean:
  no existing declaration. The repair now adds a definition node for the previously
  unowned quotient construction, with an `existing: true` record.

## Repair of H2

The returned head ee9d2113a3eb cited the theorem node
`lem-per-regular-log-smooth-monomial-chart` solely to access two plain definitions.
This packet replaces that added dependency with `def-per-monomial-trait-model`.
The new node records both existing definitions and does not cite the chart theorem.
The source formula and both declaration bodies are identical; the mathematical statement
and its proof outline are unchanged. The initial saved-packet dry run passed at bbc8056647,
but that mechanical pass did not resolve the maintainer's mathematical dependency objection;
the added definition node is the substantive repair.

I used the return's explicit option to record the definitions as `existing: true`.
Consequently their published module `Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart`
remains imported as the new definition node's recorded module. Moving these declarations
would require altering the published module and its other consumers; recording them avoids
any duplicate declaration. The import is now documented as supplying this definition node,
not as a theorem assumption. The DVR import is now proof-only; its existing stmt_dep is
retained because the advisory did not authorize changing the base node's dependencies.

## New nodes

`def-per-monomial-trait-model` records ILO XVI Definition 3.5.11, printed p.250:
the actual ring `B = R[T_1,...,T_n]/(product(T_i^e_i)-pi)` and its canonical coefficient
map, hence its affine scheme over `Spec R`. The `existing: true` record names
`AlgebraicGeometry.monomialTraitAlgebra` (abbrev) and
`AlgebraicGeometry.monomialTraitAlgebraMap` (definition) in
`Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart`, lines 41--52.
There is no new module. The node uses `def-weil-pbc-mv-polynomial-ring` (`MvPolynomial`)
and `def-weil-affine-spectrum` (`Spec` and `Spec.map`).

For every parameter and clause of the new node: `R : Type u` and `[CommRing R]`
give the coefficient ring; `π : R` gives the relation's constant; `n : ℕ` and
`e : Fin n → ℕ` give exactly the finite tuple. `MvPolynomial (Fin n) R` is the
polynomial ring; `Ideal.span {(∏ i : Fin n, MvPolynomial.X i ^ e i) - MvPolynomial.C π}`
is its specified principal relation ideal. The quotient symbol gives B, and
`(Ideal.Quotient.mk _).comp MvPolynomial.C` gives the coefficient homomorphism.
Applying the existing `Spec` and `Spec.map` yields the affine model and its structure
map, exactly as used explicitly in the item's smoothness clause. Definition 3.5.11's
quotient construction makes sense for arbitrary coefficient rings; its use here specializes
to the trait. No regularity or nontriviality claim is part of the definition.
Zero exponents give factors 1. For n=0 the empty product is 1; for an all-zero tuple the
relation is 1-pi. These are valid quotient rings, including a possible zero ring, so the
construction should not impose the theorem's positive-tuple assumptions.

Fresh searches, with exact outputs in the new node's `mathlib_searches`:

- LeanSearch: "Monomial trait model quotient polynomial ring by product of powers minus
  a uniformizer": eight hits about monic polynomial quotients and monomial division;
  none defines this model.
- LeanFinder: "Coordinate ring R[T_1,...,T_n] modulo the product T_i^e_i minus pi, with
  the coefficient ring homomorphism": eight hits, including standard etale and Weierstrass
  coordinate rings, which have different relations.
- Loogle: `MvPolynomial, Ideal.Quotient` reported an unknown `Ideal.Quotient` identifier;
  the corrected query `MvPolynomial` returns the polynomial carrier, X and C, not this quotient.
- Mathlib grep: `monomialTrait|monomial.*uniformizer|monomial.*hypersurface` in RingTheory:
  no hits. Upstream `rg` with the same model terms: no hits.
- Project `rg monomialTrait lean/Sheaf`: precisely the existing quotient and coefficient
  map in RegularLogSmoothMonomialChart and their uses in its chart theorem.
- DAG grep and `tools/blueprint_refs.py search monomial`: theorem nodes about monomial
  geometry and unrelated monomial constructions, but no definition node for this model.
  Thus this is a new DAG binding to existing Lean definitions, not a second construction.

## Second reading by Q106

This is a self-check, with no independent worker started, as required by the dispatcher.
I reopened the item, the new definition node, the delivered module and both existing
construction bodies. The original theorem hypotheses still say precisely: Noetherian
local domain, dimension one, maximal ideal generated by pi, n at least one, and one
and the same exponent nonzero and a unit in `FractionRing R`. The four conclusions are
unchanged: Noetherian, domain, regular ring, and smoothness of the canonical pullback
projection to `Spec (FractionRing R)`. The full quotient and canonical map in the new
node are exactly the expressions unfolded by those conclusions. There is no theorem
choice, added log-smoothness assumption, or definition containing sorry. The new node
has only definition dependencies. The H2 mismatch was the dependency ownership, now
repaired through the new definition node. No statement correction or dispute is needed.

Validation: the repaired module compiled cleanly with `scompile.py` in sandbox mode
(2.9 s) and library mode (2.3 s), with no errors or warnings. The repaired packet
passed `deliver2.py --no-push`: OK at commit 43f5700eb5, including preflight and
compilation of the existing-definition binding and the delivered theorem module.
The item changes only `lean` and the added definition dependency. Its recorded Lean
signature matches the file verbatim; all Lean lines are at most 100 characters.
