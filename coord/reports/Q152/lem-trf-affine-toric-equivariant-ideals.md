## Worker report

The module `Sheaf.RingTheory.AffineToricEquivariantIdeals` states
`MonoidAlgebra.affine_toric_equivariant_ideals`; its proof is `sorry`.
Its affine helper definitions have real data. No mathematical statement correction
or new DAG notion is needed. The item JSON changes only `lean`.

The earlier import failure is repaired under brief-stage2 §1(B), using two dependency
modules in this delivery. All three files now compile separately in dependency order
through scompile.py, without errors or warnings. The earlier report is retained only
in sandbox scratch; its claim that the import failure cannot be repaired is superseded.

Hypothesis and clause correspondence:

- The field is `(k : Type v) [Field k]`; the fine commutative monoid is
  `(P : Type u) [CommMonoid P] (hP : FineFan.IsFine P)`. The recorded `IsFine`
  means finite generation and injectivity of `GrothendieckGroup.of`. The additional
  `[IsMulTorsionFree (GrothendieckGroup P)]` is exactly torsion-free completion.
  Universes u, v, w, z are all explicit and independent.
- `MonoidAlgebra k P` is the finite formal-sum ring. `affineToricCoaction` sends a
  basis monomial to `e^p ⊗ e^[p]` using `MonoidAlgebra.lift`. It is the affine
  specialization of the recorded component coaction (with factors reversed), where
  the grading is the canonical group completion rather than a supplied component stalk.
- `toricIdeal k I` is `Ideal.span (MonoidAlgebra.of k P '' (I : Set P))`.
  The support clause in the first conjunct states that this is exactly the direct
  sum supported on I. `SemigroupIdeal P` includes the empty ideal; no nonemptiness
  or coherence hypothesis is imposed.
- `toricExponents k J` has carrier `{p | MonoidAlgebra.of k P p ∈ J}` and the
  actual ideal-absorption proof. `IsAffineToricEquivariant` equates `Ideal.map`
  along the coaction and along `Algebra.TensorProduct.includeLeft`. The latter is
  the image of J tensor k[G], since k is a field. Thus this is the stated equality
  of extended ideals, including both inclusions.
- The first two conjuncts give equivariance of k[I], exponent recovery, ring-ideal
  recovery for every equivariant J, and both finite-generation equivalences using
  `Ideal.FG` and `SemigroupIdeal.FG`. They give precisely the two inverse assignments.
- The first conjunct also gives `toricIdeal k I = ⊥ ↔ I = ⊥` and the analogous
  top equivalence; bottom is the empty monoid ideal and zero ring ideal, and top
  is the whole monoid and ring. The finite-support clause explicates the notation
  k[I], rather than introducing an additional mathematical restriction.
- For every a, `toricFractionMap k (Submonoid.powers a) a ...` is the canonical
  ring homomorphism from `Localization.Away (MonoidAlgebra.of k P a)` into the
  recorded `Algebra.faceLocalization P (Submonoid.powers a)` monoid algebra.
  `Function.Bijective` of this particular ring homomorphism states the canonical
  ring isomorphism. It is not a chosen arbitrary isomorphism. The following
  equation sends the actual fraction to the ambient completion monomial
  `of p * (of a)⁻¹ ^ n`, namely p-na in additive notation.
- The next equality maps the extended ring ideal along this canonical fraction
  map to the monoid ideal extension. Its membership equivalence says the exponents
  are exactly `∃ i ∈ I, ∃ n, x = of i * (of a)⁻¹ ^ n`, namely I-N a.
- For any fine Q and any homomorphism h, `toricIdealExtension h I` is the monoid
  ideal closure of h(I), namely h(I)+Q. The next conjunct gives precisely the ring
  extension formula. No injectivity or torsion-free completion is assumed for Q.
- The successive-homomorphism conjunct identifies both ideal extensions and the
  actual composite induced ring maps. The two double-fraction formulas give the
  same p-na-mb in either order, and the next two equalities give the same ideal in
  the common two-denominator localization. Repetition a=b is included.
- The final conjunct gives compatibility of the localized h with both ideal
  extension and the canonical ring maps. Its target denominator monoid is
  `(Submonoid.powers a).map h`, so it is exactly inversion of h(a).

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineFanBlowup`: `AlgebraicGeometry.FineFan.IsFine`
  (full definition, source ILO VIII 3.1.2--3.1.3), and the imported recorded
  `Algebra.faceLocalization` fraction submonoids. The item uses these notions
  without redefining fineness, completion, or monoid localization.
- `Sheaf.AlgebraicGeometry.MonoschemeToricRealization`: read `Monoscheme.Fine`,
  `monoidAlgebra`, `coaction`, `chartRingIdeal`, `IsComponentTorusEquivariant` and
  `IsTorusEquivariant`, with their source docstrings and full signatures.
  The two last notions concern sheaf ideals on a specified global realization;
  they cannot take an arbitrary affine ring ideal. The affine helpers expose the
  actual ring-level construction those declarations use, for arbitrary k and P.
- The proof leaf `lem-trf-monoid-algebra-ideal-support` records
  `AddMonoidAlgebra.mem_ideal_span_of'_image`; read it and its multiplicative form
  `MonoidAlgebra.mem_ideal_span_of_image` in `Mathlib.Algebra.MonoidAlgebra.Ideal`.
  The current public import is also used to supply ideal operations in the statement.
- The proof dependencies for tensor product and localization record Mathlib's
  `TensorProduct` and `Localization.Away`. Read the tensor quotient definition,
  `TensorProduct.lift`, `lift.tmul`, `ext'`, and the fraction-map definitions
  `Localization.awayLift`, `IsLocalization.Away.lift_eq` and `awayLift_mk`.
  `Mathlib.RingTheory.TensorProduct.Maps` and
  `Mathlib.RingTheory.Localization.Away.Basic` are public because the statement's
  actual constructions use them as well as the planned proof.

Source: read ILO VIII Proposition 3.2.2 proof, printed p.103, and 3.2.14 and
Lemma 3.2.15 with its proof, printed p.105, directly from the repository PDF.
The source's localization universal property, coefficient grading and rank-one
homogeneous pieces give the stated constructions; the node expands the finite
support, finite-generation, extension and composition computations. The theorem
has a source/proof docstring covering every step of that argument.

Edge cases checked mathematically: empty I and empty generating family, whole I,
zero J, trivial P and rank-zero completion, units, a=1, n=0, repeated a=b,
finite fields, noninjective h with colliding exponents, and target fine monoids
with torsion in their completions. None is removed by a binder or construction.
Coefficient extraction uses the group-algebra coefficient maps, so it does not
require an infinite field or rational torus points. Every definition has actual
data; only the one main theorem is postponed.

Searches (repeated on 2026-10-23 through msearch.py):

- LeanFinder: "Equivariant ideals for the torus coaction on a cancellative monoid
  algebra over a field are monomial ideals, compatible with localization and extension".
  Eight hits, including the two monoid-algebra support lemmas and unrelated results;
  no correspondence or canonical-localization theorem matching the whole node.
- Loogle: `"MonoidAlgebra", "Ideal"`. Two hits: the additive and multiplicative
  support lemmas; neither classifies torus-equivariant ideals.
- grep: `monomialIdeal|equivariantIdeal|mem_ideal_span_of_image|mapDomain.*comp`
  in `Algebra/MonoidAlgebra`. Thirteen hits, support and mapDomain composition
  results, not the full correspondence.
- LeanSearch: "Torus equivariant ideals in a monoid algebra over a field are
  precisely the monomial ideals and this correspondence preserves finite generation".
  Eight hits, principally finite-type/FG equivalences for the whole monoid algebra,
  not finite generation of these ideals or the equivariance correspondence.
- rg in `lean/WeilConjectures` and `lean/Sheaf`, and grep for the item id in
  `lean/WeilConjectures`: no exact statement. Read the project hits:
  `ToricMonoidComparison.toric_ideal_comparison` is a global sheaf/coherence theorem,
  not the affine ring theorem with its explicit fraction formulas;
  `SaturatedBlowupProductCharts.monomialIdeal` takes a finite list in one universe,
  not arbitrary possibly empty monoid ideals in independent universes; and
  `LogRegularMonomialTensor` is a different tensor-injectivity result.

No STATEMENT-DISPUTED flag: the edge cases and source agree with the node.

## Dependency modules

`def-trf-fine-fan-blowup`: its DAG record describes a module-mode repair, but the
current server source returned by scompile.py --source still has only legacy
imports. The minimal required-mode probe and full draft both fail before
elaboration with "cannot import non-`module` ...FineFanBlowup from `module`".
The supplied `Sheaf.AlgebraicGeometry.FineFanBlowup` is that current full server
source, changing only module mode, import visibility and an exposed public
section. All definitions, signatures and bodies are unchanged. The dependency
node changes only lean, with the required note. It compiles cleanly in 14 s.

`def-trf-monoscheme-toric-realization`: the current server source is likewise
legacy non-module despite its recorded repair. The supplied full module makes
exactly the same visibility changes, retaining every existing declaration,
including the canonical chart/coaction maps and all existing postponed theorems.
The node changes only lean, with a note. It compiles cleanly in 12 s. Supplying
both dependency modules together through scompile.py resolves the earlier
import failure without altering the library, launcher tools, or build artifacts.

## Validation

scompile.py compiled each of the three delivered modules separately in dependency
order, including library-mode verification: no errors or warnings. The item
compiled in about 7 s, within the default 60 s limit. Dry-run and delivery results
are recorded by the prescribed deliver2.py wrapper.

## Second reading by Q152

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
