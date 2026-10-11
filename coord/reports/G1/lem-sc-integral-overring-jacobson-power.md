## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralOverringJacobsonPower` states
`integral_overring_jacobson_power`.  `B`, `A`, and `B'` are explicit
commutative rings with algebra maps and a scalar tower; the `FaithfulSMul`
hypotheses express the inclusions `B ⊆ A ⊆ B'`.  The two `Finite
(MaximalSpectrum ·)` hypotheses render semilocality of `B` and `B'`, and
`Algebra.IsIntegral B B'` renders integrality.  `hspec` is precisely
surjectivity of the induced map `PrimeSpectrum.comap (algebraMap A B')`.
The conclusion has three clauses: `A` is semilocal; its Jacobson radical is
the radical of the mapped Jacobson ideal of `B`; and each `x : A` whose image
lies in the Jacobson radical of `B'` has a positive natural power in that
mapped ideal.  The proof is `sorry` as required for stage 2.

The dependency notion is Mathlib's `Algebra.IsIntegral` / `IsIntegral` and
`integralClosure` from `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`;
no private replacement is introduced.

Edge cases checked: `Finite (MaximalSpectrum R)` permits zero maximal ideals;
`m : ℕ` is explicitly required positive; the zero ring and empty maximal
spectrum are not excluded; arbitrary universes `u v w` are supported.  The
radical and ideal extension use Mathlib's `Ideal.radical` and `Ideal.map`.

Searches made: `msearch.py leanfinder "lem sc integral overring jacobson power"`
returned only generic integral-extension results; `msearch.py loogle
"IntegralClosure, IsDedekindDomain, Module.Finite, Jacobson"` returned no
matching radical equality; grep of Mathlib RingTheory for Jacobson/integral
extension found only generic declarations; `rg` over `WeilConjectures` and
`lean/Sheaf` found no declaration of this statement.  Therefore a new module
was required.

## Earlier second reading (a previous round; superseded)

The theorem signature was read against every clause of the node.  The three
ring objects and all semilocality/integrality hypotheses are present.  The
intermediate-ring inclusions are rendered by the algebra maps and faithful
scalar actions; the Spec-surjectivity clause is the exact `PrimeSpectrum`
comap surjectivity hypothesis.  The equality uses `Ideal.map` for `m_B A`
and `Ideal.radical`; the final clause restricts `x` to `A` and tests its
image in `B'`, then supplies `m > 0` with the stated membership.  No mismatch
was found.

## Second reading by G1

I independently read the node, its statement dependency, the delivered Lean, and
Stacks Tag 09N2. The repository's Stacks checkout is absent on this machine;
I read the .tex at /home/ubuntu/c1-stacks-review/varieties.tex:7416–7444,
with the label verified in that checkout's tags/tags:12200, and checked it
against https://stacks.math.columbia.edu/tag/09N2. The surrounding lemma assumes
a Noetherian dimension-one domain and its normalization in its fraction field.
This node isolates only the integral-extension Jacobson argument: its four
proof steps justify the stated generality without those surrounding hypotheses.
No statement correction, new definition node, or dependency module is needed.

Object/hypothesis/conclusion checklist (all pass):

- B, A, B': `(B : Type u) (A : Type v) (B' : Type w)` with three
  `[CommRing ...]` instances. Stacks rings here are commutative rings with one.
- Intermediate inclusions B ⊆ A ⊆ B': the three `[Algebra ...]` instances,
  `[IsScalarTower B A B']`, `[FaithfulSMul B A]`, `[FaithfulSMul A B']`.
  I read `faithfulSMul_iff_algebraMap_injective` in Algebra/Algebra/Basic.lean:329
  and `IsScalarTower.algebraMap_eq` in Algebra/Algebra/Tower.lean:127:
  these are precisely injective compatible homomorphisms, hence inclusions up
  to identifying each ring with its image. They add no algebraic restriction.
- B and B' semilocal: `[Finite (MaximalSpectrum B)]` and
  `[Finite (MaximalSpectrum B')]`. MaximalSpectrum/Defs.lean bundles exactly
  ideals with `IsMaximal`; finite cardinality expresses semilocality.
- B' integral over B: `[Algebra.IsIntegral B B']`. The dependency
  def-weil-pbc-integral-closure records `IsIntegral` and `integralClosure`.
  I read IsIntegral/Defs.lean:40–54 and Algebra/Basic.lean:216–225:
  integrality means a monic polynomial equation, and integralClosure has
  precisely those elements as its carrier. The module imports that dependency's
  Mathlib module; no domain or finite-module instance is imposed.
- Spec-surjectivity: `hspec : Function.Surjective
  (PrimeSpectrum.comap (algebraMap A B'))`. Prime/RingHom.lean:34 defines
  this as contraction of prime ideals, in the required direction B' to A.
- A semilocal: first conjunct `Finite (MaximalSpectrum A)`.
- Radical equality: second conjunct `Ideal.jacobson (⊥ : Ideal A) =
  (Ideal.map (algebraMap B A) (Ideal.jacobson (⊥ : Ideal B))).radical`.
  Jacobson/Ideal.lean:65 is the intersection of maximal ideals above an ideal;
  taking bottom gives the ring Jacobson radical. Ideal.map is the generated
  extension ideal, and Ideal/Operations.lean:798 defines radical by powers.
- Each x in A whose image lies in J(B'): final `∀ (x : A),
  algebraMap A B' x ∈ Ideal.jacobson (⊥ : Ideal B') → ...`.
- Some power in m_B A: `∃ m : ℕ, 0 < m ∧ x ^ m ∈ Ideal.map ...`.
  This also gives the node's radical-membership clause via mem_radical_iff.
  Positivity is equivalent to existence of any natural power: if a witness is
  zero, the ideal contains one and is the unit ideal, so exponent one works.
  The exponent depends on x, exactly as in the node.

Edge cases: independent arbitrary universes u/v/w; no characteristic, field,
Noetherianity, dimension, nonzero-element, or nontrivial-ring hypotheses.
Zero rings and empty spectra are allowed; with faithful inclusions a zero
ring forces the compatible rings to be zero. Empty maximal spectra give unit
Jacobson radicals, and exponent one suffices. x = 0 also permits exponent one.
There is no indexing-family nonemptiness requirement or fixed exponent n.
Every type/universe is explicitly bound, with no implicit variable needed.

Independent searches used different wording from the worker:
`msearch.py leansearch "In an integral extension of semilocal commutative rings
the Jacobson radical equals the radical of the extended Jacobson ideal"`
was unavailable (Internal Server Error; no negative verdict inferred).
`msearch.py loogle "Ideal.jacobson, Ideal.radical"` found
Ideal.jacobson_radical_eq_jacobson, Ideal.radical_le_jacobson, and results
requiring Jacobson, zero-dimensional, or Artinian rings; none is this statement.
`msearch.py leanfinder "Jacobson radical of an intermediate ring in an integral
extension of semilocal rings is the radical of the extended base Jacobson radical"`
found isJacobsonRing_of_isIntegral and Ideal.comap_jacobson among generic
results, with no exact match. `msearch.py grep
"jacobson.*radical|radical.*jacobson|semilocal" RingTheory` and direct rg
of Mathlib's GoingUp.lean found no exact theorem. Independent rg of
WeilConjectures and lean/Sheaf for semilocal and Jacobson/integral/overring
found related conductor, localization and divisor results only. The declared
name also has no duplicate in those trees. Thus the module is necessary.

Mismatch H8: the theorem docstring summarized the conclusion but omitted the
node's proof steps. I added all four steps, including dependency node names,
the finite-product prime argument and the empty-maximal-spectrum case.
I removed the unused Polynomial scope and replaced the broad Semilocal and
Prime.Topology imports by Maximal.Defs and Prime.RingHom, which supply the
actual notions used. The theorem signature and mathematical node statement
are unchanged; lean.statement now reproduces the file signature verbatim.
There is exactly one theorem with proof `sorry`, and no definition or proof
of an auxiliary statement was introduced. Source and blueprint docstrings,
namespace, line widths, and explicitly bound universes were checked.

Validation: scompile.py compiled the revised module cleanly in 1.4 seconds;
no warnings. deliver2.py --no-push printed OK: server compile and stage-2
preflight passed. Algebra/Defs.lean:36 was also read to verify that
Algebra.IsIntegral requires every element to be integral over the base.
