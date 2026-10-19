## Worker report

The module `Sheaf.RingTheory.PowerSeries.ExpSubstHom` states the complete node as the
single theorem `PowerSeries.exp_subst_hom`; its only proof is `sorry`.
No definitions, auxiliary axioms, new nodes, dependency repairs, or statement changes
are needed. No statement dispute or node fault was found.

Hypotheses and clauses, matched against the node:

- “R a commutative Q-algebra” is `(R : Type u) [CommRing R] [Algebra ℚ R]`.
  There is no field, domain, nontriviality, topology, or characteristic hypothesis.
- `R[[T]]` is Mathlib's `PowerSeries R`. For every argument, the formal exponential is
  exactly `(exp R).subst U`, the dependency's recorded composite.
- Membership in `TR[[T]]` is exactly `constantCoeff U = 0`; both U and W have this
  hypothesis in the addition clause. Negation and integer multiples preserve it.
- `exp(0) = 1` is the first conjunct, with the zero explicitly typed as `PowerSeries R`.
- The second conjunct quantifies over every pair U, W with these zero constant
  coefficients and states `(exp R).subst (U + W) = (exp R).subst U * (exp R).subst W`.
- The third conjunct says that for every such U there exists
  `e : (PowerSeries R)ˣ` with underlying series `(exp R).subst U`, and that
  `(exp R).subst (-U)` is the underlying series of `e⁻¹`. Existence of this unit is
  exactly the node's “exp(U) is a unit,” together with its specified inverse.
- The last conjunct quantifies over `(I : Type v) [Fintype I]`, every series family
  `U : I → PowerSeries R`, every `ε : I → ℤ`, and zero constant coefficient at every
  index. Its conclusion supplies unit representatives `e` whose underlying series
  are exactly the exponentials and states
  `(exp R).subst (∑ i : I, ε i • U i) = ↑(∏ i : I, e i ^ ε i)`.
  Here `•` is ordinary integer multiplication in the additive group of series and
  `^` is integer power in the commutative group of units. This is the finite-family
  identity of the node, with integer powers taken in the unit group as in proof
  step 3. The representatives are uniquely determined by their underlying series
  (`Units.val_injective`), so the existential presentation does not change the
  meaning of the equation or make a noncanonical choice. Conversely any prescribed
  unit representatives must equal these ones. The third conjunct already proves
  the existence needed to form the RHS. The independent universe v includes finite
  index types of every size, and no nonemptiness or decidable-equality hypothesis
  excludes the empty family.

Dependency declarations read and used:

- `def-weil-formal-power-series`: Mathlib match `PowerSeries`, defined in
  `Mathlib.RingTheory.PowerSeries.Basic` as `MvPowerSeries Unit R`; coefficient
  sequences, coefficientwise addition, and Cauchy multiplication are its API.
- `def-weil-power-series-exponential`: the recorded Mathlib composite
  `(PowerSeries.exp R).subst U`. `PowerSeries.exp` in
  `Mathlib.RingTheory.PowerSeries.Exp` has coefficients
  `algebraMap ℚ R (1 / n!)`. `PowerSeries.subst` and
  `PowerSeries.HasSubst.of_constantCoeff_zero'` in
  `Mathlib.RingTheory.PowerSeries.Substitution` give exactly the substitution
  permitted by the hypothesis. The two modules are public imports; they also
  cover both proof dependencies. No private copy of the exponential was introduced.
- The coercion and group inverse of units were read in
  `Mathlib.Algebra.Group.Units.Defs`. An ambient inverse on series over a general
  commutative ring was deliberately avoided: integer powers belong in its units.

Edge cases checked mathematically before writing: U = W = 0 gives one; W = -U
recovers the unit inverse; the constant coefficient (degree zero) of every exponential
is one, including the zero ring. The empty index type gives the first conjunct and
has its unique empty unit family. A singleton with ε = 0 gives one, ε = 1 gives its
exponential, and ε = -1 gives the inverse clause. Zero members and mixed positive/
negative integer exponents retain zero constant coefficient. Arbitrary commutative
Q-algebras, including rings with nilpotents and the zero ring, remain allowed.

Source checked: Milne's PDF, §26 p.151, defines the exponential by its formal series;
the proof of Theorem 27.6 p.156 has the alternating exponential product at “move the
inner sum outside.” These are exactly the notion and use recorded by the node.
The theorem docstring contains the complete finite-coefficient/binomial calculation,
including degree zero, followed by the inverse argument, induction on integer
multiples, and induction on the finite family.

Searches performed on 2026-10-17 (via the prescribed msearch.py wrapper where applicable):

- LeanFinder: “Over a commutative rational algebra, the exponential of the sum of two
  formal power series with zero constant coefficient equals the product of their
  exponentials.” Eight hits: `PowerSeries.exp_mul_exp_eq_exp_add`, `exp_pow_sum`,
  `exp_mul_exp_neg_eq_one`, `exp`, and four normed-algebra results. The power-series
  identity only rescales by coefficient-ring constants; the analytic results impose
  normed/completeness hypotheses. None is the node's statement.
- Loogle: `PowerSeries.exp, PowerSeries.subst`. Two hits:
  `PowerSeries.subst_exp_log` and `PowerSeries.subst_log_exp_sub_one`, the composition
  inverse identities. Neither is addition of arbitrary substituted series.
- LeanSearch: “formal exponential of sum of zero constant coefficient power series
  equals product of exponentials.” Eight hits involving analytic exponentials,
  `WithZero.exp_add`, and `DividedPowers.exp_add`; none is the formal substituted
  exponential over an arbitrary commutative Q-algebra.
- msearch grep: `exp_add|exp_mul_exp|subst_exp` in `RingTheory/PowerSeries`.
  Five hits, all in Exp.lean's documentation or the constant-rescaling identities.
  Read the complete definitions and signatures in Exp.lean and Substitution.lean.
- `rg` over the upstream `WeilConjectures` and project `lean/Sheaf` for
  `PowerSeries.exp`, `exp_hom`, `formal exponential`, and `exp`/`subst` combinations.
  Upstream TraceDatum and DetTrace contain derivative and trace identities for
  specific exponential substitutions; no arbitrary-substitution homomorphism.
  No relevant declaration in `lean/Sheaf` was found.
- Searched upstream source for `lem-weil-power-series-exp-hom`; no hit. Searched
  Mathlib, upstream source, `lean/Sheaf`, and `dag/lean_names_upstream.json` for the
  proposed name `exp_subst_hom`; no collision. There is no repair note for this item.

Validation on 2026-10-17: the resumed worker re-read the complete node, both
Mathlib dependency records, the full defining signatures and docstrings, and the
Milne source passages. The sandbox file compiled cleanly through scompile.py:
the wrapper's sandbox and library checks finished in 1.3 s and 1.4 s, respectively,
with no errors or warnings. The recorded signature matches the file verbatim;
all Lean lines are at most 100 characters; the node copy differs only in `lean`.

The resumed worker repeated the prescribed LeanFinder search with query “formal
power series exponential evaluated by substitution preserves addition for series
with zero constant coefficient”: eight results, including the constant-rescaling
identity, map_exp, exp_pow_sum, exp_mul_exp_neg_eq_one, exp_pow_eq_rescale_exp,
exp, and two analytic results. None states the arbitrary-substitution identity.
Loogle “PowerSeries.exp, PowerSeries.subst” again returned only the two exp/log
inverse identities. The msearch grep again returned five documentation or
constant-rescaling hits. Direct searches of upstream, lean/Sheaf, and the
upstream-name index found no exact statement or proposed-name collision.

The required `deliver2.py N9 lem-weil-power-series-exp-hom --no-push` is run after
this report update; its final result is the readiness criterion. Independent
second reading and delivery are left to the designated second reader.

## Second reading by N9

I independently read the full node and its three proof steps, the sandbox module,
both statement-dependency records, and the actual Mathlib declarations. I checked
Milne, Lectures on Étale Cohomology, §26 p.151 and the proof of Theorem 27.6 p.156,
and Deligne, Weil I, §1.5 pp.275–276, through the local PDFs with pdftotext. Milne
defines the exponential by its factorial series and uses the finite alternating
exponential product at “move the inner sum outside”; Deligne passes from the
alternating logarithmic identity to (1.5.4). Their geometric hypotheses concern
that application, not an additional hypothesis of this formal algebra identity.
The exponential dependency's source, 49_zeta_linear_algebra.tex lines 95–131,
explicitly assumes a commutative Q-algebra and defines exactly this factorial
series on series with zero constant coefficient.

My object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

- Coefficient ring: `(R : Type u) [CommRing R] [Algebra ℚ R]` is precisely a
  commutative Q-algebra. No field, domain, nontriviality, topology, Noetherian,
  or finiteness hypothesis has been introduced. Pass.
- Indeterminate and series ring: `PowerSeries R`, Mathlib Basic.lean:60, is
  `MvPowerSeries Unit R`; its `coeff_mul` at line 249 is the Cauchy coefficient
  formula required by def-weil-formal-power-series. One fixed formal variable
  needs no additional binder. Pass.
- Formal exponential: every occurrence is `(exp R).subst U`, exactly the
  composite recorded by def-weil-power-series-exponential. Exp.lean:49 defines
  `exp` with coefficients `algebraMap ℚ R (1 / n!)`; Substitution.lean:158
  defines substitution. Its `coeff_subst'` gives the coefficientwise factorial
  sum, and `HasSubst.of_constantCoeff_zero'` at line 67 makes each indicated
  substitution legitimate. I checked the dot notation against `coeff_subst'`
  and the upstream uses: it substitutes U into exp, in that order. Pass.
- Domain `TR[[T]]`: `constantCoeff U = 0`, and likewise for W and each U i.
  These are precisely vanishing constant terms, not the more general nilpotent
  constant terms that Mathlib also allows for substitution. Sums, negatives,
  and integer multiples remain in that domain by the constant-coefficient ring
  homomorphism. Pass.
- Zero identity: first conjunct `(exp R).subst (0 : PowerSeries R) = 1`.
  Pass.
- Addition identity: second conjunct quantifies over arbitrary `U W`, then
  assumes both zero constant coefficients, then states the required equality
  at U + W. No commuting-pair hypothesis is needed in this commutative ring.
  Pass.
- Unit and negative identity: third conjunct quantifies over every admissible
  U and supplies `e : (PowerSeries R)ˣ` with `↑e = (exp R).subst U` and
  `(exp R).subst (-U) = ↑(e⁻¹)`. This says both that the exponential is a unit
  and that its specified inverse is the exponential of -U. The unit is unique
  by `Units.val_injective` (Units/Defs.lean:113), so this presentation adds no
  data choice and loses no clause. Pass.
- Finite-family objects and quantifiers: fourth conjunct has arbitrary
  `(I : Type v) [Fintype I]`, `U : I → PowerSeries R`, `ε : I → ℤ`, then the
  vanishing condition at each i. Every finite family, in every index universe,
  is covered. The full-type sum also covers a finite subset by its subtype;
  no decidable-equality or nonemptiness assumption is imposed. Pass.
- Finite-family identity: `ε i • U i` is integer additive multiplication and
  `e i ^ ε i` is the integer power in the commutative unit group. The supplied
  family has prescribed values `↑(e i) = (exp R).subst (U i)`, followed by
  `(exp R).subst (∑ i : I, ε i • U i) = ↑(∏ i : I, e i ^ ε i)`.
  Unique unit representatives make this exactly the node's product of integer
  powers, including negative powers. It is neither weaker nor stronger. Pass.

Edge cases: U = W = 0 gives the first identity; W = -U gives the inverse.
Degree N = 0 has only the zeroth-power contribution, including in the zero
ring. The empty index type has its empty unit family and gives exp(0) = 1.
Singleton exponents 0, 1, and -1 give one, the exponential, and its inverse;
zero members and mixed signs introduce no restrictions. The zero ring and
commutative Q-algebras with nilpotents are included. A nonzero positive-
characteristic ring cannot carry the node's Q-algebra structure, and no
additional characteristic condition is imposed. `universe u v` binds both
universes independently; all objects and variables are explicitly bound.
Empty schemes and zero cohomology objects are not objects of this node.

Independent H4 searches (2026-10-17):

- Prescribed msearch LeanFinder query: “The substitution of f+g into the formal
  exponential is the product of substitutions of f and g, in a rational
  commutative ring with f(0)=g(0)=0”. Eight hits, including the constant-rescaling
  theorem, map_exp, analytic exponential results, and subst_add. I opened
  Exp.lean:123–169: exp_mul_exp_eq_exp_add quantifies over coefficient-ring
  constants a,b and rescales exp; it does not state this arbitrary-substitution
  identity. `subst_add` preserves addition in the outer series, which is a
  different assertion.
- Prescribed msearch Loogle query `PowerSeries.exp, PowerSeries.subst` returned
  only `subst_exp_log` and `subst_log_exp_sub_one`, the exp/log composition
  inverse identities. Neither matches this statement.
- Prescribed msearch LeanSearch query: “Composition of the formal exponential
  series with two zero constant term series takes their addition to
  multiplication over a commutative Q algebra”. Eight hits: analytic exp_add,
  exp_sum and related analytic results, DividedPowers.exp_add, and the
  constant-rescaling identity. No exact match.
- Prescribed msearch grep `subst.*(add|zsmul|sum)|exp.*(hom|add)` returned a
  capped and mostly unrelated list, so I did not treat it as exhaustive.
  Direct rg on Mathlib's PowerSeries and MvPowerSeries directories for
  `exp_add|exp_mul_exp|exp_subst_hom|subst_exp|exp.*zsmul` found only the
  constant-rescaling results and documentation in Exp.lean.
- Direct rg over upstream WeilConjectures, project lean/Sheaf, and the
  upstream-name index for `exp_subst_hom|exp.*subst|subst.*exp|formal exponential`
  found no duplicate or name collision. I opened the nearby upstream
  `X_mul_derivative_exp_subst` and `inv_charpolyRev_eq_exp`; they assert a
  derivative identity and a determinant identity over fields, respectively,
  not this general exponential homomorphism.

H5–H9: the module has no definitions, private copies, local notation, local
instances, hidden proof obligations, or auxiliary theorems. Its single theorem
has exactly `by sorry`. The source/blueprint docstrings identify this node and
carry all three proof steps: finite truncation and binomial reindexing with
degree zero; construction of the inverse; natural and negative integer powers
and induction on the finite family. Both public imports serve the statement
and its two proof dependencies. No new node, dependency module, repair note,
statement_change, or disputed statement is present, so H12/H13 and the
correction/citer audit do not apply.

Mismatches found: none. I preserved the module and node record unchanged and
added this independent reading to the report. The node's `lean.statement`
was checked verbatim against the file signature; the remaining node fields
match the repository copy. All Lean lines are at most 100 characters.

Validation: the required scompile.py invocation compiled the delivered file
in both sandbox and library modes in 1.6 s and 1.5 s, with no errors or warnings.
The prescribed deliver2.py dry run and delivery follow this report.
The dry run printed `OK (dry run): commit 5a5f991d00 passes the preflight and
compiles; nothing pushed`. No repair was required by preflight.
