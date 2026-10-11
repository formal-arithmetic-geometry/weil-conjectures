## Worker report

Module: `Sheaf.RingTheory.Derivation.CompletionAndLocalization`.
Declaration: `Derivation.exists_completion_and_unique_localization`.
The theorem states both parts of lem-weil-pbc-derivation-extends, including the
specified formulas. Its sole proof is `sorry`; no definition or auxiliary proof
is introduced. The item copy changes only `lean`.

Source checked: Stacks Project, More on Algebra, Lemma 07PE, items (1), (2) and
their proof, https://stacks.math.columbia.edu/tag/07PE. The local literature
checkout has no `more-algebra.tex`, so the primary source was read online.
The finite-type extension at the end of 07PE is intentionally excluded,
as the node specifies. The declaration docstring carries all eleven proof
steps of the node, including the quotient-rule well-definedness calculation.

Hypotheses and clauses:

- A commutative ring R is `(R : Type u) [CommRing R]`, with arbitrary explicit
  universe `u`. An additive absolute derivation is `D : Derivation ℤ R R`.
  Integer linearity is automatic for additive maps of abelian groups; the
  scalar action of R on itself is multiplication. Thus its bundled Leibniz
  rule is exactly `D (a * b) = a * D b + b * D a`. The bundled `D 1 = 0`
  is a consequence of that rule (proof step 1), not an extra hypothesis.
- Part (1) quantifies `∀ I : Ideal R`, without finite-generation, Noetherian,
  separatedness, completeness, or stability-under-D hypotheses.
- The power bound stated in parentheses is
  `∀ (n : ℕ) (a : R), a ∈ I ^ (n + 1) → D a ∈ I ^ n`.
  The harmless n=0 case says D maps R into R, as in proof step 2.
- The ring R-completion and canonical map from def-weil-pbc-adic-completion
  are `AdicCompletion I R` and `algebraMap R (AdicCompletion I R)`.
  Mathlib uses components indexed by n≥0; its zero-th quotient is R/R,
  so including that unique component gives exactly the node's n≥1 limit.
- The extension exists as `∃ Dc : Derivation ℤ (AdicCompletion I R)
  (AdicCompletion I R)`; the next conjunct says for every a that
  `Dc (algebraMap R (AdicCompletion I R) a) =
  algebraMap R (AdicCompletion I R) (D a)`.
- The induced additive quotient maps are
  `∃ d : (n : ℕ) → (R ⧸ I ^ (n + 1)) →+ (R ⧸ I ^ n)`.
  For `1 ≤ n`, their defining clause is
  `d n (Ideal.Quotient.mk (I ^ (n + 1)) a) =
  Ideal.Quotient.mk (I ^ n) (D a)`.
  Surjectivity of the quotient map determines each map; no arbitrary map
  replaces the specified induced one. The extra d 0 has zero target R/R
  and places no restriction. Additivity is already in `→+`.
- The exact component formula for every x and `1 ≤ n` is
  `AdicCompletion.evalₐ I n (Dc x) =
  d n (AdicCompletion.evalₐ I (n + 1) x)`.
  This states how Dc acts on every compatible sequence, not merely on
  the image of R. There is no uniqueness claim for arbitrary completion
  derivations merely agreeing on R.
- Part (2) quantifies `∀ W : Submonoid R`. Submonoid precisely supplies
  membership of 1 and closure under multiplication, without forbidding 0.
  `Localization W` is Mathlib's ring of fractions, and
  `Localization.mk a w` is a/w; its equivalence relation and ring
  operations are those in the node, including rings with zero divisors.
  The canonical λ is `algebraMap R (Localization W)`.
- The localization derivation exists as
  `∃ Dw : Derivation ℤ (Localization W) (Localization W)`.
  Its first clause says `Dw (algebraMap R (Localization W) a) =
  algebraMap R (Localization W) (D a)` for every a.
- The formula for every a and denominator w is
  `Dw (Localization.mk a w) = Localization.mk (D a) w -
  Localization.mk (a * D (w : R)) (w ^ 2)`.
  The latter term is exactly aD(w)/w²; no division on the original
  ring R is assumed. Powers of bundled w are powers in W.
- Its final clause quantifies over every other derivation `Dw'`, assumes
  only its agreement with D on R, and concludes `Dw' = Dw`.
  Thus uniqueness is among all extensions, without assuming the other
  extension already satisfies the quotient formula.

Dependency declarations read and used:

- def-weil-pbc-adic-completion records `AdicCompletion` in
  `Mathlib.RingTheory.AdicCompletion.Basic`; its full definition is the
  subtype of compatible quotient sequences. Its companion `IsAdicComplete`
  (Hausdorff and precomplete) is read but not needed by this statement.
- `Mathlib.RingTheory.AdicCompletion.Algebra` provides the same completion's
  componentwise commutative-ring structure, canonical R-algebra map and
  `AdicCompletion.evalₐ`. This import also imports the recorded Basic module.
  evalₐ identifies the module quotient by I^n • ⊤ with the ring quotient
  R/I^n, so its evaluation is precisely the x_n in the node.
- `Mathlib.RingTheory.Derivation.Basic`, `Derivation`, supplies the existing
  bundled linear/additive Leibniz maps; `Mathlib.RingTheory.Localization.Basic`
  provides `Localization`, `Localization.mk` and its R-algebra structure.
  All imported modules contribute notions directly used in the signature.

Edge cases checked before writing: the zero ring and arbitrary characteristic;
I=0 (completion is R), I=R (all quotients and completion are zero); n=0
(the power bound is tautological and the unused d 0 has zero target);
W containing 0 (the localization is zero, so the formulas and uniqueness
remain true), W={1}, and W containing zero divisors (the node's u² argument
handles equality of fractions without cancellation in R). Nothing requires
R→completion or R→localization to be injective. The choice of ℤ does not
restrict characteristic or require a field. All binders and universes are
explicit.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leansearch "derivation extension adic completion localization"`:
  unavailable, Internal Server Error; no verdict based on this service.
- `msearch.py ... leanfinder "A derivation of a commutative ring extends to its
  adic completion and uniquely to any localization"`: eight hits including
  formally smooth lifting to completions and derivations to square-zero
  ideals; none states this theorem.
- `msearch.py ... loogle "Derivation, AdicCompletion"`: zero hits.
- `msearch.py ... grep 'Derivation|derivation' RingTheory/AdicCompletion`:
  zero hits. rg on WeilConjectures and lean/Sheaf for derivation/completion
  combinations and this node id finds only the docstring in
  `Sheaf/RingTheory/PolynomialFormalFiber.lean`, not this declaration.
- rg on the source's RingTheory finds
  `WeilConjectures/RingTheory/Derivation/Localization.lean`.
  Its full module was read: `IsLocalization.extendDerivation` constructs
  the localization extension for additive derivations along a ring map;
  `extendDerivation_algebraMap`, `extendDerivation_mul`, and `derivation_ext`
  describe extension, Leibniz, and uniqueness. It does not state part (1)
  or the combined result with the component and fraction formulas.
  Therefore the node cannot be recorded as that existing declaration.
  No localization notion or construction is duplicated in this delivery.
- rg for `exists_completion_and_unique_localization` in Mathlib,
  WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json found
  no name conflict.

No new notion, unusable dependency, statement correction, or disputed
statement was found. Server compile of the module is clean; the expected
stage-2 sorry is its only postponed proof. The independent second reader
will add their own reading; this worker has not written one.

## Second reading by H1

I read the node statement, its source (Stacks Project, More on Algebra, Tag 07PE,
items (1) and (2)), the dependency node `def-weil-pbc-adic-completion`, and the
module independently. The objects and clauses match as follows.

- `R : Type u` with `[CommRing R]` and `D : Derivation ℤ R R` render the
  commutative ring and additive Leibniz derivation; no characteristic, domain,
  finiteness, or injectivity assumption is added.
- For every `I : Ideal R`, `AdicCompletion I R` and its `algebraMap` render the
  completion and canonical map. The existential `Dc` is a derivation extending
  `D`; the existential additive family `d : (n : ℕ) → (R ⧸ I^(n+1)) →+
  (R ⧸ I^n)` renders the induced quotient maps. Its formula is required for
  `1 ≤ n`, exactly the source's `n ≥ 1` range, and the final `evalₐ` equation
  renders the componentwise sequence formula for every completion element.
- For every `W : Submonoid R`, `Localization W` and `Localization.mk` render
  the general multiplicative localization and fractions. `Dw` extends `D`, the
  displayed quotient rule holds for every numerator and denominator, and the
  final universal quantifier gives uniqueness among all extensions.

The first reading's Lean had an extra conjunct asserting
`∀ n a, a ∈ I^(n+1) → D a ∈ I^n`. In the node and source this is the
well-definedness justification for the induced maps, not a separate conclusion;
adding it made the Lean statement strictly stronger. I removed that conjunct from
the module and synchronized the node's `lean.statement`. No other mismatch was
found. The harmless unconstrained `d 0` component is needed only to use a single
natural-number family; the node constrains exactly the `n ≥ 1` components.

Edge cases checked: zero rings and arbitrary characteristic; `I = 0` and `I = R`;
`n = 0` (outside the constrained quotient-map range); `W = {1}`, `W` containing
zero, and zero divisors in `R`; no map injectivity is assumed. Searches with
`msearch.py` (LeanSearch, LeanFinder, Loogle) and `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf` found no existing combined statement or
duplicate notion. The repaired module compiles cleanly with its sole expected
`sorry`.
