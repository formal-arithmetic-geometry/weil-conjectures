## Worker report

The item module `lean/Sheaf/RingTheory/HenselizationsCommonNormalCover.lean`
defines `RingHom.exists_common_normal_henselization_cover` with the exact node
statement. It binds a commutative ring `A`, two prime ideals, a commutative
normal integral domain `P`, a surjective `π : P →+* A`, and for each selected
prime `p` and inverse image `q` the localization map and ordinary henselization
objects. The conclusion requires `IsLocalHom` and `Function.Surjective` for
`φ`, locality of `Localization.localRingHom`, and both displayed composition
 equalities. Every hypothesis and clause is rendered directly in the theorem
signature; the proof is the required `sorry`.

Dependencies used are `IsDomain` and `IsIntegrallyClosed` for
`def-weil-pbc-normal-ring`; `Localization.AtPrime` and
`Localization.localRingHom` for `def-weil-pbc-localization-at-prime`;
`Algebra.IsHenselizationAtPrime` from
`Sheaf.RingTheory.HenselizationAtPrime` for
`def-weil-pbc-henselization-at-prime`; and the recorded polynomial counit and
unique-factorization declarations for `lem-trf-normal-polynomial-surjection`.
The proof documentation also cites the localization-of-quotient dependency and
the Tag 05WQ quotient-henselization dependency.

Edge cases checked: `p₁ = p₂` is permitted; no finite-generation condition on
`A` occurs; nilpotent or zero-divisor input rings are allowed; the zero ring has
no prime instances; all ring, prime, algebra, and universe binders are
explicit.

Searches recorded in `searches.jsonl` found no existing common-cover theorem.
LeanFinder/Loogle/LeanSearch found only general henselian and localization
lemmas. Mathlib and project `rg` searches found no matching declaration. The
full `Algebra.IsHenselizationAtPrime` signature and docstring were read and
used.

## Dependency modules

The proof dependency `lem-trf-henselization-quotient-at-prime` (Stacks Tag 05WQ)
is already landed on newtargets-dag by group NQ: node
`dag/nodes/sec-trace-formula/lem-trf-henselization-quotient-at-prime.json`,
module `Sheaf.TraceFormula.HenselizationQuotientAtPrime`, declaration
`Algebra.henselization_quotient_at_prime`. Its reviewer fix
(NT-stage2-cc-37a8f557a) pinned the henselization algebra of `H ⧸ IH` to the
canonical quotient structure map. The item module does not import this module;
the node is cited only in `proof_deps`. This delivery had carried an older,
weaker copy of that module at the same path. In the copy, the henselization
algebra of the quotient was an arbitrary existential, not tied to the induced
map from `R ⧸ I`. The maintainer's review replaced the copy with the landed NQ
text, byte for byte, so landing leaves the dependency module and its record
unchanged.

Validation (maintainer review, 2026-10-18): the item module and the landed
dependency module each compile cleanly with `tools/nt_compile.py` (rc 0; the
only open goal is the statement's `sorry`).

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
