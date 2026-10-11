## Worker report

The module `lean/Sheaf/RingTheory/SerreCriterionReduced.lean` states
`Ring.isReduced_iff_serreR_zero_and_serreS_one`. Its sole theorem has proof `sorry`;
no definitions or proofs were added. The node copy changes only `lean`.

Source read: [Stacks Tag 031R](https://stacks.math.columbia.edu/tag/031R), statement
and proof, and [Tag 031P](https://stacks.math.columbia.edu/tag/031P), parts (1) and
(2). The cited local `literature/stacks-project/algebra.tex` is absent on this
machine, so these source pages were opened online. The statement agrees with the
source; no correction, disputed statement, new node or dependency module is needed.
The declaration docstring carries all five node proof steps and names their DAG
facts, including finite-height induction and both uses of joint detection of zero.

Hypothesis and clause correspondence:

- A ring `R`: `(R : Type u) [CommRing R]`, with explicitly declared `universe u`.
  Commutativity is the convention of Stacks Algebra and the dependency definition.
- Noetherian: `[IsNoetherianRing R]`, exactly the recorded dependency declaration,
  meaning that every ideal is finitely generated.
- Reduced, with no nonzero nilpotent elements: Mathlib `IsReduced R`, whose field
  `eq_zero` is `∀ x : R, IsNilpotent x → x = 0`.
- If and only if: `↔`, so both directions are stated.
- Both `(R_0)` and `(S_1)`: `IsSerreR R 0 ∧ IsSerreS R 1`, using the recorded
  definitions rather than private replacements.
- Every height-zero prime localization is regular local: unfolding `IsSerreR R 0`
  gives `∀ (p : Ideal R) [p.IsPrime], p.height ≤ (0 : ℕ∞) →
  IsRegularLocalRing (Localization.AtPrime p)`. In the nonnegative height type,
  height ≤ 0 is exactly height = 0.
- For every prime the depth is at least min(1, local dimension): unfolding
  `IsSerreS R 1` gives `∀ (p : Ideal R) [p.IsPrime],
  min (1 : ℕ∞) p.height ≤
  IsLocalRing.depth (R := Localization.AtPrime p) (Localization.AtPrime p)`.
  The depth is explicitly of the localized ring as module over itself. Prime
  height is its local Krull dimension, as in the dependency and Stacks 00KF;
  Mathlib's `IsLocalization.AtPrime.ringKrullDim_eq_height` supplies this equality.

Dependency declarations used (full signatures and docstrings read):

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, an abbreviation of
  `IsNoetherian R R`, and `isNoetherianRing_iff` (the record's additional declaration).
  This module is available transitively through the single used import.
- `Sheaf.RingTheory.SerreConditions`: `Ring.IsSerreR` and `Ring.IsSerreS`, both
  `(R : Type u) [CommRing R] [IsNoetherianRing R] (k : ℕ) : Prop`.
  Their complete bodies and docstrings were read in the repository.
- Mathlib `IsReduced` was read in `Mathlib/Algebra/GroupWithZero/Basic.lean:191`.
  The underlying `IsLocalRing.depth` was also read in `Sheaf.RingTheory.Depth`.

Edge cases checked mathematically: the zero ring is reduced and has no prime
ideals, so both Serre conditions are vacuous; no `Nontrivial R` binder excludes it.
For a field, its only prime has height zero, its localization is regular, and the
S1 bound is zero. Nonreduced zero-dimensional rings such as k[ε]/(ε²) fail R0,
so S1 being automatic does not incorrectly assert reducedness. Reduced singular
rings are permitted: R0 requires regularity only at height-zero primes. Positive
local dimension imposes exactly depth ≥ 1. No global finite-dimension assumption
is added (a Noetherian ring need not have bounded prime heights). All universes and
variables in the theorem are bound explicitly.

Searches actually run with `/home/ubuntu/weil-launcher/msearch.py M1
lem-weil-pbc-serre-criterion-reduced`:

- `leansearch`, query `Noetherian ring reduced if and only if Serre R0 S1`:
  unavailable, Internal Server Error; this is not evidence of absence.
- `leanfinder`, query `Noetherian ring is reduced iff Serre conditions R0 and S1`:
  eight results, including Noetherian criteria from prime ideals, Noetherianity
  of Spec and maximal localizations, and the dimension-zero Artinian theorem;
  none states the reducedness criterion.
- `loogle`, query `IsReduced, IsRegularLocalRing`: zero hits.
- `grep`, query `Serre|isReduced_iff|IsSerre`, subdirectory `RingTheory`: thirteen
  hits on nilpotence equivalences or citations of Serre's books; no criterion.
- `rg -n 'Serre|isReduced_iff|IsSerre'` on the source `WeilConjectures` and the
  project's `lean/Sheaf/RingTheory`: source hits concern Serre duality, vanishing,
  projective dimension, and geometric reducedness. Project hits include the
  recorded `SerreConditions.lean` definitions and references to normality, with
  no existing reducedness equivalence.
- `grep -rn 'lem-weil-pbc-serre-criterion-reduced'` on source `WeilConjectures`:
  no hits.
- `rg -n 'isReduced_iff_serre'` on source and project Lean: no hits, confirming
  the chosen declaration name is unused.

Validation: server single-file compilation is run with `scompile.py`; the final
required `deliver2.py --no-push` checks the node record, module, and compile.
The second reader will add the independent second-reading section and deliver.

## Second reading by M1

I reread the node and the module independently against Stacks Tags 031R and 031P.
The source states: (i) an arbitrary Noetherian ring `R`; (ii) equivalence between
`R` reduced and `R` satisfying `(R_0)` and `(S_1)`; (iii) `(R_0)` means every
height-zero prime localization is regular; and (iv) `(S_1)` means that for every
prime localization the depth is at least the minimum of one and its dimension.
The node adds exactly the two recorded notions `[def-weil-pbc-noetherian-ring]`
and `[def-weil-pbc-serre-conditions-rk-sk]`.

The Lean rendering is exact item by item. The object and hypotheses are
`(R : Type u) [CommRing R] [IsNoetherianRing R]`; no nontriviality, finite
Krull-dimension, or characteristic assumption is introduced. The left side is
`IsReduced R`, Mathlib's absence of nonzero nilpotents. The right side is
`IsSerreR R 0 ∧ IsSerreS R 1`, using the dependency module's definitions. On
unfolding those definitions, the first conjunct quantifies over every prime
`p : Ideal R` with `p.height ≤ (0 : ℕ∞)` and requires
`IsRegularLocalRing (Localization.AtPrime p)`; this is exactly height zero since
`ℕ∞` is nonnegative. The second quantifies over every prime and requires
`min (1 : ℕ∞) p.height ≤ IsLocalRing.depth (R := Localization.AtPrime p)
(Localization.AtPrime p)`, exactly depth at least `min{1, dim(R_p)}` because
`p.height` is defined as that localization dimension. The outer connective is
`↔`, preserving both directions and all quantifier order. The declaration
`Ring.isReduced_iff_serreR_zero_and_serreS_one` and its theorem docstring match
this signature and include the node's five proof steps.

Edge cases checked: the zero ring is allowed (the prime quantifiers can be
vacuous), fields satisfy both conditions, height zero is represented by the
`≤ 0` form without excluding any prime, and `k = 0` is supported by the
underlying definitions. No universe is left implicit: the ring universe is the
single explicit `u`, and there is no independent test universe. Empty prime
families and nonreduced zero-dimensional examples are covered by the same
quantifiers.

I reran the existing searches: `msearch.py` LeanSearch (criterion query,
service unavailable), LeanFinder and Loogle (no reducedness Serre criterion),
grep in pinned Mathlib RingTheory (no `(R_k)`/`(S_k)` criterion), and `rg` in
`WeilConjectures` and project `lean/Sheaf` (only the existing Serre conditions,
no criterion theorem). The declaration name is unused elsewhere. Thus no
existing declaration replaces this module.

No mismatch was found and no source, dependency, or statement correction was
needed. The only representational difference is the dependency's mathematically
equivalent `p.height ≤ 0` encoding of height `0`; it is forced by the recorded
`IsSerreR` definition and does not change the node's meaning. The module compiles
cleanly with `scompile.py`; only its theorem proof remains `sorry`, as required
for stage 2.
