## Worker report

`Sheaf.NumberTheory.DvrGaloisDegreeData` states
`NumberTheory.dvr_galois_degree_data`. Its only proof is `sorry`; it adds no
helper definition, axiom, instance or additional theorem. The node's natural
statement is unchanged, and only `lean` changes in its JSON copy.

I checked the earlier sandbox attempt against the current DAG and Stacks
`more-algebra.tex`: Tag 09E8 (`remark-finite-separable-extension`, lines
33006–33038), Tag 09EA (`lemma-galois`, lines 33179–33189), and Tag 09EB
(`lemma-galois-conclusion`, lines 33192–33204). The current statement renders
every hypothesis and clause as follows.

- The DVR `A` is `(A : Type u) [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]`. This is the node's nonfield local PID
  convention, including its nonzero maximal ideal.
- Its fraction field is `(K : Type v) [Field K] [Algebra A K]
  [IsFractionRing A K]`. Its residue field `k` is canonical, rather than an
  additional arbitrary field: it is the residue field at
  `IsLocalRing.maximalIdeal A`, equivalently `A / maximalIdeal A`.
- The finite extension is `(L : Type w) [Field L] [Algebra K L]
  [FiniteDimensional K L]`. `[IsGalois K L]` supplies separability and
  `Normal K L`, whose `splits'` field is precisely the node's definition of
  normality by splitting of each minimal polynomial. `[Algebra A L]` and
  `[IsScalarTower A K L]` express the compatible inclusion.
- The group `G` is Mathlib's `Gal(L / K)`, the group of `K`-algebra
  automorphisms of `L`.
- The integral closure is `(B : Type z) [CommRing B] [IsDomain B]
  [Algebra A B] [Algebra B L] [IsScalarTower A B L]
  [IsIntegralClosure B A L]`. Mathlib's characteristic predicate says that
  `B` embeds in `L` with image exactly `integralClosure A L`; it is not an
  arbitrary integral subring. This merely allows any representation of the
  node's integral closure. No finiteness or fraction-field property of `B`
  is added as a hypothesis. All four universes are independent.
- Write `X = (IsLocalRing.maximalIdeal A).primesOver B`. The conclusions
  `X.Finite` and `X.Nonempty` give its finite nonempty set. The explicit
  equivalence `∀ q : Ideal B, q.IsMaximal ↔ q ∈ X` identifies this set
  exactly with the maximal ideals of `B`, as in Tag 09E8.
- `MulAction.IsPretransitive (Gal(L / K)) {q : Ideal B // q ∈ X}` gives
  transitivity of the canonical action. The instance in
  `Mathlib.NumberTheory.RamificationInertia.Galois` sends `q` to
  `Ideal.map (galRestrict A K L B σ) q`, as verified by
  `Ideal.coe_smul_primesOver_eq_map_galRestrict`; no arbitrary action is
  quantified over or chosen.
- For every `q` in that subtype,
  `IsDiscreteValuationRing (Localization.AtPrime q.1)` and
  `IsLocalHom (algebraMap A (Localization.AtPrime q.1))` give the specified
  DVR localization and local map. Subtype membership supplies the canonical
  prime and lies-over instances.
- For every base uniformizer `πA` and every local uniformizer `tq`, encoded
  by `Irreducible πA` and `Irreducible tq`, the theorem supplies positive
  integers `e_q,f_q` and a unit `u_q` with
  `algebraMap A (Localization.AtPrime q.1) πA = ↑u_q * tq ^ e_q`.
  `IsDiscreteValuationRing.irreducible_iff_uniformizer` identifies these
  hypotheses with generators of the relevant maximal ideals. The statement
  covers every choice of both uniformizers, not just a selected pair.
- `e_q = Ideal.ramificationIdx q.1 A` identifies the exponent with the
  canonical ramification index, the length of `B_q / m_A B_q`.
  `f_q = Ideal.inertiaDeg q.1 A` identifies the residue degree with the
  canonical vector-space dimension of the residue extension. In particular,
  `Ideal.inertiaDeg_eq_of_isMaximal` states exactly
  `q.inertiaDeg A = Module.finrank (A / m_A) (B / q)` for these maximal
  ideals. Positive finrank of this field extension also entails finite
  dimension: an infinite-dimensional vector space has finrank zero.
- The final `∃ e f g : ℕ` gives positive common values, `g = X.ncard`,
  equality of each canonical ramification index to `e` and each inertia
  degree to `f`, and `Module.finrank K L = g * e * f`. This is the node's
  full independence and degree formula.

Statement dependency declarations read (full signatures and docstrings):

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`; also its
  `irreducible_iff_uniformizer`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable`,
  `Mathlib.FieldTheory.Separable`; used through `IsGalois.to_isSeparable`.
- `def-weil-pbc-integral-closure`: `integralClosure` in
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `IsIntegral` in
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`, and
  `IsIntegrallyClosedIn` in
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`. The equivalent
  characteristic predicate is `IsIntegralClosure` in
  `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs`.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`; `Ideal.ResidueField` in
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` and `Ideal.Fiber` in
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber` were also read. The fibre
  ring is not needed in this statement.
- `def-weil-vector-space-dimension`: `Module.finrank`,
  `Mathlib.LinearAlgebra.Dimension.Finrank`.

Proof dependencies are imported without `public`, including the recorded
project modules `Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres`
(`AlgebraicGeometry.integralClosure_isDedekind_surjective_finite_fibres`)
and `Sheaf.RingTheory.DvrNormValuationSum`
(`IsDiscreteValuationRing.norm_valuation_sum`). The remaining imports supply
the DAG's Mathlib proof dependencies: PID Noetherianity/normality, DVR
dimension, finite normalization, fraction-field/normality of the closure,
maximal contraction, Dedekind localization, unit-times-uniformizer powers,
Galois prime conjugacy, and determinants. The docstring records each of the
eight proof steps and its named dependencies.

Edge cases: the identity extension gives `g=e=f=1`; totally ramified,
unramified and split examples respectively allow `e>1`, `f>1` and `g>1`.
The DVR class excludes fields, whose maximal ideal is zero. No henselian,
complete, perfect residue field, residue-separability, characteristic or
extra Noetherian hypothesis occurs. The prime fibre is explicitly nonempty.
Every choice of uniformizers is covered. Independent universes for `A,K,L,B`
allow arbitrary representations of the same extension and normalization.

Searches performed through `msearch.py Q117 lem-exc-dvr-galois-degree-data`:

- `leanfinder`: "For a finite Galois extension of the fraction field of a
  discrete valuation ring, its integral closure has transitive maximal
  ideals, DVR localizations and common positive ramification and residue
  degrees with field degree g e f". Eight related hits, including
  `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`,
  `Ideal.sum_ramification_inertia`, and
  `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`; none
  states this full normalization/localization/uniformizer theorem.
- `leansearch`: "The integral closure of a discrete valuation ring in a
  finite Galois extension has finitely many maximal ideals with common
  ramification and inertia degrees and field degree g times e times f".
  Eight related hits, including the same degree identities and
  `IsDedekindDomainDvr.isIntegrallyClosed`; no exact match.
- `loogle`: `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`.
  One hit. Its pinned signature assumes a finite flat invariant ring
  extension; the conclusion concerns only ideal indices, degrees and group
  cardinality. It does not give finite normalization, DVR localizations,
  local maps or uniformizer equations, so does not replace this item.
- `grep`, subdirectory `NumberTheory/RamificationInertia`:
  `ncard_primesOver_mul_ramificationIdxIn|ramificationIdx_eq_of_isGalois|inertiaDeg_eq_of_isGalois`.
  Eight hits in Galois and Hilbert theory, with the same limitation.
- `rg` of upstream `WeilConjectures/`, project `lean/Sheaf/`, and
  `dag/lean_names_upstream.json` for `dvr_galois_degree_data` and the item id:
  no existing declaration; one downstream proof docstring cites this item.
  Broader upstream `ramificationIdx|inertiaDeg` searches found related
  ramification comparison lemmas, not this full statement. Actual search
  responses are retained in the sandbox's `searches.jsonl`.

Repairs to the earlier attempt: quantify over every uniformizer pair; give
`B` its own universe `z`; import all recorded proof dependencies; replace
the abbreviated proof docstring by the eight-step source proof. The stale
second-reading text was removed because a second worker must review the
current module independently. No new node, dependency repair or natural
statement correction is required, and no statement dispute was found.

Validation uses only `scompile.py` for the single delivered file and
`deliver2.py --no-push` for the required server preflight. No delivery is
pushed by this worker.

## Second reading by Q117

I independently read the sandbox node and Lean module, the six statement
dependency records and their declaration sources, and Stacks
`more-algebra.tex`, Tag 09E8 (`remark-finite-separable-extension`), Tag 09EA
(`lemma-galois`), and Tag 09EB (`lemma-galois-conclusion`). These source
passages assume a DVR and a finite separable extension, with normality added
for the Galois conclusions; they impose no henselian, completeness,
residue-separability, characteristic, or additional finiteness hypothesis.
There is no repair note for this item. The node has no `statement_change`.

The following is my object/hypothesis/conclusion checklist, with its Lean
rendering and verdict for each item:

1. **DVR A.** `(A : Type u) [CommRing A] [IsDomain A]
   [IsDiscreteValuationRing A]` is exactly the recorded
   `def-sc-discrete-valuation-ring`. I read Basic.lean:58–60: this is a local
   principal ideal domain with nonzero maximal ideal, so fields are excluded
   exactly as in the node. **Pass.**
2. **Fraction field K and residue field k.** `(K : Type v) [Field K]
   [Algebra A K] [IsFractionRing A K]` specifies the fraction field with its
   inclusion. There is no free residue-field parameter: the canonical base
   residue field is the residue field of `IsLocalRing.maximalIdeal A`,
   equivalently `A / maximalIdeal A`. This is the k used by the inertia
   degree below. **Pass.**
3. **Finite normal separable L/K and G.** `(L : Type w) [Field L]
   [Algebra K L] [FiniteDimensional K L] [IsGalois K L]` gives exactly these
   hypotheses. I read `IsGalois` in Galois/Basic.lean:57, its separable and
   normal fields, `Normal.splits'` in Normal/Defs.lean:35, and
   `Algebra.IsSeparable` in Separable.lean:549. The splitting condition is
   the node's explicit meaning of normality. `Gal(L / K)` is the group of
   K-algebra automorphisms. `[Algebra A L] [IsScalarTower A K L]` expresses
   the compatible inclusion rather than a further restriction. **Pass.**
4. **Integral closure B.** `(B : Type z) [CommRing B] [IsDomain B]
   [Algebra A B] [Algebra B L] [IsScalarTower A B L]
   [IsIntegralClosure B A L]` permits any presentation of the integral
   closure. IsIntegralClosure/Defs.lean gives an injective inclusion in L
   whose image is exactly the integral elements; Algebra/Basic.lean:216
   defines `integralClosure` by that same carrier. Thus this uses the
   dependency's notion and adds no independent integrality, Noetherianity,
   or module-finiteness hypothesis. **Pass.**
5. **Finite nonempty set of maximal ideals X.** The first two conjuncts
   give finiteness and nonemptiness of `(maximalIdeal A).primesOver B`;
   the next conjunct `∀ q, q.IsMaximal ↔ q ∈ ...` identifies that set
   exactly with the node's X. I read `primesOver` and its prime/lying-over
   subtype instances in Ideal/Over.lean:376–385. This is an equivalent
   encoding of X, with no omitted maximal ideals. **Pass.**
6. **Canonical transitive G-action.** `MulAction.IsPretransitive
   (Gal(L / K)) {q : Ideal B // q ∈ ...}` states transitivity for the
   canonical action. In NumberTheory/RamificationInertia/Galois.lean:90–108
   its action is explicitly `Ideal.map (galRestrict A K L B σ) q`.
   It is not an arbitrary action supplied as an extra parameter. **Pass.**
7. **DVR localization and local map at every q.** The fifth conjunct
   quantifies over every q in X and states
   `IsDiscreteValuationRing (Localization.AtPrime q.1)` and
   `IsLocalHom (algebraMap A (Localization.AtPrime q.1))`. The recorded
   localization is used, with its prime instance supplied by membership
   in `primesOver`. No local-DVR or local-map assumption is added. **Pass.**
8. **Uniformizers, unit and positive exponents/degrees.** The next conjunct
   quantifies over every `πA`, q, and `tq`, with `Irreducible πA` and
   `Irreducible tq`, and supplies positive `e_q,f_q : ℕ`, a unit `u_q`,
   and exactly `algebraMap A _ πA = ↑u_q * tq ^ e_q`.
   Basic.lean:93 identifies irreducibility with generating the maximal
   ideal in a DVR. Quantifying over every choice matches the node's
   uniformizers; none is arbitrarily fixed or existentially chosen to
   make the statement weaker. **Pass.**
9. **Meaning and finiteness of e_q and f_q.** The same conjunct identifies
   them with `Ideal.ramificationIdx q.1 A` and `Ideal.inertiaDeg q.1 A`.
   I read the definitions in RingTheory/RamificationInertia/Ramification.lean
   and Inertia.lean. The first is the local quotient length, which in
   this DVR is the uniformizer exponent. The second is the residue-field
   dimension; `Ideal.inertiaDeg_eq_of_isMaximal` identifies it exactly
   with `Module.finrank (A / m_A) (B / q)`. Positive finrank over a field
   excludes infinite dimension, since finrank is zero in that case.
   The quotient and residue-field descriptions therefore agree with the
   node and with `def-weil-vector-space-dimension`. **Pass.**
10. **Common values and full degree formula.** The last conjunct supplies
    positive e,f, sets `g = X.ncard`, identifies both canonical invariants
    with these values for every q, and asserts
    `Module.finrank K L = g * e * f`. The previous uniformizer conjunct
    identifies every supplied exponent with this same e. Finiteness and
    nonemptiness of X already imply g is positive. This includes every
    clause of Tag 09EB and does not need an additional hypothesis. **Pass.**

Edge cases checked: the trivial extension has g=e=f=1; split, totally
ramified and unramified extensions permit g>1, e>1 and f>1, respectively.
The empty prime set is ruled out by a conclusion, not an assumption.
The zero ring, a field as A, a degree-zero field extension, and zero or
unit "uniformizers" are outside the node's hypotheses. No empty-scheme
or separate index-set parameter occurs. All characteristics and imperfect
residue fields remain allowed; in particular residue inseparability is
not excluded. The universes u,v,w,z are independently bound and no size
equality is imposed. All variables and universes in the signature are
explicitly bound.

Independent searches, using words other than the first worker's queries:

- `msearch.py ... leanfinder "Normalization of a discrete valuation ring
  in a finite Galois field extension: local uniformizer equations and
  equal residue field dimensions with the fundamental equality"` returned
  eight related results, including `Ideal.relNorm_eq_pow_of_isPrime_isGalois`,
  valuation uniformizers and `prod_galRestrict_eq_norm`. None is this
  combined statement.
- `msearch.py ... loogle "IsIntegralClosure, IsDiscreteValuationRing"`
  returned no results.
- `msearch.py ... leansearch "The maximal ideals of the integral closure
  of a DVR in a finite Galois extension are conjugate and have DVR
  localizations, uniformizer exponents and residue degrees satisfying
  the fundamental equality"` returned eight related conjugacy,
  maximality, and ramification/inertia results, but no exact statement.
  I checked the pinned source rather than relying on search signatures,
  some of which use older versions of the index definitions.
- Direct `rg` in Mathlib for `uniformizer|IsDiscreteValuationRing|
  eq_unit_mul_pow|ncard_primesOver_mul` in the Galois, finite-normalization
  and DVR modules found the separate normalization, factorization and
  degree results. Galois.lean:222 assumes a finite flat invariant-ring
  extension and gives only the product identity; it does not replace
  this full statement with its local DVR and uniformizer clauses.
- Direct `rg` in upstream `WeilConjectures/`, project `lean/Sheaf/`, and
  `dag/lean_names_upstream.json` for the item/name and both orders of
  `ramificationIdx`/`inertiaDeg` found no exact declaration. I also opened
  `RingTheory.dvr_galois_normalization_ramification_dvd` and
  `AlgebraicGeometry.Scheme.normalization_residue_degree_dvd_core`:
  both conclude divisibility only, so neither subsumes this item.

There are no new definition nodes or dependency modules in this delivery.
I also opened the two project proof dependency modules: the Dedekind/fibre
theorem and `IsDiscreteValuationRing.norm_valuation_sum`. They provide the
proof inputs cited in the eight-step docstring; all recorded proof
dependencies are imported. The docstring explains exponent uniqueness,
transport by conjugation, and evaluation of the norm at a base uniformizer.
The module has one theorem with proof `sorry`, no helper definitions,
private conventions or axioms, and no line exceeding 100 characters.

No mathematical mismatch or repair was needed in the current attempt.
The second reading changes only this report; the Lean and node are retained
verbatim. I checked programmatically that `lean.statement` equals the
complete signature before `:= by`, exactly. The prescribed `scompile.py`
compiled both the sandbox and library forms cleanly (1.7 seconds each),
with no errors or warnings.
