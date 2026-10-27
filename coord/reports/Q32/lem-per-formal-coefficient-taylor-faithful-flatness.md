## Worker report

The module `Sheaf.RingTheory.FormalCoefficientFlatness` states
`MvPowerSeries.map_flat_and_local_faithfullyFlat` and constructs its canonical local map
`MvPowerSeries.localCoefficientMap`. The theorem has only `sorry` as its proof. The helper
has real data: `IsLocalization.lift` of the coefficientwise map, using the existing
`IsLocalRing.notMem_maximalIdeal` equivalence to invert denominators. It neither assumes
nor chooses an unrelated homomorphism. Both declarations belong to this node's notion;
no new DAG node or dependency repair is needed.

Hypothesis and clause correspondence:

- Commutative rings A and B: `{A : Type u} {B : Type v} [CommRing A] [CommRing B]`.
  The universes are independent, so coefficient rings of different sizes are allowed.
- Both rings Noetherian: `[IsNoetherianRing A] [IsNoetherianRing B]`.
- The ring homomorphism and its flatness: `(ρ : A →+* B) (hρ : ρ.Flat)`.
- An arbitrary nonnegative number of variables: `(n : ℕ)`. The two rings are precisely
  `MvPowerSeries (Fin n) A` and `MvPowerSeries (Fin n) B`, Mathlib's families indexed by
  finite exponent vectors, with coefficientwise addition and Cauchy multiplication.
- The displayed coefficientwise homomorphism is exactly `MvPowerSeries.map ρ`.
  `MvPowerSeries.coeff_map` states that its coefficient at α is ρ applied to that
  coefficient of the input. No auxiliary algebra action is assumed.
- Flatness of this homomorphism is the first conjunct `(map (σ := Fin n) ρ).Flat`.
- The conditional nonzero-local case is `∀ [IsLocalRing B], ...`, inside the second
  conjunct, not a hypothesis on the first assertion. Mathlib's `IsLocalRing` extends
  `Nontrivial`, precisely incorporating the node's nonzero condition.
- The ideal n = (m_B,Z)T is represented by `IsLocalRing.maximalIdeal T`. The node's
  power-series-local-ring dependency gives the constant-coefficient description of this
  ideal. This is exactly `(maximalIdeal B).map C ⊔ Ideal.span (Set.range X)`: subtract
  the constant term from any series in it and group each remaining monomial by a variable
  divisor. Conversely variables have zero constant coefficient and constants in m_B
  have constant coefficient in m_B. Thus no extra ideal hypothesis or replacement
  localization is used.
- The inverse-image prime q is exactly
  `(IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) B)).comap (map ρ)`.
  Mathlib infers primality by inverse image of the maximal prime ideal.
- Its localization is `Localization.AtPrime q`. The helper maps this ring into the
  actual target series ring T. Its denominator proof is s.property, definitionally
  saying `map ρ s ∉ maximalIdeal T`, followed by the existing unit criterion. The lift
  sends F/G to the image of F times the inverse of the image of G and agrees with
  `map ρ` on R, by `IsLocalization.lift_eq` and `lift_mk'`.
- The map is local: the second conjunct includes `IsLocalHom (localCoefficientMap ρ n)`.
  Faithful flatness is `Module.FaithfullyFlat (Localization.AtPrime q) T`, with its
  module structure explicitly `(...).toAlgebra.toModule` from this very map. This uses
  the recorded module notion, not a bare `RingHom.FaithfullyFlat` predicate.
- For n = 0 nothing is excluded: `Fin 0` is empty. Mathlib's `MvPowerSeries.isEmptyEquiv`
  identifies the series rings with A and B, and `coeff_map` identifies the map with ρ.
  The maximal-ideal preimage and the localization therefore reduce to precisely the
  indicated localization of ρ. This is the meaning of the node's last sentence, rather
  than an additional assertion about a different arrow.

Recorded dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (and its ideal-finiteness
  interpretation `isNoetherianRing_iff_ideal_fg`).
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, the flat module for `ρ.toAlgebra`;
  `Mathlib.RingTheory.Flat.Basic`: `Module.Flat` and its injective-tensor criterion.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, `MvPowerSeries.map`,
  `MvPowerSeries.coeff_map`, `MvPowerSeries.C`, and `MvPowerSeries.X`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
  The canonical lift itself is `IsLocalization.lift` in `Localization.Defs`, exposed by
  this import; `IsLocalRing.notMem_maximalIdeal` is in `LocalRing.MaximalIdeal.Basic`.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`.

The proof imports also include all stated proof-dependency modules: Noetherianity and
empty-variable equivalences in `Mathlib.RingTheory.MvPowerSeries.Equiv`; the local
power-series ring instance in `Mathlib.RingTheory.MvPowerSeries.Inverse`; quotient-power
flatness `Module.Flat.flat_of_flat_quotients_powers` in the upstream
`WeilConjectures.RingTheory.Flat.FlatModulePowers`; maximal-localization detection
`Module.flat_of_isLocalized_maximal` in `Mathlib.RingTheory.Flat.Localization` (publicly
imported by that upstream module); flat local maps `RingHom.Flat.localRingHom` in
`Mathlib.RingTheory.RingHom.Flat`; local faithful flatness
`Module.FaithfullyFlat.of_flat_of_isLocalHom` in
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`; and tensor products from the flatness
imports. Proof-only imports are plain imports. The upstream FlatModulePowers module
was read in full, including its scalar-tower and quotient-module signature.

Sources read: `literature/stacks-project/algebra.tex`, labels
`lemma-flat-module-powers` (Tag 0523), `lemma-Noetherian-power-series` (0306),
`lemma-flat-localization` (00HT), and `lemma-local-flat-ff` (00HR). This theorem is the
node's coefficientwise specialization plus local corollary, not a claim that 0523
verbatim states it. The current blueprint ancestor `lem-per-artin-gabber-affine-curve`
and its proof in `literature/blueprint/latest/` were also read; this remains a supporting
commutative-algebra lemma, not the unit's own statement. The full five-step proof plan
is retained in the theorem docstring.

Edge cases checked before writing:

- n = 0: both empty-variable equivalences reduce the statement and the prime to the
  original coefficient map and its maximal-ideal preimage. The variable ideal is zero.
- B = 0: the first flatness assertion remains applicable (the zero module is flat);
  the second is conditional and has no `IsLocalRing B` instance. No global nonzero
  hypothesis was introduced.
- A = 0: a unital map forces B = 0, so the same first-clause check applies.
- Identity coefficient map: coefficientwise identity is flat; in the local case the
  source is the localization of T at its maximal ideal and canonically maps back to T.
- A coefficient localization A → A_s: it is allowed when B is Noetherian, and neither
  injectivity nor faithfulness is required before passage to the indicated local source.
- Distinct coefficient universes and all characteristics: neither is restricted.

Searches for an existing statement (all through prescribed tools or read-only searches):

1. `msearch.py ... leanfinder`: “A flat map between Noetherian rings induces a flat
   coefficientwise map on multivariate formal power series, faithfully flat after
   localization at the preimage of the local maximal ideal”. Eight hits included
   `Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing`, smooth-flat lemmas,
   local faithful flatness and localization flatness; no exact completed coefficient map.
2. `msearch.py ... loogle "MvPowerSeries.map, Module.Flat"`: zero hits.
3. `msearch.py ... grep "flat|Flat|FaithfullyFlat" RingTheory/MvPowerSeries`: zero hits.
4. `msearch.py ... leansearch`: “Flat coefficientwise extension on finite variable
   formal power series over Noetherian rings”. Eight hits gave maps, coefficients,
   Noetherianity and `MvPowerSeries.map.isLocalHom`, no coefficientwise flatness theorem.
5. `rg` in `lean/WeilConjectures/RingTheory`, `lean/Sheaf/RingTheory`, and
   `dag/lean_names_upstream.json` for MvPowerSeries, coefficient flatness and the intended
   names; `grep -rn` for the item id under `lean/WeilConjectures`: no exact theorem.
   Read `WeilConjectures/RingTheory/MvPowerSeriesFlat.lean`: its `constants_flat` only
   asserts flatness of B → B[[Z]], not flatness of A[[Z]] → B[[Z]]. Existing general
   quotient-power and local flatness interfaces are reused instead of restated.
6. Exact declaration-name searches found no `MvPowerSeries.localCoefficientMap` or
   `MvPowerSeries.map_flat_and_local_faithfullyFlat` in Mathlib, upstream, or Sheaf.
   An unrelated `localCoefficientMap` occurs in a different namespace for matrix
   coordinates and is not this ring localization.

No statement correction, new node, dependency module, or STATEMENT-DISPUTED issue.

## Second reading by Q32

A separate second pass by this worker compared the node's complete statement and
five-step proof with the finished module. No additional agent was started, as required
by the dispatch brief; independent maintainer review remains part of delivery.
The first conjunct has both Noetherian hypotheses and only flatness of ρ; the local
hypothesis is scoped solely to the second conjunct. The denominator proof forces the
specified maximal-ideal preimage. In particular, an arbitrary faithfully flat algebra
structure was not substituted for the canonical localized map: the module action is
written explicitly from `localCoefficientMap`. The target maximal ideal agrees with
(m_B,Z) by the unit/constant-coefficient criterion and variable-divisor grouping; n = 0
is retained, and B = 0 is retained in the first clause. The helper contains no `sorry`.
The one postponed theorem has the node's full proof plan and source in its docstring.
No hypothesis or conclusion mismatch was found in this second pass.

Validation: the first server compile found an unconstrained localization submonoid in the
helper. The helper now explicitly supplies `M := q.primeCompl`; this fixes elaboration
without changing either the construction or the theorem. The repeated server compile
and prescribed delivery preflight are recorded below when complete.

Final validation: `scompile.py Q32 lem-per-formal-coefficient-taylor-faithful-flatness`
compiled the delivered file both as a sandbox probe and under its actual module name,
with no errors or unexpected warnings. The 100-character line bound, exact verbatim
recorded signature, and lean-only node delta were also checked. The prescribed
`deliver2.py ... --no-push` printed `OK (dry run)` and confirmed that the preflight and
per-file compile passed; nothing was pushed by that dry run.
