## Worker report

The module `Sheaf.RingTheory.GRingQuotientCompletedLocalComparison` states
`AdicCompletion.isRegular_completedLocalComparison_of_quotient_isGRing` with one
postponed proof (`sorry`). It also defines the canonical specialized map
`AdicCompletion.jacobsonCompletedLocalComparison`, using the existing
`RingHom.exists_adicCompletion_map_of_local`. No new mathematical notion or
postponed helper theorem is introduced.

Hypothesis and clause correspondence:

- Commutative Noetherian semilocal B: `(B : Type u) [CommRing B]
  [IsNoetherianRing B] [Finite (MaximalSpectrum B)]`. Finiteness of the maximal
  spectrum says exactly that there are finitely many maximal ideals.
- The intersection r of all maximal ideals: `Ideal.jacobson (⊥ : Ideal B)`.
  Mathlib defines this as the infimum of maximal ideals containing the zero ideal;
  every ideal contains the zero ideal.
- Ideal J contained in r: `(J : Ideal B) (hJ : J ≤ Ideal.jacobson (⊥ : Ideal B))`.
- The quotient is a G-ring: `(hG : IsGRing (B ⧸ J))`, using the recorded definition.
- The inverse-limit completion C: `AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B`.
- Every nonmaximal prime Q of C: `(Q : Ideal C) [Q.IsPrime] (hQ : ¬ Q.IsMaximal)`;
  C is expanded in the actual signature, with no local notation.
- Q contains JC: `(hJQ : J.map (algebraMap B C) ≤ Q)`.
- The contracted prime p: `Q.comap (algebraMap B C)` inside the helper.
- B_p and C_Q: `Localization.AtPrime` of the contracted prime and Q, respectively.
- U_p and T_Q: their `AdicCompletion` at the respective `IsLocalRing.maximalIdeal`.
- The induced local ring map B_p → C_Q: `Localization.localRingHom p Q
  (algebraMap B C) rfl`, whose fraction formula is Mathlib's
  `Localization.localRingHom_mk'`.
- The canonical map alpha: the helper chooses the witness of
  `RingHom.exists_adicCompletion_map_of_local` for this very local ring map.
  Its theorem specifies every quotient coordinate: if x_n = [a], then
  alpha(x)_n = [f(a)]. Every coordinate has a representative, so this determines
  alpha uniquely by extensionality of compatible sequences. Thus this is the
  canonical map, with no arbitrary comparison or extra assumption.
- Regularity: `(jacobsonCompletedLocalComparison B Q).IsRegular`.
- Locality: `IsLocalHom (jacobsonCompletedLocalComparison B Q)`.
- Faithful flatness: `(jacobsonCompletedLocalComparison B Q).FaithfullyFlat`.
- The absence of J-adic completeness or a G-ring hypothesis on B is literal:
  neither occurs among the binders. There is no restriction on characteristic.

The helper's target maximal ideal uses the explicit `.toCommSemiring` projection
of the canonical localization CommRing instance. This resolves Mathlib's opaque
Ore-localization addition diamond. `with_unfolding_all` in the definition body
checks the same canonical coordinate map against that type; it constructs no
proof by sorry, introduces no cast or alternative algebra, and changes no data.
Every variable and universe is bound explicitly (`set_option autoImplicit false`).

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `WeilConjectures.RingTheory.GRing`: `IsGRing`, `RingHom.IsRegular`,
  `Algebra.IsGeometricallyRegular` (read their full definitions).
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  its canonical ring/algebra structure and maps, `AdicCompletion.evalₐ`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  `Localization.localRingHom`, its fraction formula and local-hom instance.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`;
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`.
- `WeilConjectures.RingTheory.CompletionMapForLocalHom`:
  `RingHom.exists_adicCompletion_map_of_local`, including its full coordinate
  specification and constructive proof. The corresponding already landed node
  `lem-weil-pbc-fs-adic-completion-map-local` is added to stmt_deps.

Every recorded proof dependency's available module is imported plainly, including
Mathlib leaves via their recorded files. In particular the proof uses
`AdicCompletion.isNoetherianRing`, `AdicCompletion.isRegular_of_isGRing`,
`RingHom.isRegular_iff_localRingHom_prime_and_maximal`,
`Algebra.formallySmoothAdic_of_isGeometricallyRegular`,
`RingHom.formallySmoothAdic_of_flat_closedFiber`,
`Algebra.exists_formallySmoothAdic_completeSourceTarget`, and
`RingHom.isRegular_of_formallySmoothAdic`. The module docstring carries the node's
six proof steps, including the canonical quotient/tensor ring identification,
the identical closed fibre, complete-source and complete-target hypotheses,
and the final faithful-flatness implication. No proof imports were omitted.

Edge cases checked before and after writing: the zero ring has no prime Q,
so no artificial Nontrivial hypothesis is imposed; fields and Artinian semilocal
rings have no nonmaximal Q, so the result is vacuous there. J = 0 retains exactly
the G-ring hypothesis on B; J = r is permitted. For an already r-complete B the
comparison is the canonical completed localization map. The nonmaximal condition
is retained even though the argument may also cover maximal primes. Completion
coordinates include n = 0 (the zero quotient); no positive-degree truncation is
silently assumed. All rings and their localizations/completions remain in the
arbitrary explicitly bound universe u, and no smaller universe of test objects
is introduced.

Searches (2026-10-24):

- `msearch.py ... leanfinder "The completed local comparison from a semilocal
  Noetherian ring to its completion is regular above a G-ring quotient"`:
  8 hits on regular sequences, henselian rings, localization and semilocal
  Noetherian descent; none states this theorem.
- `msearch.py ... leansearch "regular map between completions of localizations
  of a Noetherian semilocal ring above a G-ring quotient"`: 8 hits, including
  localization maps and topological completion functoriality; none states this
  adic regularity theorem.
- `msearch.py ... loogle "AdicCompletion, RingHom.IsRegular"`: 0 hits;
  RingHom.IsRegular is not a Mathlib identifier (it is supplied by the project).
- `msearch.py ... grep "mapRingHom|map.*ompletion|IsSemilocal"
  RingTheory/AdicCompletion`: 25 hits on evaluation, completion tensor maps,
  inverse-limit lifting and exactness, with no theorem match.
- Direct `rg` in Mathlib for semilocal identifies `[Finite (MaximalSpectrum B)]`
  as the established representation; Jacobson/Ideal.lean defines the radical
  as the infimum of maximal ideals above the input ideal.
- Direct `rg` in WeilConjectures/RingTheory and Sheaf/RingTheory for completed
  comparisons and completion maps found CompletionMapForLocalHom, the required
  existing coordinatewise map theorem. Its node and full source were read.
  `AlgebraicGeometry.localMapCompletionMap` is a same-universe general chosen
  local-completion map in the trace-formula approximation module, also read;
  the present specialized helper applies its underlying recorded map theorem
  directly, without importing the unrelated geometric approximation theorem.
- `rg` for this node id and the new declaration names in WeilConjectures and
  Sheaf found no existing statement. The old upstream CompactObject example is
  withdrawn; its node now points at WeilConjectures.CategoryTheory.CompactObject,
  whose full current header and declaration were read.

Source checks: read the node and its full accepted six-step proof; read local
Stacks more-algebra.tex at lemma-formally-smooth-completion (07ED) and
proposition-fs-regular (07PM), confirming the source/target completion and
complete-local regularity hypotheses. The inherited Rotthaus PDF URL was tried
with the web reader but that endpoint was inaccessible; no claim is made to
have inspected that PDF. The node's accepted proof_origin explicitly assembles
the statement from the Stacks results rather than the inherited attribution.
No statement correction, disputed statement, or unusable dependency was found.

Validation: server scompile.py on the delivered module in module mode; the final
result and the delivery dry-run result are recorded below.

## Second reading by Q65

I performed a separate final clause-by-clause rereading of the node and generated
module, as the single worker explicitly forbidden to start other agents. This is
not represented as another person's independent review; the maintainer performs
that independent review on delivery. The hypotheses B, J, B/J, Q, JC and
nonmaximality and all three conclusions match as enumerated above. I rechecked
that the completed map uses the localizations' maximal ideals and the original
B → C map, and that the coordinatewise existence theorem uniquely determines
its data. No additional G-ring, completeness, locality or Noetherian hypothesis
is imposed. The only change found during the compile pass was an explicit ring
instance projection to resolve elaboration and a line wrap; no mathematical
statement changed. The sole theorem proof is sorry, and the helper has real data.

Final scompile.py: clean in sandbox (2.5 s) and library module (2.6 s), no warnings.
