## Worker report

The module states that for a Noetherian commutative ring `R`, a finite module `M`, and `f : R`, there are maximal nowhere-dense-support submodules `K` and `Kf` (the latter over the localized ring) and a linear equivalence between the localization of `M ⧸ K` and the quotient of the localized module by `Kf`. The binders render the Noetherian-ring and finite-module hypotheses, and the two `Maximal` clauses render the two quotient constructions. `LocalizedModule (Submonoid.powers f) M` is the formal `M_f`, and `M ⧸ K` and its localized module render `(M')_f`; the final `Nonempty` linear equivalence renders the canonical isomorphism.

The statement uses `Module.exists_maximal_nowhereDense_support_quotient` from `Sheaf.RingTheory.RemoveEmbeddedPrimes`, which supplies each maximal quotient. The proof is `sorry` as required for stage 2. Edge cases checked include `f = 0` (the localized module can be zero), `f = 1` (localization is unchanged), `M = 0`, and an empty support; the existential formulation does not exclude any of these.

Searches for an existing declaration: `msearch.py ... leanfinder "localization quotient remove embedded primes finite module"` found no theorem with this conclusion; `msearch.py ... loogle "Module localization associatedPrimes quotient"` found no hits; grep of Mathlib `associatedPrimes.*localiz|localiz.*associatedPrimes` found no quotient-removal theorem; `rg` over `WeilConjectures` found no matching declaration; `rg` over `lean/Sheaf` found only the affine-removal dependency.

The original node statement was corrected because it referred to informal objects `M'` and `(M_f)'` without introducing the submodules or the localized module types. The correction follows Stacks Tag 02M7 and names the two maximal submodules explicitly.

## Earlier second reading (a previous round; superseded)

The node and module were read together. The Noetherian and finite-module hypotheses correspond exactly to the node. `K` and `Kf` are explicitly introduced, each maximality clause expresses nowhere-dense support in the relevant support, and the final linear equivalence is the stated localization/quotient isomorphism. No additional mathematical hypothesis is present.

## Earlier proposed statement correction (withdrawn by second reading)

The old statement used undeclared informal quotient objects. It was corrected to the self-contained existential statement above, following Stacks Project Tag 02M7. Citer `lem-sc-hilbert-embedded-points` still holds because it uses the affine-removal quotient and its localization compatibility.


## Second reading by E1

I independently read the base node, the sandbox node and Lean module, each of the
three statement dependency nodes, and the actual dependency signatures. The local
Stacks .tex tree is absent on this machine. I read the source .tex directly from
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex at
`lemma-remove-embedded-primes-localize` (02M7), together with
`lemma-remove-embedded-primes` (02M6). The tag pages confirm these labels:
https://stacks.math.columbia.edu/tag/02M7 and
https://stacks.math.columbia.edu/tag/02M6. Lemma numbering has changed, but the
labels and hypotheses match. The source assumes a Noetherian commutative ring
and a finite module and allows every element f; no field, nonzero element,
characteristic, or nontriviality hypothesis occurs.

Object/hypothesis/conclusion checklist, against the restored ORIGINAL node:

- R, a Noetherian commutative ring: `(R : Type u) [CommRing R]
  [IsNoetherianRing R]`. Exact. Opened `def-weil-pbc-noetherian-ring` and
  Mathlib's `IsNoetherianRing` in `RingTheory/Noetherian/Defs.lean`, which is
  `IsNoetherian R R` and means every ideal is finitely generated.
- M, a finite R-module: `(M : Type v) [AddCommGroup M] [Module R M]
  [Module.Finite R M]`. Exact. Opened `def-weil-finitely-generated-module`
  and `Module.Finite` in `RingTheory/Finiteness/Defs.lean`: its field is
  finite generation of the top submodule, not finiteness of the underlying set.
- Any element f: `(f : R)`, with no restriction. Exact.
- The supplied quotient M to M': `K : Submodule R M`, `hK : Maximal ... K`,
  and `M ⧸ K` with the actual quotient map `K.mkQ`. Exact. The predicate
  is `IsNowhereDense {p : Module.support R M | p.val ∈ Module.support R L}`.
  The ambient type is the support subspace, not the whole prime spectrum.
  `Module.support` in Mathlib `RingTheory/Support.lean` is defined by
  nonzero localization at primes; `IsNowhereDense` is empty interior of closure.
  These are the exact predicates of the opened dependency module
  `Sheaf.RingTheory.RemoveEmbeddedPrimes`, declaration
  `Module.exists_maximal_nowhereDense_support_quotient`. Its signature has the
  same independent universes and ring/module hypotheses; it supplies K and
  also proves the support and associated-prime properties of its quotient.
- The corresponding localized quotient: `Kf : Submodule
  (Localization (Submonoid.powers f)) (LocalizedModule (Submonoid.powers f) M)`
  and `hKf : Maximal ... Kf`, with the same predicate evaluated in the support
  of the localized module over the localized ring. Exact. No additional
  Noetherian or finite instance is assumed: localization preserves those
  properties, so the same dependency applies. The quotient is literally
  `(LocalizedModule (Submonoid.powers f) M) ⧸ Kf` and its map is `Kf.mkQ`.
- Conclusion `(M')_f` is canonically identified with `(M_f)'`:
  `∃ e : LocalizedModule (Submonoid.powers f) (M ⧸ K) ≃ₗ[
  Localization (Submonoid.powers f)] ((LocalizedModule ... M) ⧸ Kf), ...`.
  Exact scalar ring, source, and target. The added equation for every m says
  that e sends the localization of `K.mkQ m` to the quotient of the
  localization of m. This specifies the canonical map: quotient classes
  followed by fractions generate the localized source, so linearity makes
  this compatibility determine e. The opened Mathlib `mkLinearMap` is the
  canonical map to the localized module, not an arbitrary identification.
- Quantifier order: arbitrary R, M, f and their two specified quotients,
  then an equivalence respecting the maps. Exact rendering of the source's
  'where ... are the quotients constructed'. Maximal submodules here are
  unique: the sum of two nowhere-dense-support submodules has support in
  the union of their supports and again qualifies. Thus arbitrary maximal
  K and Kf give precisely the quotients in 02M6, with no stronger assumption.

Edge cases: independent universes u and v allow arbitrary sizes; no universe
restriction to a field or common universe. The zero ring and zero module are
allowed, as are empty support and no minimal primes. For f = 0 or nilpotent f,
the localized module and both quotient sides vanish and the compatibility
condition is valid. For f = 1 or a unit, localization gives the original
quotient. Empty schemes, n = 0, and an external index set are not objects of
this affine module statement; the empty-support case covers the relevant
empty geometry. There is no characteristic restriction.

Independent searches (2026-10-11):

- LeanSearch via msearch: 'Localization of a finite module commutes with
  quotienting by its maximal submodule with nowhere dense support'. Service
  returned Internal Server Error; recorded unavailable, no verdict inferred.
- LeanFinder via msearch: 'largest submodule support avoids minimal primes
  localization quotient'. Eight hits: Module.support, its membership lemmas,
  support_quotient and support_quotSMulTop, and localized-module vanishing
  criteria. Opened support's definition; none states removal compatibility.
- Loogle via msearch: 'LocalizedModule, Submodule.mkQ'. Zero hits.
- rg with 'embedded|nowhereDense|nowhere.dense' in Mathlib/RingTheory,
  WeilConjectures/RingTheory, and lean/Sheaf/RingTheory found only the
  already-used removal dependency (other embedded hits are unrelated ring
  embeddings). The support and localization APIs are reused, not redefined.
  A full-name rg in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found no existing declaration of the proposed
  theorem name. No duplicate theorem or notion was found.

Mismatches and repairs:

1. The worker's `Nonempty` equivalence omitted compatibility with the quotient
   maps, so it did not express the source's canonical localization identity.
   Replaced it with an explicit existential equivalence and its equation on
   all images of M. Changed existentially selected K/Kf into binders with
   maximality hypotheses, matching the source's already specified quotients.
2. The proposed node correction was unnecessary: the original statement
   explicitly introduces M' and (M_f)' as supplied quotients, exactly as the
   source does. Restored the base statement verbatim and removed the sandbox
   statement_change record. No unit or node statement is changed by delivery.
   Checked all direct citers: the only one is
   `lem-sc-hilbert-embedded-points`; its affine restriction/gluing step still
   holds and specifically benefits from the canonical map compatibility.
   There is no second direct citer to read. The earlier correction discussion
   above is historical and superseded by this section.
3. Removed the unused direct spectrum-module import. Expanded the theorem
   docstring to include all three actual node proof steps: exactness, the
   minimal-prime kernel characterization and vanished factors, then applying
   affine removal over R_f and identifying the quotient maps.

No new definition nodes or dependency modules are needed. No data definition,
private copy, or hollow definition was introduced. The one theorem remains
`by sorry`; nothing was proved. All declarations have source/blueprint
citations, all variables and universes are bound, and lines are at most 100
characters. The node's lean.statement is copied verbatim from the new
signature. The repaired file compiled cleanly on the server with scompile
(exit 0, 1.7 seconds, no warnings).
