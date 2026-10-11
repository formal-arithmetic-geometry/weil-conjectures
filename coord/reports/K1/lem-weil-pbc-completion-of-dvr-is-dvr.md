## Worker report

The module `Sheaf.RingTheory.CompletionOfDVR` states
`AdicCompletion.completion_dvr_of_nonzero_principal_maximalIdeal`, with `sorry` as its
entire proof. It uses the literal characterization in Stacks 00PD (4), rather than
introducing another definition of DVR. The node is unchanged except for `lean`.
No new nodes or dependency modules are needed, and no statement correction is needed.

The source is the forward direction of [Stacks Tag 0AP1](https://stacks.math.columbia.edu/tag/0AP1),
with the characterization [Tag 00PD (4)](https://stacks.math.columbia.edu/tag/00PD).
The named local literature files are absent on this machine, so both original source
pages were opened and read. They confirm the node's hypothesis and conclusion.
The declaration docstring carries all six proof steps and their named DAG dependencies.
No proof dependencies are imported merely for the postponed proof.

Clause-by-clause correspondence:

- The commutative ring `A` is `(A : Type u) [CommRing A]`, with explicit universe `u`.
- Noetherianity is `[IsNoetherianRing A]`.
- Locality is `[IsLocalRing A]`; the ideal `mathfrak m` is `IsLocalRing.maximalIdeal A`.
  It is the canonical unique maximal ideal, so no arbitrary ideal is substituted.
- Being a domain is `[IsDomain A]`, including nontriviality.
- A single nonzero generator is
  `hgen : ∃ π : A, π ≠ 0 ∧ IsLocalRing.maximalIdeal A = Ideal.span {π}`.
  The existential matches the node, which does not fix a chosen generator.
- The completion is exactly
  `let B := AdicCompletion (IsLocalRing.maximalIdeal A) A`.
  This is a local abbreviation in the proposition, not a new completion definition.
  Mathlib's compatible families have components `A ⧸ (m ^ n • ⊤)`; for `M = A`,
  `m ^ n • ⊤ = m ^ n`, hence this is the stated inverse limit of `A/m^n`.
  The inherited ring operations are componentwise.
- The conclusion's Noetherian local domain clauses are explicitly
  `IsNoetherianRing B ∧ IsLocalRing B ∧ IsDomain B`.
- Its single nonzero generator clause is
  `∃ π : B, π ≠ 0 ∧ IsLocalRing.maximalIdeal B = Ideal.span {π}`.
  The conclusion does not demand that a particular original generator be used.
  The locality instance needed to form `maximalIdeal B` is already available from Mathlib
  under the original Noetherian/local hypotheses; it is not an added hypothesis on `B`.
- “That is, again a discrete valuation ring” describes these four properties and adds
  no extra clause beyond the 00PD (4) characterization.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`, the abbreviation `IsNoetherian A A`, whose
  docstring says every ideal is finitely generated. The accompanying theorem
  `isNoetherianRing_iff_ideal_fg` confirms the equivalence literally.
- `def-weil-pbc-adic-completion`: `AdicCompletion` in
  `Mathlib.RingTheory.AdicCompletion.Basic`, with its full compatible-family signature
  and docstring read. Its ring instance in `Mathlib.RingTheory.AdicCompletion.Algebra`
  was also read. `Mathlib.RingTheory.AdicCompletion.LocalRing` is the sole import:
  it transitively supplies both recorded dependency modules, the completion ring
  structure, and the locality instance used to type the concluding maximal ideal.
  Its instance signature is
  `[IsNoetherianRing A] [IsLocalRing A] : IsLocalRing (AdicCompletion (maximalIdeal A) A)`.

Edge cases checked before writing:

- The zero ring is excluded exactly by the domain hypothesis, as in the node.
- A field is excluded: its zero maximal ideal cannot be spanned by a nonzero element.
  Thus the statement does not mistakenly include fields as DVRs.
- The generator cannot be zero or a unit: the former is explicitly excluded; a unit
  would generate the whole ring, whereas the maximal ideal of a local domain is proper.
- No hypothesis asserts the input is complete. Already-complete DVRs and incomplete
  DVRs are both covered. No residue characteristic, equal-characteristic assumption,
  finite residue field assumption, or dimension hypothesis is imposed.
- All universes and variables are explicitly bound. The inverse limit includes `n = 0`,
  whose quotient is zero and whose compatibility imposes no extra restriction.

Searches for an existing statement and name (2026-10-11):

- `msearch.py ... leanfinder` query “the maximal ideal adic completion of a discrete
  valuation ring is a discrete valuation ring”: eight results, including
  `instIsDiscreteValuationRingSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegers`
  and `IsDiscreteValuationRing.instIsHausdorffMaximalIdeal`. The former concerns a
  valuation subring in the completion of a fraction field, with Dedekind-domain and
  height-one-prime data; the latter asserts Hausdorffness. Neither is this statement.
- `msearch.py ... loogle 'AdicCompletion, IsDiscreteValuationRing'`: zero hits.
- `msearch.py ... grep
  'IsDomain.*AdicCompletion|IsDiscreteValuationRing.*AdicCompletion|completion.*is_dvr'
  RingTheory`: zero hits.
- `msearch.py ... leansearch` query “The completion of a discrete valuation ring at its
  maximal ideal is a discrete valuation ring”: service unavailable, Internal Server Error.
  This is recorded as unavailable; the other searches were completed.
- `rg` over Mathlib/RingTheory, source `WeilConjectures`, and project `lean/Sheaf` for
  `completion.*[Dd][Vv][Rr]|[Dd][Vv][Rr].*completion|IsDomain.*AdicCompletion|
  IsDiscreteValuationRing.*AdicCompletion|lem-weil-pbc-completion-of-dvr-is-dvr`:
  only the project docstring in `AnalyticallyUnramifiedPrincipalCriterion.lean` mentioning
  completed localizations as DVRs; no matching declaration.
- `rg` over `dag/lean_names_upstream.json` for `AdicCompletion|IsNoetherianRing`: no hits.
- Full proposed name `completion_dvr_of_nonzero_principal_maximalIdeal` searched in
  Mathlib, source `WeilConjectures`, project `lean/Sheaf`, and the upstream-name index:
  no hits before creating the module.

Validation: `scompile.py K1 lem-weil-pbc-completion-of-dvr-is-dvr` on the module succeeded
(exit 0, 1.5 seconds), with no errors or warnings. The final delivery dry run is recorded
below after completion. No `STATEMENT-DISPUTED` issue was found.

Delivery validation: `deliver2.py K1 lem-weil-pbc-completion-of-dvr-is-dvr --no-push`
printed `OK (dry run)`: the module compiles and passes preflight except for the second
reading, which the independent second reader writes. Nothing was pushed.

## Second reading by K1

Independent second reading on 2026-10-11, with the node, module and both dependency
nodes open. Verdict: the signature says exactly what the node says; no Lean or node
repair is needed. No new definition nodes, dependency modules or statement correction
are present or needed.

The node's objects, hypotheses and conclusions, matched individually:

1. A commutative ring A: `(A : Type u) [CommRing A]`. Exact, with arbitrary universe u.
2. Noetherian A: `[IsNoetherianRing A]`. Exact. I read the recorded dependency
   `def-weil-pbc-noetherian-ring` and Mathlib Noetherian/Defs.lean:196-205:
   `IsNoetherianRing` abbreviates `IsNoetherian A A`, equivalent to every ideal being
   finitely generated. No extra finiteness assumption is introduced.
3. Local A with its maximal ideal m: `[IsLocalRing A]` and
   `IsLocalRing.maximalIdeal A`. Exact: m is the unique maximal ideal, not extra data.
4. A is a domain: `[IsDomain A]`. Exact, including the source's nonzero-ring condition.
5. m has a single nonzero generator:
   `hgen : ∃ π : A, π ≠ 0 ∧ IsLocalRing.maximalIdeal A = Ideal.span {π}`.
   Exact existential, with the generator quantified after A and its structures.
6. The ring B is the m-adic inverse limit:
   `let B := AdicCompletion (IsLocalRing.maximalIdeal A) A`.
   Exact. I read `def-weil-pbc-adic-completion` and the actual declaration in
   Basic.lean:165-173, whose components are `A ⧸ (m ^ n • ⊤)` and whose compatibility
   uses `Submodule.factorPow`. For the self-module A, `m ^ n • ⊤ = m ^ n`.
   Algebra.lean:68-106 gives componentwise multiplication, one and the commutative-ring
   structure. This uses the recorded completion definition, not a private replacement.
7. B is Noetherian: `IsNoetherianRing B`, the first conjunct. Exact.
8. B is local: `IsLocalRing B`, the second conjunct. Exact. LocalRing.lean:90-91
   supplies the instance needed for the final maximal-ideal expression from just the
   existing Noetherian/local assumptions on A. This is not an additional binder or
   assumption on B, and does not depend on the domain conclusion.
9. B is a domain: `IsDomain B`, the third conjunct. Exact.
10. B's maximal ideal has one nonzero generator:
    `∃ π : B, π ≠ 0 ∧ IsLocalRing.maximalIdeal B = Ideal.span {π}`.
    Exact. The node does not require the output generator to be specified as the image
    of a chosen input generator. The concluding phrase "again a discrete valuation
    ring" is precisely the four asserted properties in Stacks 00PD (4).

Source verification: local Stacks .tex files are absent. Independently fetched and read
`more-algebra.tex` and `algebra.tex` from the official stacks/stacks-project repository,
including `section-permanence-completion`, `lemma-completion-dvr` and
`lemma-characterize-dvr` with their proofs. Also opened
[0AP1](https://stacks.math.columbia.edu/tag/0AP1) and
[00PD](https://stacks.math.columbia.edu/tag/00PD).
The section fixes completion at the maximal ideal and assumes a Noetherian local ring;
00PD (4) gives exactly the hypothesis and conclusion used here. The node selects the
forward implication of 0AP1, so no reverse implication is missing. No hypothesis from
section context is omitted.

Edge cases: the zero ring is excluded by IsDomain, exactly as in the source. Fields
cannot satisfy hgen because their maximal ideal is zero; a nonzero generator cannot
span zero. A unit generator cannot span a proper maximal ideal. Both complete and
incomplete DVRs are included. There is no characteristic, residue-field finiteness,
field-algebra or equicharacteristic restriction. The universe u is explicitly bound;
there is no hidden smaller-universe ring or unbound variable. The natural-number
index includes n = 0, whose quotient by the unit ideal is the zero ring and adds no
constraint to compatibility. Empty schemes and empty index families do not occur in
this node.

Independent searches, using different wording from the first worker:

- LeanFinder via msearch.py: "A local integral domain with nonzero principal maximal
  ideal remains a domain after ideal-adic completion". Eight hits: locality of complete
  rings and valuation subrings in completions of fraction fields, no matching statement.
- Loogle via msearch.py: `AdicCompletion, IsDomain`. Zero hits.
- LeanSearch via msearch.py: "Completion of a local principal ideal domain is a
  discrete valuation ring". Service unavailable (Internal Server Error); no verdict
  inferred from this unavailable service.
- rg across all Mathlib, source WeilConjectures, project lean/Sheaf and
  dag/lean_names_upstream.json for adic completion paired with IsDomain or
  discretevaluation, completion/principal/maximal, and the proposed declaration name.
  The only relevant hit is the IsDiscreteValuationRing instance in
  Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean:76. I opened it: its
  ring is `v.adicCompletionIntegers K`, the valuation subring of a completed fraction
  field at a height-one prime, not `AdicCompletion (maximalIdeal A) A`. It does not
  replace this statement. No duplicate theorem or project declaration found.

H5/H6/H8/H9 checks: the module contains no definitions, one theorem with only `sorry`
as proof, and one used Mathlib import. The header, namespace and source/blueprint
markers are correct. The docstring follows all six node proof steps and names their
DAG dependencies. The recorded lean.statement is verbatim the signature before `:=`.
No mismatch was found; changed only this report to record the independent reading.
