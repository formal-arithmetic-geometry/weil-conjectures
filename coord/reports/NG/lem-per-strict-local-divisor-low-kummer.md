# Stage-1 delivery: lem-per-strict-local-divisor-low-kummer

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-strict-local-divisor-low-kummer.json`: statement, split; not a Mathlib leaf. Eight proof steps, with all original statement hypotheses and clauses retained.
- `citations.json`: a verbatim statement quote for every node cited by every proof step.
- `report.md`: this report. `searches.jsonl` contains the five actual search-command results; `write_split.py` is sandbox-only preparation material.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this auxiliary item is not its unit's key statement.

## Attachments

No complete attachment for the item was found. I searched the slopmaster2 project under `WeilConjectures/` for the exact blueprint id, strict-local/divisor/Kummer names and concepts, and the upstream Lean-name inventory. The affine-line Kummer declarations concern the line over a field, not this arbitrary regular local ring and its principal open; the abstract `HasKummerClass` interfaces do not compute these cohomology groups. The existing closed node `lem-sc-regular-local-domain` already owns `IsRegularLocalRing.isDomain`; it is reused without creating an attachment or a duplicate. No master sorry declaration is treated as a proof.

## WANTED

None. All external sources used are available in the shared repository.

## Findings and corrections

The item was statement-only and its statement is correct. I retained its statement, statement dependencies, blueprint ancestry, source, creation metadata and all inherited Mathlib searches. The proof is marked agent-origin because it reconstructs the omitted low-degree calculation from permitted sources rather than copying a complete proof from ILO. I read ILO XVI Proposition 3.4.2 on printed p.245 (PDF page 251): its criterion explicitly rests on degrees 0 and 1, but refers elsewhere for their calculation. I use Stacks' ordinary Kummer/Picard/root-lifting route for that calculation, without importing the excluded reference.

Two easy overstatements are avoided. The existing `lem-sc-h1-gm-pic` is only for curves; I use `thm-sc-hilbert-90`, whose statement explicitly says any scheme. The regular-local Picard lemma is about rank-one projective modules over a localization, so Step 6 explicitly establishes that a scheme line bundle has such a module of sections before using it. In particular, `R[1/t]` need not be local or semilocal.

The existing UFD boundary-factorization node has parameters among a full regular system. It is unnecessary here: regularity of `R/(t)` makes `(t)` prime, and induction on `N` in `xy=t^N` gives the needed unit normal form. This is a short elementary argument in the item, not a new factorization node. The coefficient trivialization and the specified Kummer generator are likewise clauses of the item and are proved in its steps, not repackaged as children.

## Unfinished work

None for this stage-1 split. No Lean was written or compiled. No compiler, Lake, local DAG checker, live-project write or manual git command was run.

## Not duplicates

No new nodes were created. Whole-DAG searches for Kummer, roots of unity, Picard/H1, factoriality, local root lifting, affine quasi-coherent equivalence, finite projectivity and long exact cohomology identified the reused nodes. Blueprint searches for `Kummer`, `factorial`, `roots of unity`, `divisor complement`, `strictly henselian regular` and `0AFZ` found no node stating this complete low-degree strict-local divisor-complement calculation. Existing statements were opened, not inferred from titles or their proofs.

## Mathlib searches

The five searches in the sandbox log were run with the required `msearch.py NG lem-per-strict-local-divisor-low-kummer` command and read. They comprise grep `kummer|etaleCohomology|regularDivisor`, Loogle `"Kummer"`, LeanFinder with the first-etale-cohomology formulation, a second LeanFinder phrasing in terms of units modulo powers and the Kummer sequence, and LeanSearch with the strict-local divisor-complement phrasing. All services responded. Hits are Kummer extensions and Kummer-Dedekind factorization, cotangent H1, etale ring maps and Dedekind Selmer groups. They do not state this small-etale H0/H1 computation or specialize to it in one line; even the Selmer-unit map lacks the cohomological and Picard comparisons. Original item searches from its creation are preserved separately and not presented as new runs.

## Review by NG

I read the chapter and unit records, the three-level contract, the current blueprint ancestor, ILO XVI Proposition 3.4.2 and the Stacks passages used below. This is a low-degree input beneath the recorded historical divisor-purity branch of `lem-per-artin-gabber-affine-curve`; it changes neither the chapter nor the unit route. The contemporary blueprint ancestor has no full proof of this input, so its ancestry is preserved as historical provenance rather than claimed as a source for an argument it does not contain.

For Step 1 I read Stacks 00NP, `algebra.tex` lemma-regular-domain, and the full statement of `lem-sc-regular-local-domain`. It applies both to R and to R/(t), since the latter is a proper local quotient and is regular by hypothesis. The node says domain, exactly what I use. Properness of (t), nonzero t and injectivity into B follow from the explicit hypotheses and fraction arithmetic. The zero prime in every nonempty basic open proves connectedness directly; no dimension-one or excellence hypothesis has entered.

Step 2 uses only the primality and domain conclusions of Step 1 and fraction arithmetic. I checked the base N=0 and both possible prime-divisibility branches of the induction. After each cancellation the power is N-1. Uniqueness uses that t is a nonunit; it holds for negative as well as nonnegative exponents after cancelling powers in B. This proves the full product description, rather than just describing elements of R that become units. No general factorization theorem is hidden here.

For Step 3 I read the statement of `lem-weil-pbc-henselian-local-root-lifting` and Stacks 04GF/04GG in `algebra.tex` (the defining root-lifting property and its characterizations). Our original definition is the finite-algebra idempotent definition, so the equivalence in the cited node is necessary. The monic polynomial X^ell-u has a simple root in the separably closed residue field: its nonzero constant term rules out zero roots and its derivative is ell X^(ell-1). Invertibility of ell is used here. The lifted root is a unit by the displayed inverse. Thus it proves divisibility of R-units, without erroneously claiming the same for all B-units.

For Step 4 I read the whole statement of `lem-sbc-strict-local-roots-of-unity`: it gives both cyclicity/cardinality and that every nonidentity root minus one is a unit. It applies since ell>0 and is invertible in the strictly henselian R. Those two conclusions give a primitive root and pairwise unit differences. I wrote out monic division and the disjoint-open local description of roots on an arbitrary etale test scheme, so the sheaf isomorphism does not rest merely on the count of R-valued roots. `def-asd-etale-roots-of-unity` gives exactly those test-scheme sections. `lem-weil-pbc-constant-sheaf-sections-locally-constant`, read against Stacks 03P5 (`etale-cohomology.tex`, remark-constant-locally-constant-maps), identifies the locally constant exponents with the constant sheaf on every test scheme. The construction preserves multiplication/exponentiation and restricts to V. No descent or stalk-comparison theorem is silently assumed.

For Step 5 the same 03P5 statement and the definition of etale cohomology identify degree-zero constant sections. The degree-zero resolution cohomology is the original sections because kernels of sheaf maps and the global-section kernel are computed sectionwise. A connected nonempty scheme has only constant locally constant maps, by open-and-closed fibres. Step 4 identifies both restriction maps with that map on A, so both degree-zero clauses are proved with their stated maps.

For Step 6 I read Stacks 0AFZ, `more-algebra.tex` lemma-regular-local-Pic-zero, together with Schemes 01HV/01IA and Algebra 00NX/00E8. I opened every cited node: `def-sc-invertible-module` says quasi-coherent and rank-one locally free; `lem-weil-pbc-affine-tilde-gamma-adjunction` gives reconstruction from sections; `lem-weil-pbc-affine-scheme-qcqs` gives compactness of V; `lem-weil-pbc-spec-module-tilde-sections` gives P_f as the sections on D(f); `lem-sc-affine-standard-cover-finite-projective` takes a finite unit-ideal basic cover with finite free localizations; `lem-trf-regular-local-pic-zero` then takes a finite projective module with rank-one localizations at every prime. The finite subcover and further-localization argument verify all of those hypotheses. Its conclusion P=B gives a trivial sheaf by the affine equivalence and `lem-weil-pbc-spec-tilde-free-module`, explicitly at rank one. This checks the algebraic/scheme Picard comparison that otherwise would be a missing step.

For Step 7 I read Stacks 03P8, `etale-cohomology.tex` theorem-picard-group, and 03PL, lemma-kummer-sequence, including the displayed long exact sequence after it. `thm-sc-hilbert-90` has the arbitrary-scheme hypothesis needed here, unlike the curve-only variant. `lem-amb-kummer-any-base` states the exact Kummer sequence for any scheme where the exponent is invertible. Clause 2 of `lem-weil-pbc-pullback-cohomology-long-exact-ladder` states the long exact sequence for a short exact sequence of abelian etale sheaves; I apply it to id_V, so there is no unverified base-change hypothesis. The zero Picard group yields H1(G_m)=0, and exactness identifies the quotient of B-units by ell-th powers with H1(mu_ell) through the actual connecting map, not just an unspecified group isomorphism.

Step 8 computes this quotient explicitly using Steps 2 and 3. The exponent of t modulo ell is well defined and surjective, and its kernel is exactly ell-th powers because R-units are ell-divisible. Under its inverse the class 1 goes to [t], so the connecting map gives precisely kappa(t), with no sign or normalization ambiguity. The resulting additive map is F_ell-linear since both groups are killed by ell.

I tested the edge cases: dimension zero cannot satisfy nonzero nonunit t; dimension one gives the usual strictly henselian DVR fraction-field calculation; in higher dimension B may have many maximal ideals, but the proof uses only the localized regular-local Picard theorem. ell=2 is valid because 2 is invertible; then -1-1 is a unit as needed. Imperfect separably closed residue fields cause no problem because the polynomials used are separable. If the quotient-regular assumption were removed, t=xy in a regular two-dimensional local ring would produce two independent exponents, explaining the essential primality hypothesis. No new statement requires a separate small-case test.

I checked delivery-errors B1-B10, C1-C8, D1-D5 and E1-E7 against the actual files. There are no new nodes to carry hollow definitions, duplicate tags, missing searches or a restated item clause. All proof dependencies equal the union of uses, all quotes are literal substrings of the relevant statements, and a dependency traversal found no route back to this item. Generic results from other units are declared individually in `split_report.tool_uses`; they supply algebra or sheaf tools, not alternate unit proof routes. No proof step exceeds 2000 characters. The source is not claimed to contain the reconstructed proof; agent origin is explicit. No statement dispute was found.

## Validation

The resumed session started with the required server dry run; it exited successfully with `OK (not pushed)` at `00a0312258`. I compared the sandbox with the current shared item: its statement, statement dependencies, source and blueprint ancestry are unchanged, and the current item remains unsplit. I reread the current chapter/unit records, the current blueprint ancestor, ILO XVI Proposition 3.4.2 (printed p.245), Stacks 00NP, 04GF/04GG, 00NX, 01HV/01I7/01IA, 0AFZ, 03P5, 03P8 and 03PL, and every cited node statement. The affine-line cohomology declarations at `WeilConjectures/EtaleCohomology/Purity/Smooth/AffineLine.lean:119` and `:129` contain `sorry` and concern a different geometric setting; they are not attachments. The abstract Kummer-class interface supplies no cohomology computation.

All 18 citation entries remain verbatim substrings of the current cited statements and cover every proof use. The longest proof step is 1291 characters, so there is no long step requiring extraction. The small-case and hypothesis review above still applies. No mathematical repair or new search was needed; the prior proof, citations and search log have been retained. A final server dry run follows this validation update before direct delivery.
