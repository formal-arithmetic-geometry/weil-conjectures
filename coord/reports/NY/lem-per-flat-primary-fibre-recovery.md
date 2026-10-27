# Worker report: lem-per-flat-primary-fibre-recovery

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-flat-primary-fibre-recovery.json`: statement, split into five proof steps; no Mathlib match.
- `citations.json`: one entry for each cited node in each proof step, with verbatim statement quotations.
- `report.md`: this report. The search command also wrote `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. The live item was unsplit and the sandbox initially contained no node, report or prior split. Its imported searches and all other existing fields were preserved; searches actually run for this worker were appended.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and id, for primary-ideal/flat-extension notions, and for `IsPrimary`. The only relevant primary localization/recovery results found are Mathlib localization statements or project primary-component results with different hypotheses/conclusions. No project declaration states the full item. Existing project declarations of the tools are not claimed as attachments for this item.

## WANTED

None. All sources used are available in `literature/stacks-project/algebra.tex`.

## Findings and corrections

The item's statement is correct and is unchanged. No STATEMENT-DISPUTED issue was found. The source's Bourbaki argument supplies the useful idea that flatness preserves a multiplication injection; the full associated-prime base-change equality is unnecessary for this special primary quotient. I wrote that specialization explicitly instead of creating a new lemma restating the item or a primary-quotient clause.

The proof takes generic commutative-algebra tools from the existing DAG, with their off-unit uses declared in `split_report.tool_uses`. It does not change the perverse unit's route. The blueprint place is the existing formal ideal-descent chain below Step 3 of `lem-per-artin-gabber-affine-curve`; I read that node's proof in `literature/blueprint/latest/`, not an older snapshot.

Searched the whole DAG for Tags 0311 and 0312, `associated primes`, `associatedPrimes`, and primary/flat recovery; read the statements of the existing flat base-change and quotient-associated-prime nodes as well as the tools actually used. `tools/blueprint_refs.py ancestor` confirms the inherited ancestor; blueprint searches for `primary`, `primary ideal`, 0311 and 0312 supply no duplicate of this item. In particular, the general associated-prime formula and the injection into associated-prime localizations already exist, so no nodes were created for them.

The recorded Mathlib searches were run through msearch, using LeanFinder twice with different formulations, LeanSearch, Loogle, and grep. Read the hits and source: `IsLocalization.under_map_of_isPrimary_disjoint` (`Localization/Ideal.lean:126`, deprecated alias `comap_map_of_isPrimary_disjoint` at 145) recovers an already primary ideal under a localization; our extended ideal need not be primary. `IsLocalization.AtPrime.under_map_eq_map` (`Localization/AtPrime/Basic.lean:642`, alias `comap_map_eq_map` at 670) concerns a particular localization tower, not arbitrary flat primary extension. `Lasker.lean:201` concerns a selected part of a primary decomposition. Flat going down, faithful-flat lying over and faithful-flat contraction likewise do not give this statement by one-line specialization. No unavailable service was recorded as a negative match.

## Not duplicates

No new nodes; there are no new/existing same-tag pairs to justify.

## Review by NY

I read Tags 0312 (`lemma-bourbaki`, lines 15774–15851) and 0311 (`lemma-zero-at-ass-zero`, lines 15496–15515) in algebra.tex, including their proofs. I also read Tag 00HD (`lemma-flat`, from line 8708), Tag 00HB (`definition-flat`, from 8621), and Tag 00DF (`lemma-tensor-product-exact`, from 1994), and the two localization definitions cited below. There are no new-node sources to check.

Step 1 expands primaryness directly. With a outside the radical and b nonzero modulo q, ab in q would force a power of a into q. This proves injectivity on the entire R/q, including zero divisors elsewhere; it uses no unquoted theorem.

Step 2 cites `lem-weil-pbc-flat-tensor-exact`: its statement expressly preserves an initial injection after tensoring with a flat module. Here S is flat over R by the item's hypothesis. It also cites clause (1) of `lem-weil-pbc-tensor-over-quotient-ring`, which expressly identifies (R/q) tensor S with S/qS by the displayed formula. Only its R-linear form is needed; on pure tensor generators that formula intertwines multiplication by a with multiplication by f(a). Thus no uncited S-linear comparison or derived identification is assumed.

Step 3 uses the exact-annihilator definition of an associated prime, introduced in the proof step. The witness is nonzero because a prime ideal is proper. qS kills the quotient, so the contraction contains q and hence its radical, since the contraction is prime. The reverse inclusion follows from Step 2 acting on this nonzero witness. This proves exactly that all associated primes lie in the whole radical fibre; it never restricts to minimal primes or assumes the fibre reduced. It needs no assertion that the fibre is nonempty.

Step 4 cites `def-weil-pbc-localization-at-prime`, whose statement includes the fraction equality relation u(rs'-r's)=0. I expanded localization ideal membership into a finite sum and a common denominator, then used that exact relation to produce s outside Q with sx in qS. Multiplicative closure of the complement follows from primality. This avoids silently identifying a localized quotient or applying an uncited localization-exactness theorem.

Step 5 cites `lem-weil-pbc-module-injects-localizations-associated-primes`. Its statement's equivalent criterion is exactly: for every associated prime there is an element outside it killing the chosen module element, then that element is zero. Apply it with base ring S and module S/qS; S is Noetherian by the item's hypothesis. Step 4 supplies every required annihilator. The same stated criterion includes the empty associated-prime set and so verifies the empty-fibre convention without faithful flatness.

All cited node statements were read, and `citations.json` copies their statements verbatim rather than inferring a claim from a title, a proof, or a definition. The only non-elementary ingredients are the three cited theorem nodes in Steps 2 and 5. Every other step is the written-out primaryness, annihilator or fraction calculation. Proof dependencies are exactly the union of the uses lists. No proof step exceeds 2000 characters. No target, statement, unit, chapter, library file, or launcher script was changed.

Edge cases checked: Z to Q, q=(4), has empty fibre over (2) and qQ=Q. A zero target ring also has empty fibre and the quotient is zero. Nonreduced flat targets, e.g. Z to Z[e]/(e^2) with q=(4), satisfy the multiplication-injection argument without any reduction hypothesis. Over a field with q=0 the argument applies to every algebra, including rings with embedded associated primes, because every prime contracts to 0. Flatness is essential: k[t] to k[t]/(t), q=0, would have an empty fibre over 0 while qS=0 is proper. None of these cases invalidates a statement or introduces an extra hypothesis.

I checked delivery-errors B1–B10: no new nodes, statement unchanged and self-contained with its existing definitions, single TeX escaping, sources by tag and label, all recorded searches actually run, no new claimed Mathlib leaf or attachment. For C1–C8 I checked the precise cited clauses and their hypotheses as above, introduced no cycle or dependence on an internal proof construction, and declared generic off-unit tools. For D1–D5 the steps contain the argument and denominator details rather than delegate clauses to new nodes. For E1–E7 I checked the ring/module types, exact radical fibre, primaryness and Noetherian/flat hypotheses; no source error or statement correction was needed.

## Unfinished work

None in the mathematical split. Delivery validation is run with the required server tools; this report does not claim a Lean proof or compilation.
