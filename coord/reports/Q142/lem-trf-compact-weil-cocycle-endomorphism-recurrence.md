# Stage-1 worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-compact-weil-cocycle-endomorphism-recurrence.json`: statement item, split into five short proof steps; no Mathlib match.
- `citations.json`: five verbatim quotations for the five step/node citations.
- `report.md`: this report. The search command maintains `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. The imported statement and statement dependencies are unchanged.

## Attachments

None. I searched the current project under `lean/WeilConjectures/` for the exact blueprint tag and for compact Frobenius, cocycle and recurrence terminology. `CompactWeilDatum.lean` defines compact Frobenius over the identity of the target but states no direct-power recurrence with point transport. `ExtendScalars/StrictWeilComplexFrobenius.lean` proves scalar-extension compatibility, not this recurrence. `TraceFormula/FrobeniusIterate.lean` defines iterates for a different coefficient presentation and explicitly does not prove the needed composition coherence. The related `lean/Sheaf/Paper/FrobeniusOperatorCompactDescription.lean` theorem still has `sorry`; its paragraph (4) is useful source material, not an attachment.

## Literature and searches

WANTED: none.

Read the current main-20261015 compact-description proof, the iterated-Weil-map definition and cocycle statement/proof, and the retained expanded Lean docstring paragraph (4). I also read Deligne, Weil II, printed pp. 150–153, (1.1.7), (1.1.10), (1.1.11) and (1.1.14), for the geometric Frobenius convention and compact-support action by transport of structure. Deligne provides the interpretation, not this exact finite-level derived formula; the calculation is therefore agent-authored. No SGA route is used.

The sandbox started with no item or earlier split/report. I retained all searches already recorded in the imported item and added the five actually executed searches from this group's log: LeanFinder, Loogle, grep, LeanSearch, and a second more general LeanFinder phrasing. The hits concern group cohomology, ring Frobenius and small-object iteration, rather than the stated transport. I read Mathlib's `SmallObject/Iteration/Basic.lean` (`ofNatTrans`, `mapObj_trans`) and `Sites/ElladicCohomology.lean`; none is a one-line specialization giving this statement. Blueprint searches for cocycle, transport, compact-support description and endomorphism recurrence found the existing cocycle and the ancestor description, not a separate recurrence theorem. No helper node is warranted for the final elementary composition calculation.

## Problems found and corrections

The item itself is true as stated. No statement dispute or changed hypothesis. Its imported proof was empty. I supplied the argument with the inverse pullback-composition map explicit, preventing the untyped suppression of the comparison between `TP_r` and `P_{r+1}`. No blueprint or import fields were removed. All proof steps are shorter than 2000 characters.

## Unfinished work

No unfinished stage-1 mathematical work. The cited existing nodes remain responsible for proving their own statements in later stages. No Lean was written and no compiler, Lake or build command was run.

## Not duplicates

No new nodes were created. The existing iterated-Weil cocycle, direct compact-transport composition, iterated-map definition and degree-one transport naturality are reused. The ancestor compact-description theorem additionally identifies the global operator and its powers; using it here would be circular and it is not cited.

## Review by Q142

I checked delivery-errors B–E against the node and sources. There are no new statements with hidden objects, proof sketches, missing definition references or repeated clauses, and no Mathlib leaves with unchecked locations. The item retains its finite coefficients A=O_E/varpi_E^n, n>=1, l!=p, separated finite-type X_0, geometric (inverse arithmetic) Frobenius, and one compactification over k_0 used for every power. I did not replace semilinear point transport by the identity on Spec k.

For step 1, I read the entire statement of def-trf-iterated-weil-map: its one-factor composite is phi. I read lem-trf-compact-frobenius-transport-composition: it explicitly identifies tau^(1) with tau_c. These two substitutions give precisely the asserted base case. For step 2 I checked that the same lemma assumes exactly our coefficients, scheme and retained compactification, and that its c_{r,K} has source TP_rK and target P_{r+1}K. Its displayed composition equation is copied verbatim into citations.json and is applied at M=K, m=r.

For step 3 I read the entire statement of lem-trf-iterated-weil-cocycle and compared it with the current blueprint. Its (m,n)=(1,r) formula is valid since both integers are positive. Its canonical identification is the inverse pullback compositor used in step 2, so it gives phi^[r+1] b_{r,K}=phi T(phi^[r]), with both sides typed TP_rK -> K. No auxiliary coherence lemma is being silently reproved here: the cited cocycle already states its formula for this canonical comparison.

For step 4 I read def-weil-frobenius-cohomology-transport, whose statement explicitly says both transports are natural, as composites of natural transformations. I use exactly that assertion, not a theorem inferred merely from a definition name. At u=phi^[r]:P_rK -> K its naturality equation has source H(P_rK) and target H(TK). Both coefficient objects are in the bounded constructible domain: K is in it by hypothesis, and P_rK is isomorphic to K by the specified iterate. This off-unit naturality statement is declared as a generic tool in split_report.tool_uses; it supplies no alternate route. Step 5 substitutes the three equations already established and uses only preservation of composition by H and associativity. I checked every composition domain, including H(b_{r,K}) and H(Tu), and the order is U_1 after U_r, as requested.

I tested r=1 explicitly: the cocycle gives phi^[2] b_1=phi T(phi) and naturality at phi reduces the direct tau^(2) composite to (H(phi) tau_c)^2. Zero K and empty X give the unique endomorphism. On a point with constant free coefficient object and matrix Weil map B, transports are the canonical scalar-identifications and the formula becomes B^(r+1)=B B^r. The argument needs neither an identity transport nor a general isomorphism-transport theorem. Every citation quote was checked as a literal substring of the cited statement. No long step conceals a separate lemma and no new dependency points upward to the ancestor.

The first dry run requested a longer verbatim quotation for the degree-one identification (minimum 40 characters). I replaced it by the complete sentence, without changing the proof or the cited fact.
