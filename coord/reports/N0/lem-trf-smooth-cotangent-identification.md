# Stage-1 worker report

Item: lem-trf-smooth-cotangent-identification. Group: N0. Date: 2026-10-18.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-smooth-cotangent-identification.json: split statement, four proof steps; no whole-statement Mathlib match.
- citations.json: verbatim statement quotations for every use in every step.
- report.md: this report. searches.jsonl contains the mandated command log.

New nodes: 0. New Mathlib leaves: 0. The proof reuses two existing cotangent-complex nodes and three existing Mathlib leaves.

## Attachments

None. Searched WeilConjectures/ in the read-only slopmaster2 checkout for the exact blueprint tag, cotangent complex, and polynomial algebra, and read its related RingTheory material. The project standard-smooth polynomial declaration concerns a finite-variable smoothness property, not the derived cotangent augmentation. No project declaration states every clause of this item. The upstream master checkout was consulted as reference only, not treated as evidence of completed proofs.

## WANTED

None. All sources used are available in literature/stacks-project/.

## Corrections and observations

The mathematical statement is unchanged. The initial item had no proof and no Lean audit attachment. Its existing dependencies really define the cotangent construction, derived category, and universal differentials. The title mentions a differential basis although the statement only asks for the cotangent identification; Step 3 records the existing arbitrary-variable basis result as useful supporting information, with no added hypothesis or finite-rank claim. No STATEMENT-DISPUTED issue was found.

The original Mathlib search records were retained. Eight fresh commands, in two phrasings, are logged in searches.jsonl and appended to the item with the exact query text and actual results. The Loogle error for the unqualified identifier is recorded, not taken as evidence of absence; the second quoted-identifier search succeeds. Read the returned types and Mathlib/RingTheory/Extension/Cotangent/Basic.lean around lines 53–65 and 335–344: its cotangentComplex is a presentation linear map and H1Cotangent is its kernel. Read Kaehler/Polynomial.lean lines 28–101: mvPolynomialEquiv and mvPolynomialBasis describe the ordinary differential module. These are not the full derived cotangent theorem. The existing arbitrary-variable basis leaf is used directly.

The inherited chapter, unit, creation record, blueprint ancestry and statement-dependency list are retained. This is an auxiliary input below lem-trf-lci-cotangent-presentation in the inherited historical semistable-modification support branch. I read the chapter and unit records and did not change their route or realization records. There is no new off-unit non-Mathlib proof tool: both cotangent nodes have the item's unit, and all three off-unit nodes are Mathlib leaves.

## Not duplicates

No nodes were created. Whole-DAG and whole-blueprint searches for cotangent, polynomial differentials, 08QH and 08SF located the existing resolution, arbitrary-variable basis, differential-localization and intrinsic/localization-comparison nodes. The affine comparison contains the general ring-localization theorem, so creating a separate cotangent-localization node would duplicate it. The lci parent uses this item and cannot be used in its proof. Existing naive-cotangent and H1 results give only a truncation or first homology; none replaces the polynomial full-complex argument.

## Review by N0

I read coord/delivery-errors.md B–E in full and checked this delivery against their mathematical requirements with the source and every cited statement open. For the item I read cotangent.tex Tags 08QG/08QH, the arbitrary-resolution comparison in 08QI and functoriality in 08QL, and the localization proof in 08SF. The proof follows the source's constant polynomial resolution rather than introducing a node restating the desired polynomial clause. There are no new nodes whose sources or hypotheses need a separate review.

Step 1 uses only the convention and resolution criterion stated in lem-trf-cotangent-resolution-coherence. Its statement says that degreewise polynomial surjections and an augmentation quasi-isomorphism form a polynomial resolution. The constant resolution has identity augmentation in every degree, all face maps are identities, and the explicitly computed alternating differential pairs every negative degree with an identity. This proves the needed criterion directly. The elementary mark refers to this calculation, not to an uncited resolution-existence theorem.

Step 2 uses that same node's actual canonical comparison for every polynomial resolution and its naturality for morphisms of augmented polynomial resolutions. These clauses, not just its title, justify replacing the standard resolution by the constant one. The negative-degree homotopy is given explicitly, with h in odd homological degrees only; I checked dh+hd in degrees 0, -1, -2, and the two parity cases. The identity in degree zero supplies the augmentation inverse. I also checked the evaluation formula on dq tensor p: it identifies the resulting isomorphism with the augmentation specified in the item, rather than an arbitrary isomorphism between its objects.

Step 3 uses exactly the statement of lem-weil-pbc-polynomial-ring-kahler-basis-any-variables, including its base-changed basis clause. I read its source algebra.tex 00RX and the returned Mathlib basis implementation. The extension from finite to arbitrary variables is the same universal derivation calculation with finite supports and is already stated by the existing node. Neither the proof nor the item assumes E finite.

Step 4 uses the last, ring-localization clause of lem-trf-affine-cotangent-comparison. I checked that it explicitly gives the canonical map from the ordinary tensor complex to the cotangent complex after localizing both rings. Taking S={1} in A and W=T in P satisfies its compatibility hypothesis for every multiplicative subset T, so its target is L_{C/A}, with the same base A. It does not assume Noetherianity, smoothness or principal localization. I read 08SF in the source to check this orientation. The statement of lem-weil-pbc-localization-module-exact explicitly preserves every exact pair of modules, so applying it to cycle and boundary sequences preserves the augmentation quasi-isomorphism. I read algebra.tex 00CS for this use. The tensor/localization identification is written as two inverse formulas, rather than citing the existing principal-localization-only tensor node for arbitrary T; the balancing relation and fraction equivalence check it in a few lines (00DK). Finally lem-weil-pbc-kahler-differentials-localization explicitly states the arbitrary multiplicative-subset isomorphism with the exact generator formula used here, as in algebra.tex 00RT(2). The formula on differential generators also checks the augmentation compatibility, so the final object is the localized differential module in degree zero with its specified map.

I tested the empty variable set (P=A, M=0), a singleton, infinite E, zero base ring, T={1}, and localization with 0 in T. The latter has C=0 and both differential and cotangent complexes zero, consistently with the same exact-localization argument. No finite presentation, nonzero ring, domain or smoothness hypothesis has slipped into an invocation. Every proof dependency appears in a step and every step use has a verbatim citation entry. No step exceeds 2000 characters; the short homotopy and tensor/fraction calculations are elementary computations from the cited constructions and do not hide a new comparison lemma. All new-node return checks are vacuous because none were created; the non-elementary facts used are precisely the five existing statements cited. No SGA source, compilation, Lean change, or live-project write was used.

## Unfinished work

None in the mathematical split. The required server preflight and final push are the remaining delivery operations.
