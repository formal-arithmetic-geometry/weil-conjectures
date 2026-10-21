## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-bounded-dual-components.json`: item, statement, now split into six elementary calculations; no Mathlib match.
- `citations.json`: verbatim statement excerpts for every step/node pair.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log.

No new nodes and no Mathlib leaves. The statement and statement dependencies are unchanged. No unit record is changed: this is a subordinate calculation, not the unit's key node.

## Attachments

None. Searching the project's `lean/WeilConjectures/` for the item tag found none. Concept searches found `CochainComplex.rightDual` in `Algebra/Homology/Monoidal/Dual.lean`; reading its construction shows the hypothesis that every term has a right dual. It therefore does not prove this item for arbitrary module sheaves. `homComplex_unit_iso` in `Algebra/Homology/HomComplexUnitIso.lean` instead treats Hom **from** the degree-zero unit. `homComplex_sc_iso_dual_total` concerns a specified opposite double complex, not the bidual evaluation map. None states all clauses under this item's hypotheses.

## WANTED

None. Both Stacks sources and the current blueprint proof are available locally.

## Audit findings and changes

The item had an empty proof. Its stated signs are correct and need no repair. I supplied explicit projection/insertion inverses, reversed bounds, both differential calculations, the sheaf-level evaluation construction, its parity calculation, and the chain-map equation. I did not import the finite-projective or exactness assumptions from the parent item.

I read Stacks `sites-cohomology.tex`, Tag 0A8X (`section-hom-complexes`, lines 8571 onward), and Tag 08JJ (`lemma-dual-perfect-complex`, lines 13048 onward). The former gives the entire product and differential construction. The latter's second proof paragraph identifies the degree-reversed ordinary dual and says that the bidual map is evaluation up to sign. The proof here supplies that sign and its compatibility with the differential directly. No derived comparison, local-to-global argument, or theorem about reflexivity is used.

The current blueprint is `main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-internal-hom.proof.md`, second paragraph, final sentence. It uses the coefficient dual of a locally constant perfect complex. The parent `lem-sfb-ringed-site-strict-perfect-hom` invokes this item in steps 2 and 4 for the degree-reversed bound and signed bidual. The unit and chapter routes are retained. The computed blueprint ancestor is null because an inherited creation chain reaches a Lean module name; I retained the documented blueprint location and made its purpose explicit, rather than inventing an ancestor.

## Searches and reuse

There was no earlier sandbox node, report, or search log to resume. The original item's four Mathlib search records are retained. Six additional searches were actually run through the prescribed `msearch.py`: LeanFinder with the internal-sheaf phrasing and then the twice-dual differential phrasing, Loogle `CochainComplex, Module.Dual`, LeanSearch with the signed differential/bidual phrasing, and two grep queries. All services answered successfully. The queries and actual hit names are recorded in the item and the command's log.

I read Mathlib `Algebra/Homology/HomotopyCategory/HomComplex.lean`, especially `δ` at line 401 and `HomComplex` at line 566, and the single-target cochain construction in `HomComplexSingle.lean`. These are external cochains in morphism abelian groups, not an identification of the internal sheaf Hom, nor a proof of all bidual clauses. Thus these hits are candidates for later implementation tools, not a leaf for this statement.

DAG searches by `08JJ`, signed bidual, and dual components, plus `blueprint_refs.py` searches for `bidual`, `ordinary dual`, and `dual components`, found broader derived/perfect duality results or more restrictive coefficient/projectivity statements. The directly relevant existing `lem-sfb-ringed-site-duality-maps` concerns derived normalization, and the parent uses this very item, so neither is used circularly. No new node was necessary.

## Not duplicates

No new nodes. In particular I did not introduce separate nodes for unique maps to/from zero, projection away from zero factors, evaluation naturality, or the parity identity: each is written out as a short elementary calculation.

## Review by NC

I checked delivery-errors B through E against the node and the sources. Each proof step is a calculation from the two cited definitions, rather than an invocation of an uncited theorem. No step is longer than 2000 characters and no step hides a lemma with separate hypotheses. The six step texts spell out the proof; none delegates a clause to a new node. The cited definitions are existing nodes, exempt from the unit-route restriction, and no off-unit theorem is used.

For step 1 I read the full statement of `def-pur-hom-complex`: its product is computed sectionwise and its elements are homogeneous maps on the slice. I also read `def-pur-sheaf-hom`: its sections are maps of sheaves on the slice, with restriction by restricting maps. This is exactly what makes the displayed projection and zero insertion inverse sheaf morphisms. In step 2 that same sheaf-Hom definition makes Hom out of the zero sheaf the zero module; the inequalities were checked in both directions needed for the support assertion. No assertion that infinite products are exact is needed.

For step 3 the cited Hom-complex definition explicitly supplies the differential, and setting the target differential equal to zero gives the sign by one substitution. For step 4 I used that same formula a second time and the definition of sheaf Hom to interpret precomposition twice: the sign product is `(-1)^(i+1) (-1)^(-i) = -1`, so the bidual differential is negative double dual. There is no assumed unsigned identification of complexes, only of their degree objects.

For step 5 the sheaf-Hom statement supplies the correct slice-valued interpretation of evaluation. I wrote evaluation on every `V -> U`, so this does not confuse a map of sheaves with a map on one set of sections. Commutativity of the coefficient ring gives the required linearities. The Hom-complex definition supplies the degree constraint: the only surviving evaluation has dual degree `-i`, giving parity `-i^2 = i mod 2`. For step 6 I evaluated both sides of the proposed chain-map equation on every such slice and every local dual map; the two signs agree. These are precisely the cited definitions' statements, and `citations.json` quotes actual substrings from both nodes for each occurrence. I checked all these substrings before writing the file.

I tested the formulas on a complex concentrated in an arbitrary positive or negative degree, the zero complex, and the degenerate bound `a > b`. For the two-term identity complex over the one-point site with ring Z in degrees 0 and 1, the dual differential in degree -1 is +id, the bidual differential in degree 0 is -id, and beta is (+id,-id), giving the chain equation. In degrees -1 and 0, beta is (-id,+id) and the same equation holds. In characteristic 2 the minus signs all become plus consistently. Finally a degree-zero Z/2 module over Z has zero ordinary dual and zero bidual map; the statement requires a chain map, not its invertibility, so it correctly includes this nonprojective example. No hypothesis or statement correction was needed.

## Unfinished work

None within this stage-1 item. There are no new unsplit nodes, no requested literature, and no Lean edits or compiler invocations.
