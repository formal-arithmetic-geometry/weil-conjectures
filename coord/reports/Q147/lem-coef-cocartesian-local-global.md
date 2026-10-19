# Worker report: lem-coef-cocartesian-local-global

## Files written

- dag/nodes/sec-six-functors/lem-coef-cocartesian-local-global.json: existing statement, split into six steps, unchanged statement; no Mathlib match.
- citations.json: verbatim excerpts for every step citation.
- searches.jsonl: actual item searches through msearch.py, including two semantic phrasings.
- report.md: this report. No new DAG nodes, no Mathlib leaves, no unit file changed.

## Attachments

None. I searched WeilConjectures in /home/ubuntu/weil-src-slopmaster2 for the blueprint ID and case-insensitive cocartesian terminology; there is no matching project declaration. I also checked the exact upstream master tree for the ID; it is reference material only.

## Wanted literature

WANTED: Jacob Lurie, Higher Topos Theory, Remark 2.4.2.13, Remarks 2.4.1.9 and 2.4.1.12, Proposition 2.4.1.7, for lem-coef-cocartesian-local-global. Read directly online at https://www.math.ias.edu/~lurie/papers/HTT.pdf; no archival copy in literature/.

WANTED: Jacob Lurie, Higher Algebra, Lemma B.2.4(a), printed pp.1483-1484, for lem-coef-cocartesian-local-global. Read online at https://people.math.harvard.edu/~lurie/papers/HA.pdf; no archival copy in literature/.

## What needed correction

The shared local checkout did not yet contain this newly created item, nor references to its ID. A read-only SSH check found the authoritative server node and I copied that node directly into the sandbox. Its statement, source, ancestry and existing searches were retained. There was no earlier sandbox split or report to reuse.

The item is true as stated. The first clause only assumes a global lift from the particular source x. The tempting existing base-restriction theorem assumes lifts from every source above the relevant base arrows; using it would silently strengthen the hypothesis. Instead Steps 1--4 compare just the two relevant lifts in the same lift category. The strict-fibre equivalence clause is proved separately in Step 5, so it is not confused with equivalence merely in the total category. No STATEMENT-DISPUTED correction was necessary.

The inherited source HA B.2.4(a) is the application: that paragraph characterizes the marking through locally cocartesian edges. The specific one-source comparison appears as the opposite of HTT Remark 2.4.2.13. The proof_origin records an agent expansion using those online sources and existing foundational nodes. No forbidden SGA route is used.

## Not duplicates

No new nodes. I searched the whole DAG by cocartesian/local terminology and the blueprint with tools/blueprint_refs.py search 'cocartesian' and 'local.*cocartesian' (no blueprint hits), and checked the ancestor of prop-coef-integral-exceptional-adjoint. The existing lem-coef-infinity-cocartesian-base-restriction has stronger all-source hypotheses. The existing composition-initiality and equivalence outer-horn nodes provide the needed genuine inputs and are cited, not recreated. The historical inherited ancestry through the marked-pattern model construction is kept, as is unit sk-prop-sf-biduality-general. The unit has no own proof steps to replace.

## Review by Q147

I read the entire item from the server, its unit and chapter records, HA B.2.4(a) including the locally cocartesian description, and HTT's local-edge definition, lift uniqueness, composition, and Remark 2.4.2.13. I read in full the statements of every node cited in the six proof steps. I checked delivery-errors B--E against these statements and the actual proof; no new statement-only nodes were needed.

Step 1 uses def-cbc-enhanced-diagrams-cones for the degreewise pullback and quasicategory convention, and def-coef-infinity-fibrations for precisely the inner and first-outer horn lifting predicates. Filling after projection and pairing with the prescribed base simplex proves pullback lifting directly. Thus no unstated base-change theorem is used. Filling an inner horn first in the base and then in the total object establishes the quasicategory hypotheses needed later, including the strict fibres. This is an elementary unpacking of the two cited definitions.

Step 2 uses lem-cbc-inner-fibration-equivalence-outer-horn-lift exactly for its first-outer horn with a prescribed equivalence as edge 01, in every dimension n >= 2. This is exactly cocartesianness in def-coef-infinity-fibrations. The inclusion of a strict fibre preserves inverse edges and their inverse triangles by the simplicial definition in def-cbc-enhanced-diagrams-cones. The horn lifting tool is declared in split_report.tool_uses because it is a generic off-unit foundation, not a substitute geometric route.

Step 3 applies lem-coef-infinity-cocartesian-composition-initiality to r:E_a -> Delta1, after Step 1 verified both quasicategories and the inner-fibration hypothesis. Its statement explicitly says each cocartesian lift is initial in the lift category, and explicitly supplies the comparison equivalence of targets in the strict target fibre, together with the triangle. The target fibre is degreewise E_d. The projected triangle is over s_1(a), not an unspecified triangle up to base homotopy. Both lifts have exactly source (x,0) and base edge 01; no lifts from other sources are assumed.

Step 4 uses the composition/cancellation clause of that same node on the actual triangle supplied in Step 3. The first edge is the hypothesized global lift, and Step 2 establishes that the second edge is globally cocartesian. The clause then gives global cocartesianness of u. This writes the comparison argument in the item and does not move its content into another node.

Step 5 uses the degenerate-edge and lift-comparison clauses of composition-initiality with p itself and the degenerate base edge. The entire comparison triangle lies in E_c because its base simplex is constant, which verifies the stronger strict-fibre conclusion. I checked that lem-coef-infinity-mapping-composition explicitly provides both the triangle equation [u]=[h][1_x] and equivalence iff invertible component class, so it justifies exactly the claimed inference in h(E_c). Its unrelated mapping-space construction is not used. Conversely the equivalence witnesses in E_c remain witnesses in E, so Step 2 applies. There is no assumption that p reflects total equivalences into fibre equivalences.

Step 6 uses only conditions (i) and (ii) and the degenerate-edge inclusion in def-coef-categorical-pattern-fibrancy. Those exact clauses supply innerness, the required lifts and the identification of T with global cocartesian lifts over S. Applying the proved equivalences source by source gives the claimed local marking, including degenerate arrows. The cone requirements (iii)--(iv) are not invoked. This final substitution is elementary.

Small cases checked: E or a fibre empty (assertions with a source are then vacuous); the terminal base (cocartesian arrows are equivalences in E); the identity fibration (fibres are points); a product E=F x C (local and global cocartesian arrows are precisely equivalences in the F factor); a degenerate base edge with distinct vertices x,y in E_c; empty pattern cone-family; and marking S consisting only of degenerate arrows. The proof keeps the one-source existence hypothesis and never upgrades a locally cocartesian fibration to a global one. All dimensions of the horn conditions and all constant simplices in the strict fibres are retained.

I read the actual Mathlib hits: IsCocartesian and IsStronglyCocartesian in CategoryTheory/FiberedCategory/Cocartesian.lean:43-78 have ordinary categories and Hom-set universal properties. The Quasicategory/InnerFibration.lean predicates at lines 55-97 give inner-horn lifting but none of this local/global comparison. The semantic searches in two phrasings returned ordinary-category assertions, not a one-line generalization for these quasicategories. The searches of this attempt are logged and appended to the inherited item searches verbatim as query records. No search was invented.

I checked that proof_deps is exactly the union of uses and traced the cited foundational nodes' dependency closure: none depends on this item in the local DAG. Each citation has an exact statement quote. The longest proof step is 935 characters, so there is no step over 2000 characters hiding an extracted lemma. No new nodes or changed target statement are involved. No Lean was written and no compiler or build tool was run. The server dry run is the final mechanical authority.

## Unfinished work

No mathematical clause remains unsplit. The archival sources remain WANTED as above; the proof is therefore marked agent-origin. Delivery validation and push are performed with the authorized launcher tool.

## Continuation check, 2026-10-17

The existing sandbox split, report, citations and searches were reused. The required initial dry run exited successfully at 6e55a7aeee. I compared the sandbox with the now-current shared item: only split-owned fields differ. A renewed read-only search of both named source checkouts found no matching project declaration. I re-read all six dependency statements and checked every one of the ten citation quotes against the current statements; all are verbatim and their step/node pairs exactly cover the proof uses. The five logged searches were read and retained without repetition, and their ordinary-category and inner-fibration source hits were inspected.

I reopened Higher Algebra B.2.4(a), printed pp.1483--1484, and Higher Topos Theory 2.4.1.5--2.4.1.9, 2.4.1.11--2.4.1.12 and 2.4.2.13 online. The opposite of Remark 2.4.2.13 has exactly the one-source lift hypothesis used here; B.2.4(a) supplies the marking application. The initial-lift comparison node explicitly supplies the strict-fibre comparison and triangle required by Steps 3 and 5, and its composition clause has the correct cocartesian orientation for Step 4. Step 5 applies the homotopy-category clause to the quasicategory E_c already established in Step 1. No mathematical repair was needed. I corrected only Step 6 source.document, which had incorrectly pointed to HTT despite its place field naming Higher Algebra. The longest step remains 935 characters. A final dry run and push follow this citation-path correction.
