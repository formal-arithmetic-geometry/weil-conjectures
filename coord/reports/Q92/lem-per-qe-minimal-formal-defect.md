# Q92: lem-per-qe-minimal-formal-defect

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-qe-minimal-formal-defect.json: statement retained; complete fourteen-step stage-1 proof; status split. No exact project declaration or Mathlib match found.
- dag/nodes/sec-deligne-laumon-a1/lem-per-local-g-ring-adic-lifting.json: statement-only local G-ring lifting theorem; Mathlib searches found no match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-semilocal-g-ring-j2.json: statement-only theorem that a Noetherian semilocal G-ring is J-2; Mathlib searches found no match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-g-ring-quasi-excellent-closed-fibre.json: statement-only Theorem 4.1, quasi-excellence of a G-ring from a quasi-excellent Jacobson closed fibre; Mathlib searches found no match.
- citations.json: verbatim statement quotations for all 51 step/node uses. Full statements are quoted so that hypotheses remain visible.

Three new statement nodes; zero Mathlib leaves. New nodes have no proofs and no proof dependencies.

## Attachments

None. Searches in the live read clone's lean/WeilConjectures/ by the item blueprint tag and by minimal formal singularities, Rotthaus, G-ring lifting and the new nodes' concepts did not find a sorry-free project declaration proving this item or any of the new inputs. Existing sorry declarations are not attachments. No Lean was written or compiled.

## Literature wanted

WANTED: Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber), Theorem 5.1 Step 2 and Claim 5.2, printed pp.9–11, and finite-extension consequence printed p.13, for lem-per-qe-minimal-formal-defect. URL: https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf . The paper is not archived in literature/ on this read clone. I read the PDF online without downloading it; archive it and integrate its citation entry. Since the local literature lacks it, proof_origin.by is agent, as the standing brief requires.

WANTED: same paper, Appendix A, Definition A.1(2), printed p.14 and the G-ring LLP assertion printed p.15, also Theorem 5.1 equation (5.1), printed p.9, for lem-per-local-g-ring-adic-lifting. Its cited original is Rotthaus, Komplettierung semilokaler quasiausgezeichneter Ringe, Nagoya Math. J.76 (1979), 173–180; the present node uses only the local case of the semilocal lifting property.

WANTED: same paper, Section 2, printed p.2 and the use after equation (5.1), printed p.9, for lem-per-semilocal-g-ring-j2. Its cited original is Matsumura, Commutative Algebra (1980), Theorem 76. I verified the theorem as stated in Kurano–Shimomoto, not an unavailable copy of Matsumura.

WANTED: same paper, Theorem 4.1, printed p.4 and proof printed pp.4–7, for lem-per-g-ring-quasi-excellent-closed-fibre. This theorem assumes a G-ring and a quasi-excellent quotient by a Jacobson ideal; it does not assume completeness. It is independent of the later main completion theorem and so does not create a circular citation to the parent.

No SGA source was used.

## What needed repair or clarification

The imported statement is retained: no statement dispute, hypothesis change, or weakened conclusion. The imported node was unsplit. Its blueprint ancestor is lem-per-artin-gabber-affine-curve, Step 3 (regular local model and purity), through the already recorded chain of completion inputs. The newest blueprint was read through literature/blueprint/latest/, and the chapter and unit records were read. The new nodes refine this auxiliary algebra route and do not replace a step of the unit.

Two potentially hidden comparisons are now explicit steps. First, the maximal completion of a principal-adic completion agrees with the original maximal completion: step 2 computes each quotient using existing exact-completion and finite-module tensor nodes, then takes the compatible inverse limit. This is elementary assembly from those nodes, not a new theorem. Second, steps 10–11 choose an explicit nonzero product in all surviving singular components and prove regularity after inverting it point by point. They do not assert an unproved equality of singular ideals after regular base change.

The source tests the generic fibre after suitable finite extensions. Here the item is over Q, and the stated definition of geometric regularity tests finite purely inseparable extensions; all such extensions in characteristic zero are trivial. Thus L=Frac(R), whose normalization is R, suffices for this part of the proof. The universal assertion about C for all L is proved in step 3, and the conclusion about all B_L is proved in step 14. Nothing has been omitted from the item.

The source's local G-ring lifting input must not be replaced by lifting for arbitrary non-semilocal G-rings: Appendix A explains that the unrestricted property fails. The new lifting node is expressly local. Likewise the closed-fibre theorem is stated with a quasi-excellent quotient, not merely a J-2 quotient.

## What remains unfinished

No missing argument in the item's one-level split. The three independent G-ring inputs remain statement-only for subsequent workers, as required by stage 1. Their original references need local archival as requested above. No stage 2 or stage 3 work was attempted.

## Searches and duplicate audit

For the item and each new node, I ran the mandated msearch.py commands (LeanFinder, LeanSearch, Loogle, and Mathlib grep), inspected the returned hits, and used a second semantic phrasing before concluding no match. mathlib_searches preserves the exact queries and logged results in searches.jsonl. Hits on adic completeness, local rings, Jacobson radicals, smooth loci and a Brodmann local-cohomology bibliography entry do not state any of the three G-ring theorems. None of the selected recorded searches was unavailable. Earlier exploratory searches for a possible completion-comparison node and a J-2 formulation are preserved in the log; neither node was created.

I searched the whole DAG by G-ring, lifting, semilocal, quasi-excellence, formal fibre, completion, singular locus and related wording, read the candidate statements, and searched the whole blueprint with tools/blueprint_refs.py before creating the nodes. No source Stacks tag is assigned to a theorem that is not in Stacks. The new source is the explicitly located paper. The cited existing completion, regularity, dimension and excellence nodes already carry their Stacks source places. All new nodes have blueprint.from places and via chains, and same_as is empty after the blueprint search. Generic algebra tools from other units are declared in split_report.tool_uses; they support the prescribed route.

## Not duplicates

lem-per-local-g-ring-adic-lifting vs lem-per-qe-complete-pair-lifting: the existing parent concludes quasi-excellence of an arbitrary complete pair; the new input lifts only the G-ring property for a local ring from its G-ring quotient and is the independent Rotthaus input used inside that parent, not its conclusion.

lem-per-local-g-ring-adic-lifting vs lem-per-gabber-adic-quasi-excellence: the existing completion theorem concerns preservation of quasi-excellence under completion; the new theorem assumes completeness of the given local ring and a G-ring quotient and concludes G, without assuming quasi-excellence of the base.

lem-per-local-g-ring-adic-lifting vs lem-weil-pbc-g-ring-completion-regular: the existing node assumes G to prove the regularity of a completion map; the new node establishes G from the complete local quotient, so the existing hypothesis is exactly what is missing.

lem-per-semilocal-g-ring-j2 vs lem-per-complete-local-excellence: the existing result assumes maximal-adic completeness, while a semilocal G-ring need not be complete; the new implication supplies J-2 from geometrically regular formal fibres and finitely many maximal ideals.

lem-per-semilocal-g-ring-j2 vs lem-per-j2-finite-algebra-criterion: a criterion involving regular loci of module-finite algebras does not itself prove that those loci are open from the G-ring hypothesis. The new theorem has G and semilocality as its inputs.

lem-per-g-ring-quasi-excellent-closed-fibre vs lem-per-qe-complete-pair-lifting: Theorem 4.1 assumes G, does not assume completeness, and proves J-2/quasi-excellence; the parent establishes quasi-excellence from completeness without a G assumption. The parent depends on this item, so it is deliberately not cited here.

lem-per-g-ring-quasi-excellent-closed-fibre vs lem-per-gabber-adic-quasi-excellence: the existing node concerns completion of a quasi-excellent ring; the new node concerns an already G-ring with a quasi-excellent Jacobson closed fibre, without completeness.

lem-per-g-ring-quasi-excellent-closed-fibre vs lem-per-quasi-excellent-localization: localization preserves an already known quasi-excellence hypothesis, whereas the new statement derives quasi-excellence of the whole G-ring from a quotient.

## Review by Q92

I checked delivery-errors B through E against the JSON statements and the online paper, not only the dependency lists. I read Theorem 5.1 Step 2, Claim 5.2 and the final consequence on pp.9–11 and 13 for the item, Section 2 p.2 for semilocal G implies J-2, Theorem 4.1 and its proof pp.4–7 for the closed-fibre criterion, and Appendix A pp.14–15 together with (5.1) for local lifting. The three new nodes isolate independent source inputs, not clauses restating the item or an elementary consequence of other cited statements.

Step 1 uses finite-type-algebra-noetherian only after observing that finite module generators are algebra generators. localization-noetherian and adic-completion-noetherian apply to the resulting Noetherian rings. adic-complete-jacobson-radical applies because B_L is assumed x-complete, and adic-completion-mod-ideal applies to A, a Noetherian ring. These statements give exactly Noetherianity, x in the maximal ideal, and the complete quotient used here.

Step 2 reuses adic-complete-jacobson-radical for C. completion-exact-finite-modules applies to the finite modules m^j, A and A/m^j since A is Noetherian. completion-finite-module-tensor identifies the completed inclusion with the ideal m^jC, including naturality of quotient maps. The nilpotence x^j=0 on A/m^j makes the other completion stabilize. The localness and inverse-limit identification are written out; no unquoted formal comparison theorem is assumed.

Step 3 uses quasi-excellent-localization on B/xB at the image of n. The local-lifting node applies to C and ideal xC, whose completeness and localness were proved in steps 1–2, and quotient G follows from quasi-excellence. The semilocal node applies because local implies one maximal ideal. g-ring-completion-regular and local-completion-faithfully-flat then apply to the Noetherian local C. Its maximal completion was identified with the assumed normal local domain in step 2, so faithfully-flat-normal-ring-descent has its target-normal hypothesis. Normality is descended rather than asserted for a completion of an arbitrary normal ring.

Step 4 uses quasi-excellent-localization on the nonzero quotient R/t, g-ring-completion-regular on its indicated localization, and formal-fibre-quotient-iso for the exact prime and quotient in question. I checked that the last statement identifies the fibre rings; it is not just a definition of a formal fibre. This proves every nonzero-prime fibre, not just the fibre at x.

Step 5 checks x nonzero, so R/xR is one of the assumed quasi-excellent quotients. The complete-Jacobson node supplies the ideal hypothesis for the new closed-fibre theorem. The maximal-ideal G criterion supplies an actual bad maximal completion, and the faithful-flat local-completion node supplies flatness. With step 4 only its generic fibre can be bad. I read def-weil-pbc-g-ring: its geometric regularity test is by finite purely inseparable extensions. Since K has characteristic zero, these are trivial. This justifies ordinary nonregularity of the generic fibre without a missing finite-extension criterion.

Step 6 uses flat-over-regular-with-regular-fibre only on local maps whose source local ring is regular and whose closed fibre is regular by the already regular map C to its maximal completion. The prime-contains-minimal-prime statement applies to the ideal defining the closed singular locus and produces a minimal singular prime below the bad prime, so its contraction remains zero. It proves nonemptiness, not merely existence of some unspecified singularity.

Step 7 uses noetherian-prime-finite-height to make the height minimization a minimization in N. serre-criterion-normal gives R1 from the normality proved in step 3, and serre-conditions-rk-sk explicitly says R1 means regularity in height at most one. Thus neither height zero nor height one can occur. No global finite-dimensionality assumption is inserted.

Step 8 uses noetherian-completion-flat for R_n to C and local-flat-faithful-flat for the local map. minimal-prime-over-proper-ideal applies after faithful flatness shows pC proper. flat-going-down then proves that the selected Q contracts exactly to p. I checked flat-height-formula: it has no finite-type hypothesis and explicitly gives the local dimension formula. Minimality over pC makes the closed fibre zero-dimensional, so it proves the exact height equality required here.

Step 9 uses localization-noetherian and adic-completion-noetherian for C_Q and T. flat-completion explicitly states flatness of the induced map between the two maximal completions of a flat local homomorphism; it is not merely flatness of one completion. local-completion-local-ring identifies the maximal ideals and makes this map local, after which local-flat-faithful-flat applies. def-weil-pbc-g-ring quantifies over every prime of C, and hence gives regularity of C_Q to T without assuming excellence of C_Q.

Step 10 uses finite-minimal-primes-over-ideal for the Noetherian ring C and its singular ideal. The remaining deductions are strict chain lengths and finite products in a domain: when a surviving singular minimal prime is strictly below Q its height is less than h, so it cannot contract to zero; if it equals Q it contracts to the fixed nonzero p. Empty singular support uses the explicit empty product b=1.

Step 11 uses prime-contains-minimal-prime to detect which singular components survive at each contracted prime, then flat-over-regular-with-regular-fibre on the localized regular map from step 9. Its source and fibre regularity are both supplied. localization-noetherian supplies the Noetherian part of regularity of T[1/b]. This proves the needed consequence pointwise and avoids hiding a singular-locus comparison as an uncited theorem.

Step 12 uses flat-under-regular with the source and target both local and the map flat, after choosing primes by faithful flatness; regular-local-localization accounts for further localization. The faithful-flat local-completion node supplies flatness of A to its maximal completion. Every generic prime avoids b because b is nonzero in the domain R. Step 4 supplies all other geometric fibres, and the same characteristic-zero argument as step 5 supplies the generic one.

Step 13 uses the maximal-ideal G criterion on the local Noetherian A and the semilocal theorem on its one maximal ideal. I checked the definition of excellence: it also requires universal catenarity. The step proves its localization using a finitely presented finite-type model over R and equality of prime-chain intervals under localization, rather than omitting it. The zero prime is treated separately using fields-excellent, not the nonzero-p argument.

Step 14 uses dimension-formula-universally-catenary-finite-type-domain only for the finite extension R subset B_L, which is finite type and has algebraic fraction and residue extensions. Both transcendence degrees in the cited formula are zero, giving the required equality of heights. finite-type-localization-excellent applies after step 13 has established excellence of R_p; B_L base changed to R_p is finite and its q-localization is the desired local ring. This proves the second family of local excellence conclusions for all L.

I checked small cases and scope: p=0 uses the field argument, Q minimal in the closed fibre gives dimension zero even if that fibre is nonreduced, h=2 is allowed by R1, and the empty surviving singular-prime list gives b=1. The nonzero nonunit x condition and all normality, Noetherianity, completeness and catenarity hypotheses remain in place. The proof never applies a theorem to a non-Noetherian generic fibre: it is a localization of a Noetherian completion. No non-elementary step exceeds 2000 characters. No new node is an elementary tensor/localization observation, a disguised clause of the item, a known duplicate, or an uninspected Mathlib hit.

The first dry run rejected the phrase “the item's hypothesis” in step 3 as a standalone-node wording violation (B2). I replaced it with the precise assumption on the maximal-adic completion of $(B_L)_{\mathfrak n}$; no mathematical content changed.
