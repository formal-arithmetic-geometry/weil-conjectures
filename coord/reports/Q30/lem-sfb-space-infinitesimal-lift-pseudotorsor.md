# Stage-1 report: lem-sfb-space-infinitesimal-lift-pseudotorsor

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-infinitesimal-lift-pseudotorsor.json: item, split into five steps; original statement retained verbatim; not a Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-differentials-finite-presentation.json: one new statement-only node, unsplit; not a Mathlib match.
- citations.json: a verbatim statement quotation for every cited node in every proof step.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for infinitesimal lifts, pseudo-torsors, square-zero derivations, and relative differential finiteness. No project declaration states the item. The existing project QuasicoherentSheafHom theorem is the Zariski scheme result already belonging to lem-weil-pbc-sheaf-hom-finite-presentation-quasi-coherent; it does not state the present item.

## WANTED

None. All sources used are present under literature/stacks-project/.

## Findings and corrections

The original statement is consistent with Stacks and is unchanged. Its empty proof was not a split. In particular, neither the pseudo-torsor property nor quasi-coherence may be inferred from a definition. The five steps now supply the relative derivation kernel argument, the matrix calculation for internal Hom, actual sheaf descent, and the restriction/action laws. I corrected an initial transcription of the differential definition tag to 04CT after reading tags/tags; 04CU and 04CV are the localization and quasi-coherence lemmas.

The historical blueprint ancestry has from.node = null. tools/blueprint_refs.py ancestor confirms None. I retained that ancestry rather than inventing a blueprint node, and appended a precise source place to the new node. Read the current literature/blueprint/latest/.../sk-thm-sf-ctf-stability/_section.md and direct-images.proof.md. They state the six-functor preservation route, not this infinitesimal lemma; this remains a generic prerequisite along the historical alteration/curve-moduli chain. Chapter and unit records were not changed.

## Not duplicates

lem-sfb-space-relative-differentials-finite-presentation vs lem-sfb-space-infinitesimal-lift-pseudotorsor: the new node states finite presentation of relative differentials for any locally finitely presented algebraic-space map; the item states a lift sheaf and its translation action, and uses differential finiteness as an input. It is not a clause of the item: the item does not conclude finite presentation of differentials.
lem-sfb-space-relative-differentials-finite-presentation vs lem-sfb-smooth-space-affine-infinitesimal-lift: the latter concludes existence of a global lift on affine tests for smooth maps; it merely cites Tag 05ZF in its supporting source chain. The new node has no smoothness or affineness requirement and asserts no existence of a lift.

Other close statements checked: lem-per-etale-local-lift-torsor-quasi-coherent is the scheme version of the item and cannot handle arbitrary algebraic spaces. lem-sfb-space-square-zero-lift-linearization has no local finite presentation hypothesis and already supplies the absolute lift bijection and its naturality; reused it, with no duplicate. lem-sfb-space-naive-cotangent-finite-local-model gives a two-term derived local model, not the explicit relative differential module interface. lem-sfb-space-qcoh-kernels-colimits states parts (1)-(3) of 03M1 and does not state differential finiteness. The scheme Hom node is already present: I did not create a second Hom-quasi-coherence node.

Searched the entire DAG by 05ZF, 03M1, 0618, 0619, 061A, 061C, 061D, by differential/finite presentation/internal Hom key phrases, and by parsing statements for potential generalizations. Ran blueprint_refs.py search for derivation, differentials, finite presentation differentials, locally finitely presented, internal Hom, 05ZF, 05ZN, and 061C; no blueprint statement supplies the missing differential finite-presentation lemma. Searched the project Lean source for that fact before creating it.

## Mathlib searches and results

searches.jsonl contains the actual msearch.py calls. Read all returned hits. Both semantic phrasings returned the commutative-algebra instance Algebra.instFinitePresentationKaehlerDifferentialOfFinitePresentation and general presheaf differential constructions. Loogle found that ring instance, and the stronger formally-smooth variant; no AlgebraicSpace theorem was found. Read the source at Mathlib/RingTheory/Extension/Cotangent/Basic.lean:537: it states Module.FinitePresentation S Ω[S/R] for finitely presented commutative algebras. It is relevant to a future split of the new node, but cannot by one-line specialization give finite presentation on algebraic-space etale charts or identify the differential sheaf. The source grep of the generated instance name returned zero because its declaration is an anonymous instance; a follow-up grep for the actual type found lines 537 and 540. Those actual results, including the zero hits, are preserved. The existing item search record from its creator is retained; the new logged searches are appended. No unavailable service is represented as an absence result.

## Review by Q30

I read Stacks spaces-more-morphisms.tex, Tags 0618/0619/04D0 and the complete statements and proofs of 061A, 061C and 061D, as well as 05ZF, 04CT, 04CU and 04CV. I also read spaces-properties.tex 03M1(6) and its matrix-kernel proof ingredients, and descent.tex 06VE(5),(8), using the existing equivalent module interfaces rather than creating the Hom comparison as another node.

For the new node, 04CT defines the universal differential sheaf on the small etale site, 04CU identifies compatible chart restrictions, 04CV says it is quasi-coherent, and 05ZF says precisely that local finite presentation of the space map makes this module finitely presented. The statement spells out finite presentation locally by finite free modules. No Noetherian or separation hypothesis enters those source statements. The node has no proof or proof dependencies.

Step 1 uses exactly the finite-presentation conclusion of the new node, the tensor adjunction of lem-weil-pbc-ringed-topoi-module-adjunction, and preservation of colimits by lem-weil-pbc-left-adjoint-preserves-colimits. It applies the latter only to a finite presentation, hence a small diagram. Free finite modules pull back to free finite modules by the basis/tensor formula. The ideal descends to O_T0 because its square is zero; on affine opens it is the A/J-module J, so its quasi-coherence here is the definition, not a new theorem.

Step 2 uses the kernel/finite-colimit conclusion of lem-sfb-space-qcoh-kernels-colimits and the local-presentation definition of site quasi-coherence, and explicitly identifies Hom with the kernel of a finite matrix. This avoids assuming that Hom of arbitrary quasi-coherent modules is quasi-coherent. The finite-presentation hypothesis proved in step 1 is essential. The closed-immersion node explicitly says its pushforward preserves quasi-coherence; j is a closed immersion by the thickening hypothesis. The scheme etale-Zariski equivalence node explicitly gives the restriction inverse and counit, so it supplies both the asserted Zariski quasi-coherence and H_et = j_*K. No statement about cohomology was substituted for that equivalence.

Step 3 cites the exact fpqc descent statement lem-a1-algebraic-space-fpqc-sheaf and the etale-to-fpqc covering lemma. The source domains here are schemes and the targets are algebraic spaces over the same S, so all hypotheses are available. Equalities over Y and over U0 are checked by the uniqueness part of that same node. The relevant base-changed family is again etale and jointly surjective. The argument requires no separation of X or Y.

Step 4 reads the statement of lem-sfb-space-square-zero-lift-linearization literally: it gives absolute S-lifts with fixed reduction and is natural for postcomposition by every S-map of spaces. Apply its naturality to f, so the required relative lifts are exactly the kernel of derivations under composition with f-sharp. The universal differential property is explicitly built into the item's definition of Omega_X/Y; the module adjunction turns it into Hom out of a0^*Omega. On every localized etale site this is the internal Hom section group by its definition; the algebraic-space definition explicitly says etale pullback is restriction. Thus no assumption that f is representable or has scheme target is made. Square-zero after etale base change is the affine ideal formula (JB)^2=0.

Step 5 is elementary assembly from that bijection: zero, addition, inverse and restriction are addition/subtraction of the same ring-sheaf maps, and uniqueness gives all action identities. Its only citation is the existing linearization bijection, whose inverse is addition of the derivation. I checked there is no choice of a global lift hidden here: if L(U) is empty, the action has empty domain there, and if it has a lift, the orbit bijection is precisely step 4. Restriction of sums and differences is written explicitly.

I checked B-E against the open files: no new definition or duplicate of a clause, no proof in the new node, every cited statement has a verbatim quote in citations.json, all references are by tags/labels, and every non-elementary input is named. Existing linearization and closed-immersion nodes have no path back to this item. No step exceeds 2000 characters. The two semantic search phrasings and the source reading rule out a missed one-line Mathlib specialization.

Edge cases: I=0 gives H=0 and at most one lift; identity f gives Omega_X/Y=0 and the unique lift is forced by b; empty test schemes have the unique empty morphism and zero module; finite presentations of ranks zero make the matrix-kernel calculation valid unchanged. Empty lift fibres remain allowed, and no step asserts local nonemptiness. Infinite-dimensional square-zero ideals are allowed; only the differential source module is finitely presented. Non-affine and non-separated test schemes are handled by sheaves and local presentations, not by intersections of affine opens assumed affine.

Off-unit tool uses are declared in split_report.tool_uses: the ringed module adjunction, the scheme etale-Zariski module equivalence, and the fpqc descent/covering tools are generic inputs, not replacements for the unit's six-functor route. No SGA source is used.

## Unfinished work

None for this one-level split. The one new node remains unsplit as required. Delivery checks and their final result are recorded below when completed.
