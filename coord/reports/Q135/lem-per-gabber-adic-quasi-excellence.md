# Q135: lem-per-gabber-adic-quasi-excellence

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-gabber-adic-quasi-excellence.json`: item, split into nine steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-gabber-normal-counterexample-reduction.json`: statement only, unsplit; no Mathlib match. Gives the normal principal counterexample and its finite normalizations without a rational-algebra hypothesis.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-gabber-minimal-formal-defect.json`: statement only, unsplit; no Mathlib match. Produces the minimum singular formal-fibre height and the excellent low-height localizations without a rational-algebra hypothesis.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-gabber-semilocal-defect-height.json`: statement only, unsplit; no Mathlib match. Supplies the semilocal completion, normalized boundary, flatness, reduction and height comparisons without a rational-algebra hypothesis.

`citations.json` contains the full verbatim statement of every node cited in every step. `searches.jsonl` is the search command's unmodified log. The scratch transformation script is confined to this sandbox; it is not part of the delivery.

## Attachments

None. Searched `lean/WeilConjectures/` by the item's blueprint tag, Gabber/adic terminology, quasi-excellence terminology, and the three proposed inputs. No declaration states the item or the new inputs. The isolated appearance of quasi-excellence in a derived-stability comment is not a theorem. No Lean file was written and no compiler, Lake or build tool was run.

## Wanted literature

WANTED: Kurano–Shimomoto, *Ideal-adic completion of quasi-excellent rings (after Gabber)*, https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf, Theorem 5.1 Steps 1–3, Claim 5.2 and Claim 5.4, for the item and the three new Gabber nodes. The paper was read online (including pp.7–14); it is not in the permitted local literature directory. No document was downloaded. Existing qe-* source records already identify this same paper. Since the detailed proof's local copy is missing, `proof_origin.by` is `agent`, with the local ILO statement and the precise online comparison recorded.

## Problems found and corrected

The item itself agrees exactly with ILO Exposé I, Théorème 9.2, printed p.17/PDF p.23, including arbitrary characteristic. No STATEMENT-DISPUTED correction is needed. Its original proof was empty.

The existing `lem-per-qe-complete-pair-lifting` is restricted to rational algebras; three structural inputs in its proof have the same restriction. Their statements cannot be applied to this item. Kurano–Shimomoto's Theorem 5.1 has no characteristic restriction, and its Steps 1–3 prove the corresponding unrestricted inputs. Only those three restricted nodes required new general versions. The existing alteration-neighbourhood and Rotthaus boundary statements already work in arbitrary characteristic and were reused. None of the new nodes asserts quasi-excellence lifting as its conclusion, nor does it assert G-ring/J-2 as a clause of the item. They are distinct intermediate constructions in the contradiction proof.

In the reused assembly I expanded the closed fibre calculation: all denominators of the semilocalization avoid the contracted prime, so the residue tensor is the original residue field. I made generic-fibre flatness cite the scheme-over-a-field lemma and flat base change, instead of using an uncited assertion about tensors of vector spaces. I added explicit Noetherian stalk checks and a minimal-height choice in the finite-boundary argument, then renumbered all proof references. Each non-elementary step is below 2000 characters; no long step conceals an additional lemma.

## Not duplicates

- lem-per-gabber-normal-counterexample-reduction vs lem-per-qe-normal-counterexample-reduction: the latter assumes a Noetherian rational algebra and returns a rational domain; the new input applies to an arbitrary Noetherian complete pair, including positive and mixed characteristic.
- lem-per-gabber-minimal-formal-defect vs lem-per-qe-minimal-formal-defect: the latter assumes a domain over the rationals; the new statement applies to a normal Nagata domain in arbitrary characteristic. The low-height excellence argument is Claim 5.2 of the unrestricted theorem.
- lem-per-gabber-semilocal-defect-height vs lem-per-qe-semilocal-defect-height: the latter assumes a domain over the rationals; the new comparison applies to an arbitrary-characteristic minimum-defect configuration.
- Each new node vs lem-per-gabber-adic-quasi-excellence and lem-per-qe-complete-pair-lifting: none states that a complete ring with quasi-excellent quotient is quasi-excellent; respectively they construct a counterexample reduction, a minimum defect, and its boundary height comparison. The contradiction and its finite-boundary argument remain in the item.

Searched the entire DAG for quasi-excellence, the source paper, normal counterexamples, formal defects and semilocal defects. The six qe-* records were opened, not just their dependency lists. Whole-blueprint searches with `tools/blueprint_refs.py search` for quasi-excellent, quasi-excellence, formal defect, semilocal, normal counterexample, and semilocal defect found no blueprint duplicate. `ancestor` returned `lem-per-artin-gabber-affine-curve`. Read the ancestor's current proof in `literature/blueprint/latest/`; the new nodes retain its completion-lifting provenance through the existing chain. No chapter or unit route is altered. The item is not the unit's key node, so no unit record is changed.

## Review by Q135

I read the local ILO PDF around Exposé I §§8–10, in particular the exact statement and limitations following I.9.2. It requires only Noetherianity, ideal-adic completeness and quasi-excellence of the quotient; it does not require a field, a characteristic bound, universal catenarity of the original ring or finite dimension. I read Kurano–Shimomoto's unrestricted theorem and its reductions, the minimum-height claim, the semilocal calculation and final alteration diagram online. The new reduction is Step 1 (1-1)–(1-4), the new minimum-defect statement is Step 2 and Claim 5.2 with the finite-extension observation on p.13, and the new semilocal statement is the normalized boundary definition and Claim 5.4. These are the precise arguments already isolated by the rational versions; removing their rational-algebra restrictions is justified by this source, rather than assumed from the older nodes. The new files contain no proof or proof sketch in their statements.

Step 1 uses exactly the new counterexample reduction. Its hypotheses are the original Noetherian complete pair and the contradiction assumption. Its conclusion supplies a normal Nagata domain A, a nonzero nonunit x and all the finite-normalization properties needed subsequently. The auxiliary universal catenarity is a conclusion of this reduction, not a new hypothesis on the original R.

Step 2 uses the complete hypotheses of the minimum-defect node, all supplied by Step 1. It then uses the semilocal node on an attaining triple, so the minimum is global over the finite extensions, not just over primes of one fixed normalization. The statements give h >= 2, the excellent localizations, the same contracted primes, and heights h and h+1. I checked that the boundary is defined in the normalization of D_gamma/s_gamma, and that the cited semilocal statement explicitly identifies it with contractions of primes minimal over s_gamma+xD_gamma. This is the precise boundary used by Rotthaus, not an unnormalized substitute.

Step 3 applies the existing alteration-neighbourhood statement to B and xB. B is Noetherian and integral, B/xB is quasi-excellent from the reduction, and B_q is excellent for ht(q) <= h from the minimum-defect node. That node's conclusion really supplies the proper surjective witness, its open cover, and regularity above the specified closed fibre; no construction from its proof is used. The union Omega contains every such q because b_q avoids q.

Step 4 uses the semilocal statement's alternative boundary description to choose the actual prime Q-tilde. The element b_q avoids both it and s_gamma by their stated contractions. Surjectivity after base change is the statement of `lem-weil-pbc-surjective-base-change`; closedness of that same base change follows directly from universal closedness in `def-weil-proper-morphism`. I did not assume the alteration charts themselves proper.

Step 5 uses `lem-trf-closed-map-specializing` on the proper witness, lifting the general point first and then its specialization. Both lifts lie in one open chart because open sets contain generalizations. Their images specialize by continuity. Q contains x, so the regularity conclusion of the alteration-neighbourhood node applies exactly to zeta_1.

Step 6 uses the semilocal statement's flatness and reduction isomorphism, the flat ring/affine equivalence, flat base change, and the definition of flatness at a stalk. I checked the closed fibre by the localized quotient calculation written in the step; every inverted element already has nonzero residue. Thus it is a field and is regular. The finite-type Noetherian theorem supplies the affine chart rings after tensor base change; localization Noetherianity supplies their stalks. The regular-source/regular-closed-fibre flat-local criterion therefore has both of its Noetherian hypotheses, and yields regularity at eta_1.

Step 7 uses regular-local localization for the generalization eta_2. Since s_gamma contracts to zero, this point is in the generic fibre over Frac(B). The scheme-over-a-field lemma and flat base change give the local flatness used for descent. The source is a localization of Noetherian D_gamma and the target was checked in Step 6. `lem-weil-pbc-flat-under-regular` therefore contradicts the exact nonregularity stated by the semilocal node. There is no inference from mere flatness of B -> D_gamma to flatness of the alteration itself.

Step 8 uses only finite minimal primes from the Noetherian lemma and boundary heights from the semilocal lemma. The elementary chain argument, including existence of a minimal prime under Q by minimizing its finite height, is written out. Since Omega contains all primes of height <= h, every boundary point of height h+1 is a minimal prime of its closed complement. Hence the boundary is finite. This is an elementary inference from those statements, not a new node.

Step 9 checks every hypothesis of the existing Rotthaus criterion against the three new statements: B is Noetherian Nagata and x-adically complete; s is minimal singular; every s_gamma has positive height; and Step 8 proves finiteness of the same normalized Delta. Its conclusion s intersect B != 0 contradicts the chosen minimum-defect triple. That contradiction proves the original item.

I checked small cases: J=0 gives the identity implication and cannot start a bad-pair reduction. J=R with completeness forces the zero ring, for which the spectrum is empty and all quasi-excellence conditions are vacuous. Nilpotent ideals cause no missing separatedness assumption because completeness is defined by the canonical isomorphism. Complete local rings over fields of positive characteristic and mixed-characteristic complete DVRs are within scope, which is exactly why the rational versions are insufficient. In the new minimum-defect statements, h=0 or h=1 is excluded by normality; an empty singular locus is incompatible with the stated non-quasi-excellent counterexample assumptions. Gamma always contains the selected maximal ideal and is nonempty. No globally finite-dimensional ring assumption is used; only the finite heights of individual Noetherian local rings enter the minimum and chain arguments.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 of the delivery-error checklist against the files: definitions are existing explicit nodes, source places are exact theorem/claim labels (no invented Stacks tag for a non-Stacks theorem), each new statement introduces its own objects, every citation quotes its actual statement, no cited proof is mined, and no elementary boundary or comparison lemma was created as a redundant node. Every new node was searched with the mandatory command in two semantic phrasings, Loogle and Mathlib grep, with LeanSearch also used. The actual height and completion hits are proper ingredients, not a one-line proof of any new statement, so all three stay unsplit. Off-unit uses of generic algebra/topology are declared in `split_report.tool_uses`. No SGA source is used. The item statement, pointers and imported metadata are preserved.

## Unfinished work

No part of the one-level split remains unfinished. The three new statement-only inputs intentionally remain queued for later splitting. The local bibliographic copy requested above is not present; its precise online source was read and the assembly is marked agent-written.
