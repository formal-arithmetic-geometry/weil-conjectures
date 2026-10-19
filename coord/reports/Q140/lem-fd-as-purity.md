# Worker report: lem-fd-as-purity

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-fd-as-purity.json`: item, statement corrected and split; no new nodes.
- `citations.json`: five verbatim statement quotations for step 1.
- `report.md`: this report.

## Attachments

None. I searched the supplied `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` tree for the item id, its blueprint tag, and the theorem name recorded in `lean_audit.slopmaster2`; no matching declaration is present in that checkout. The audit entry is therefore not an attachment candidate for this delivery.

## WANTED

None.

## Statement corrected

STATEMENT-DISPUTED: the imported statement used `\psi` and `a` in `\mathcal L_{\psi,ax}` without introducing either one. The trace dependency [lem-fd-as-trace] requires the nondegenerate additive character over `k₀` and `a ∈ k₀^×`. I corrected the statement by explicitly fixing the character from [def-fd-additive-character] and requiring `a ∈ k₀^×`; this restores the intended Artin–Schreier purity assertion and adds the corresponding statement dependencies. The correction does not weaken the intended result; it supplies the hypotheses already required by the cited trace formula.

## What was checked

I read the item node, its source paragraph in `literature/blueprint/master/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-some-weight/lem-fd-as-purity.md`, and the current `main-20261015` statement. I also read the complete statements of [def-fd-additive-character], [def-fd-artin-schreier-sheaf], [def-weil-punctual-weights], [lem-fd-as-lisse], [lem-fd-as-trace], and [lem-tw-root-of-unity-modulus]. The main and master blueprint statements agree apart from the same undeclared symbols, and the corrected statement keeps their intended objects and conclusion.

The sole proof step uses [lem-fd-as-lisse] for lisse rank one, [lem-fd-as-trace] for the exact local trace value (whose `a ∈ k₀^×` hypothesis is now present), and [def-fd-additive-character] for the homomorphism property. Since the trace value lies in the finite additive group `k₀`, raising its character value to `q` gives the value at `q t = 0`, hence a root of unity. [lem-tw-root-of-unity-modulus] then gives complex modulus one, and [def-weil-punctual-weights] turns `|ι(α)| = 1 = q_u^{0/2}` into punctual purity of weight zero. Each cited quotation is copied verbatim into `citations.json`; no step relies on a proof detail absent from a cited statement.

I checked edge cases: the assertion allows every nonzero `a` (including the smallest finite field), every closed point degree (where `q_u` is positive), and the root-of-unity argument also works when the trace is zero, giving eigenvalue one. No new lemma is needed: the finite-group argument is written directly in the proof step.

## Review by Q140

I checked the source paragraph and both blueprint snapshots, then opened every cited DAG node. The corrected hypotheses are exactly the character and nonzero scalar required by the trace node; the Artin–Schreier sheaf definition and punctual-weight definition are included as statement dependencies. Step 1 takes only the lisse rank-one conclusion from [lem-fd-as-lisse], the displayed trace formula from [lem-fd-as-trace], the additive-character homomorphism from [def-fd-additive-character], the modulus conclusion from [lem-tw-root-of-unity-modulus], and the defining eigenvalue equality from [def-weil-punctual-weights]. The finite-group exponent calculation is elementary once the character homomorphism is stated, and it is written explicitly. The statement was tested at zero trace and at the smallest nonzero scalar case; all hypotheses remain meaningful and no conclusion is vacuous. The full-blueprint search found no duplicate statement, and the Mathlib searches (LeanSearch, LeanFinder, Loogle, and source grep) found no Mathlib declaration for this project-specific purity assertion. There are no new nodes, no external tool uses, no SGA citations, and no cycles.

## What was wrong or changed

The only source/item fault was the undeclared `ψ` and `a`; it is recorded above as STATEMENT-DISPUTED and repaired in the item. The imported proof also called the trace value a root of unity without explaining why; the repaired step supplies the finite additive-group calculation. The imported `uses_not_cited` note about the sheaf definition is retained as historical metadata; the definition is now correctly in `stmt_deps`.

## What remains unfinished

Nothing within stage 1. The item has no new unsplit nodes.
