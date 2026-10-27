# Stage-1 delivery: lem-trf-restricted-saturated-submodule-finite

## Files written

- dag/nodes/sec-trace-formula/lem-trf-restricted-saturated-submodule-finite.json: existing statement unchanged; complete four-step split; additional recorded searches.
- dag/nodes/sec-trace-formula/lem-trf-restricted-flat-module-finite-presentation.json: new statement-only analytic finite-presentation input; unsplit, no Mathlib match.
- citations.json: one verbatim statement quotation for every node used by every proof step.
- searches.jsonl: actual msearch search records, retained unchanged.

One new node, zero new Mathlib leaves. Two existing Mathlib leaves are reused.

## Attachments

None. Searches under lean/WeilConjectures for the exact blueprint tag, restricted/saturated submodules, restricted series, and Tate algebras found no declaration stating the item. The restrictedProduct in RingTheory/TateResidue is a different construction. No Lean was written and no compiler was run.

## Wanted literature

WANTED: Siegfried Bosch, Lectures on Formal and Rigid Geometry, April 2008 preprint, https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf, Section 2.3, Theorem 4 (printed p.130, PDF page 131) and Lemma 7(i) (printed pp.131–132, PDF pages 132–133), for both this item and lem-trf-restricted-flat-module-finite-presentation. The primary PDF was read online; no archival copy was found under literature/. Accordingly proof_origin.by is agent, as the brief requires when the local document is missing. The report requests the archival copy; no literature file was written.

## Errors and corrections

The imported statement is correct, and its statement and statement dependencies are unchanged. The original proof was empty. The proof now writes the missing implication from pi-saturation to torsion-freeness for every nonzero scalar, rather than silently equating pi-torsion and V-torsion. No finite-presentation assumption on M, Noetherian assumption on V, discreteness assumption on the absolute value, or finite-type assumption on the restricted-series ring is introduced.

## Unfinished work

The new analytic finite-presentation theorem is deliberately statement-only and remains for its own stage-1 item. The report does not claim the full dependency closure is proved. All work authorized for this one-level split is complete, subject to the delivery checks.

## Search and blueprint audit

Read GOAL.md, the three blueprint levels in SETUP.md, stages/1-dag.md, roles/worker.md, coord/brief-stage1.md, and both copies of delivery-errors B–E. Read the item's unit sk-i-curve-zero and chapter sec-trace-formula, and the current latest blueprint statement/proof of lem-trf-local-term-locality. The item is a historical analytic sub-argument below that ancestor, not an attempt to replace the current contracting-correspondence proof.

Ran blueprint_refs.py ancestor for the item, and searches for saturated, saturated submodule, restricted series, topologically finite, valuation, finite presentation, flat modules, torsion-free, Raynaud, and restricted. Inspected the relevant DAG statements found through restricted-series, valuation/flatness, and finite-presentation/kernel searches across the DAG. No blueprint statement supplies the new theorem; the broad restricted search largely finds unrelated restrictions of functors. The new blueprint.from uses the returned ancestor, extends the item's via chain by the item, and identifies Bosch 2.3/4 as the supporting input to 2.3/7(i).

All new searches used the prescribed msearch command and their exact tool/query pairs were copied from searches.jsonl into node records. Both the item and the new node have LeanFinder searches with a second mathematical phrasing, Loogle, grep, and LeanSearch. Services returned answers. Read the returned signatures and Mathlib sources: Algebra/Module/FinitePresentation.lean:67–118,191–193, RingTheory/Flat/TorsionFree.lean:74–101, and RingTheory/MvPowerSeries/Restricted.lean:28–45. Module.finitePresentation_of_finite requires a Noetherian coefficient ring; ordinary PowerSeries theorems concern a different ring; flat-plus-finite-presentation results already assume the desired conclusion. No search hit proves the analytic input. Module.FinitePresentation.fg_ker is already represented by lem-trf-finite-presentation-surjective-module-kernel and is reused rather than duplicated. The older searches on the live item are preserved as provenance.

## Not duplicates

lem-trf-restricted-flat-module-finite-presentation vs lem-trf-valuation-finite-type-module-presentation: the existing Tag 053E(2) concerns algebras of algebraic finite type; the new theorem concerns the restricted-series algebra, which need not be of algebraic finite type over V.

lem-trf-restricted-flat-module-finite-presentation vs lem-trf-valuation-flat-finite-module-presentation: the existing local essentially-finite-type theorem does not cover the restricted-series ring; no such finite-type hypothesis is justified here.

lem-trf-restricted-flat-module-finite-presentation vs lem-trf-restricted-saturated-submodule-finite: the new theorem asserts finite presentation of an arbitrary finite V-flat S-module Q; the item asserts finite generation of P inside a possibly non-flat and non-finitely-presented M. The quotient construction, scalar torsion argument, flatness theorem and generic kernel theorem connect these different statements in four explicit steps.

lem-trf-restricted-flat-module-finite-presentation vs lem-trf-restricted-submodule-adic-topology: that node compares induced and intrinsic adic topologies of arbitrary submodules, and uses the item; it does not state finite presentation of finite flat modules.

lem-trf-restricted-flat-module-finite-presentation vs lem-trf-restricted-quotient-complete: completeness/separatedness of quotients is a different conclusion, and that node is above the item, so using it would risk a cycle.

lem-trf-restricted-flat-module-finite-presentation vs def-trf-restricted-series-presentation: the definition describes series and presentations, not a theorem asserting that finite V-flat modules are finitely presented.

lem-trf-restricted-flat-module-finite-presentation vs lem-trf-finite-presentation-surjective-module-kernel: the existing Mathlib leaf assumes a finitely presented target and proves finiteness of its kernel; the new analytic theorem establishes the needed target finite presentation.

No new Stacks tag is introduced: the new theorem has Bosch 2.3/4 as its source. Existing Stacks 0539 and 0519 leaves are cited directly.

## Review by NX

I read Bosch's online primary PDF from the case-(V) hypotheses at the start of Section 2.3 through Theorem 4, Corollaries 5–6, and Lemma 7 and its proof. Lemma 7(i) states saturation finiteness for any finite ambient module, and its proof passes to the flat quotient M/N, then invokes Theorem 4. Theorem 4 states finite presentation of finite modules flat over the valuation base. In the height-one case Bosch also describes its proof by intersecting a generic-fibre relation module with the integral lattice, using 1.3/10. This is substantive analytic finiteness, so it belongs in the new statement-only node rather than being called elementary or hidden inside the item. The new theorem is the restricted-series specialization of 2.3/4, with all field, valuation ring, variables, module and flatness objects explicitly introduced. Completeness and a real-valued nontrivial norm match Bosch's rank-one setup. Its definitions are existing nodes, whose statements I opened and read; flatness is over V, while finite generation and presentation are over S.

For Step 1 I checked the statement of def-weil-finitely-generated-module: a finite generating family spans, so its quotient images span. The remaining argument is explicit scalar arithmetic: for nonzero a, real convergence of |pi|^k to zero gives a k with |pi|^k <= |a|, hence pi^k/a lies in V. Thus a*x in P implies pi^k*x in P and saturation implies x in P. This uses no cancellation in M, no completeness theorem for M, and no analytic finiteness fact. It is a short elementary quotient argument, not a new lemma to move out.

For Step 2 I opened lem-trf-valuation-torsionfree-flat and checked its conclusion is flatness for every torsion-free module over a valuation domain, without finite generation over V. I read Stacks more-algebra.tex, lemma-valuation-ring-torsion-free-flat, Tag 0539, and the Mathlib match in Flat/TorsionFree.lean. The quotient Q and the given V meet precisely those hypotheses.

For Step 3 I read the new statement again against Bosch Theorem 4. The Q from Step 1 is a finite S-module, its scalar action is through constant series, and Step 2 gives V-flatness. Hence its finite presentation over S is exactly the new node's conclusion, not an unrecorded transfer from polynomial finite type.

For Step 4 I opened lem-trf-finite-presentation-surjective-module-kernel: it allows any finitely generated source P and finitely presented target Q over any commutative ring. I read Stacks algebra.tex, lemma-extension, Tag 0519(5), and Mathlib Module.FinitePresentation.fg_ker at lines 191–193. Applying it directly to M -> M/P avoids the unnecessary choice and enlargement of a free presentation in Bosch's prose. The kernel is literally the given submodule P by the quotient relation. Every hypothesis is supplied by the item or preceding steps; no source freeness is required.

I tested r=0, M=0, P=0 when M is torsion-free, P=M (Q=0), and M=S/(pi). In the last example saturation forces P=M, so the proof must and does handle ambient torsion. For a nondiscrete valuation ring with non-finitely-generated maximal ideal m, m is not pi-saturated in V because pi*1 belongs to m while 1 does not. This excludes the tempting false unrestricted-submodule finiteness assertion. The new theorem allows Q=0 and r=0, where finite torsion-free valuation modules are free. It makes no assertion for finite modules that have V-torsion.

I checked delivery-errors B–E individually: new node statement only, notions defined by their actual cited definitions, TeX encoded once, source locators precise, real search logs, no new Mathlib leaf to mislabel, ancestor and duplicate searches, no attachment; every used non-elementary fact has a node whose statement I read and quote verbatim in citations.json, with no use of proofs as interfaces; no back-edge to the parent completeness/topology nodes, no off-unit proof theorem, no elementary/duplicate/self-clause nodes; and the scalar argument, quotient object, and kernel hypotheses hold in the edge cases above. All four steps are below 2000 characters, and the full assembly is below 3000 characters. I corrected the empty proof and explicitly documented the missing archival source, without changing the item statement or writing to the shared repository.
