# Stage 1 delivery: lem-sfb-unramified-cotangent-fibre-criterion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-unramified-cotangent-fibre-criterion.json: statement, split; no exact Mathlib match.
- citations.json: eleven step/node entries with verbatim statement quotations.
- searches.jsonl: actual msearch.py records, retained alongside this report.

No new nodes, no Mathlib leaves. The original item statement, statement dependencies, provenance, creation record and earlier searches are retained. The five proof steps total 2912 characters; no step exceeds 2000 characters. Only the sandbox was written. No Lean was written and no compiler, Lake or build command was run.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for unramified/cotangent/differential variants. The project has FormallyUnramified.exists_neighbourhood_of_stalkMap in AlgebraicGeometry/Morphisms/FormallyUnramifiedStalkNeighbourhood.lean, but it assumes formal unramifiedness of a stalk ring map; it does not state this item's differential-fibre equivalence. It is therefore neither an attachment nor a substitute for the whole proof.

## WANTED

None. All sources needed are present in literature/stacks-project/.

## Corrections and route

The statement is correct as written. There is no STATEMENT-DISPUTED. The unsplit item had no proof; this delivery supplies the proof without strengthening its hypotheses. In particular locally of finite type is sufficient; locally of finite presentation, closedness of the point, perfect residue fields, flatness and Noetherian hypotheses are unnecessary.

Read the chapter sec-six-functors-basics, unit sk-thm-sf-ctf-stability, the three levels in SETUP.md, and the inherited exceptional-fibre argument in resolve.tex, Tag 0C5R, lines 4957–4961. This node supplies the unramified-point criterion used there. Its existing blueprint creation chain ends without an imported blueprint ancestor: blueprint_refs.py ancestor explicitly returned None. Retained that metadata and its precise existing from.place instead of inventing an ancestor. Blueprint searches for unramified, unramified cotangent, cotangent fibre and unramified-at-point supplied no duplicate statement (the unramified search returned conventions and unrelated boundary-monodromy nodes).

No unit or chapter was changed. Generic tools from other units are declared in split_report.tool_uses: the relative-differential finite-type clauses, the affine sections comparison and the support/annihilator criterion. They supply commutative algebra and differential-sheaf infrastructure, not replacement proof routes for any unit.

## Mathlib searches

Preserved the four searches inherited from the original item. Ran five further searches using msearch.py: leanfinder with the scheme differential-fibre criterion, loogle for AlgebraicGeometry.FormallyUnramified, grep for relativeDifferentials/unramified combinations, leansearch for zero differential fibre implying an unramified neighbourhood, and a second leanfinder phrasing using Nakayama. Read all hits. Read Mathlib/RingTheory/Unramified/Locus.lean, especially Algebra.unramifiedLocus_eq_compl_support (line 111), basicOpen_subset_unramifiedLocus_iff, and exists_unramified_of_isUnramifiedAt, plus the FormallyUnramified scheme class source. These are ring-locus or affine formal-unramified statements; none alone is the scheme fibre equivalence. The item is an assembly of existing DAG facts, not a Mathlib leaf. All five actual searches succeeded; no unavailable service was recorded as an absence result.

## Not duplicates

No new node was created. Reused lem-trf-relative-differential-sheaf-base-change rather than introducing a finite-type differential-sheaf lemma, lem-weil-pbc-finite-type-module-support-closed rather than a stalk-zero shrinking lemma, the existing affine differential sections and localization nodes rather than new comparison nodes, and the existing Nakayama leaf rather than a special-case tensor-zero lemma. In particular lem-sc-rational-unramified-cotangent-criterion assumes closed rational points and cannot replace this arbitrary-point statement. lem-trf-affine-chart-stalk-differentials assumes local finite presentation and was deliberately not cited under the weaker finite-type hypothesis here.

## Review by Q143

I read morphisms.tex Tag 02GF (lemma-unramified-at-point), including the proof of (1), (3) and (5), rather than merely its equivalence list. I also read Tag 01V2 (lemma-finite-type-differentials), Tag 01UT (lemma-differentials-affine), Tag 02G4 (definition-unramified), Tag 02G5 (lemma-unramified-omega-zero), and the affine characterization 02G6. For support I checked morphisms.tex Tags 056I and 056J; for localization I checked algebra.tex Tag 00RT (lemma-differentials-localize), part (2); for Nakayama algebra.tex Tag 00DV (lemma-NAK); and for the basic open schemes.tex Tags 01I3 and 01HV. No SGA source is used.

Step 1 uses only the finite-type and quasi-coherence conclusions of lem-trf-relative-differential-sheaf-base-change, not its unused cartesian comparison. The affine chart comes directly from the stated definition of locally finite type. I opened lem-sc-relative-differentials-affine-sections: its statement identifies sections on arbitrary compatible affine opens, without requiring finite presentation. I opened the support node: it explicitly says both that M is finite and that F_x is M localized at the point's prime. The localized generators give finiteness of the stalk without an implicit Noetherian theorem.

Step 2 uses the affine-cover equivalence explicitly included in def-weil-unramified-morphism, and the affine sheaf description in def-sc-relative-differential-sheaf. The chart inside W is also a chart for the original f, so its zero ring-differential module makes the original differential sheaf zero there. There is no unsupported identification of a new relative differential sheaf with a restriction and no appeal to an uncited restriction theorem.

Step 3 applies the tensor version actually stated in lem-weil-pbc-nakayama-local-generators, with the empty generating family. The ring is the local ring at x, the module is finite by Step 1, and exchanging tensor factors is the elementary map m tensor a to a tensor m over a commutative ring. No equality or separability of residue fields is assumed.

Step 4 uses the annihilator criterion explicitly stated by lem-weil-pbc-finite-type-module-support-closed. Since the stalk vanishes, the annihilator is not contained in the point's prime; thus g can be chosen outside that prime. The fraction calculation proving M_g=0 is written out. The cited localization node explicitly gives Omega(A_g/R) isomorphic to Omega(A/R)_g, exactly the needed comparison.

Step 5 uses both clauses of lem-weil-pbc-affine-open-section-vanishing-prime: g outside the prime gives x in D(g), and D(g) is affine with section ring A_g. Finite type after this localization is proved by listing the old algebra generators and 1/g, not assumed from an uncited theorem. Finally the affine-cover characterization of unramifiedness applies to D(g) mapping into V inside Y; no conclusion about an open immersion into Y is mistakenly inferred from an affine chart alone.

I checked B–E point by point: there are no new statements with missing objects, no relabelled clauses, no source tags used instead of dependency nodes, and every uses entry has a verbatim quote in citations.json. The cited prerequisite closures were traversed and none reaches the item, so the added proof edges create no cycle. All five steps are marked non-elementary because they invoke genuine cited results; none is longer than 2000 characters.

Small-case checks: for an identity map the differential module is zero and both conditions hold, including at nonclosed points of a non-Noetherian scheme. For an arbitrary closed immersion Spec(R/I) to Spec R, even with I not finitely generated, the map is locally finite type and the relative differential module is zero; the proof never assumes finite presentation. For A^1 over a field, including its generic point, the differential fibre has rank one and there is no unramified neighbourhood. For a nontrivial purely inseparable finite field extension in characteristic p the differentials need not vanish, as required (for k=F_p(t) and L=k(u), u^p=t, Omega(L/k)=L du). Empty schemes give no x to test; an already-zero module permits g=1. These checks confirm the intended arbitrary-point scope.

## Repair of returned delivery 4705b314ac6

The return of 2026-10-23 04:22 UTC approved the mathematics but reported that a side-project completion had not been promoted to the live queue DAG. I continued the retained delivered sandbox and compared it with the current read clone. The current item is unsplit, with empty proof and proof dependencies; its statement, statement dependencies, source, creation record, chapter, unit and blueprint metadata agree with the retained version. There is no released repair note that changes the route. The required initial dry run exited successfully at 6f2187161e4 before these repairs. The delivery tool constructs the delivery on current origin/sheaf-dag, retaining current maintainer-owned fields; no manual repository write or git command was used.

I re-read all nine distinct proof prerequisites in the current DAG. All eleven quotations saved with the returned split equal the entire current statements byte for byte, including the finite-type differential clause, the unrestricted affine sections comparison, the stalk/annihilator criterion, the tensor form of Nakayama, and the affine-cover unramified characterization. Thus there is no changed cited mathematical statement to replace and no new hypothesis to supply. I also re-read the seven statement definitions. The prerequisite closure has 206 nodes and does not reach the item. The local source search still supplies no exact project declaration of the item's equivalence; the existing stalk-map neighbourhood theorem has a different hypothesis and conclusion. I retained the actual logged Mathlib searches after reading their recorded results and the relevant ring-locus source; the search question has not changed.

The repair retains the approved argument and makes two elementary calculations explicit: Step 3 now constructs the two inverse tensor-swap maps and checks their composites on pure tensors; Step 4 writes m/g^r=(gm)/g^(r+1)=0 and specifies the powers-of-g multiplicative set for the localization theorem. These are calculations within the existing steps and require no new lemma. I re-read Stacks 02GF, 01V2, 01UT, 02G4/02G5/02G6, 056I/056J, 00DV, 00RT, 01HV and 01I3, together with the inherited exceptional-fibre use in resolve.tex. The arbitrary-point, non-Noetherian, identity, closed-immersion and inseparable-field checks in the signed review still apply. Every step remains below 2000 characters. This report and the explicit proof calculations are changes beyond rebasing or re-pushing unchanged content.

## Unfinished work

None at stage 1. The independent maintainer review remains the delivery protocol's next step.
