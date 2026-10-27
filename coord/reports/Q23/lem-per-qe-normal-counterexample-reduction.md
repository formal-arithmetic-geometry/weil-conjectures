# Stage-1 delivery: lem-per-qe-normal-counterexample-reduction

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-qe-normal-counterexample-reduction.json: item, split into eight argument steps, statement unchanged.
- dag/nodes/sec-deligne-laumon-a1/lem-per-qe-jacobson-g-ring-criterion.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-qe-finite-surjective-descent.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-adic-nagata-lifting.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-adic-normal-completion-lifting.json: statement, unsplit, no Mathlib match.
- citations.json: verbatim statements for every citation in all eight steps. searches.jsonl and the search result files retain the actual msearch output.

## Attachments

None. I searched WeilConjectures for the blueprint id, quasi-excellence, Nagata, and normal completions. The only quasi-excellence hit is a comment in SixFunctors/Etale/Derived/Stability.lean; it does not state this result. No compiler or Lake command was run.

## Literature requests

WANTED: Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber), https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf, Theorem 4.1, Theorem 5.1 Step 1 and (5.3), for the item and all four new nodes. The live literature directory has no bibliographic copy. I read the authors' PDF online; integration into literature/ and LIST.md is requested, not performed by this worker.

WANTED: Greco, Two theorems on excellent rings, Nagoya Math. J. 60 (1976), Theorem 3.1, for lem-per-qe-finite-surjective-descent.

WANTED: Marot, reference [8] in Kurano–Shimomoto, theorem on lifting Nagata rings, for lem-per-adic-nagata-lifting.

WANTED: Nishimura–Nishimura, reference [12] in Kurano–Shimomoto, Theorem A and the Z-ring normal-completion criterion recalled in Step 1 (1-4), for lem-per-adic-normal-completion-lifting. These original proofs are future work on the statement-only nodes, not assertions that they were read here.

## Audit and route

No mathematical or statement dispute was found. The source of the live item refers to a previous sandbox copy, which this sandbox does not have; I checked the current authors' PDF online instead. I preserved the item's source and all other maintainer fields. Since the paper is not in the authorized literature tree and the supplied argument expands several omitted details, proof_origin.by is agent.

The latest blueprint ancestor lem-per-artin-gabber-affine-curve.proof.md, Step 3, is read together with the live item's ancestry through the formal-completion and quasi-excellence-lifting nodes. This delivery only supplies the completion proof's Step 1, and does not change the perverse unit, its route, or its realization. Generic algebra statements from other units are declared individually in split_report.tool_uses. No SGA source is used.

Before creating nodes I searched the entire DAG by quasi-excellence, Nagata, Greco, Marot, Nishimura, Z-ring, G-ring, finite descent, universal catenarity and normal completion, and used blueprint_refs.py searches for quasi-excellent, G-ring, Nagata, formal fibres, normal completion, finite surjective and finite surjective descent. I read the potentially overlapping statements, including quasi-excellent finite-type stability, Nagata permanence, henselian normal completion preparation and Ratliff formal catenarity. None states one of the four new lemmas. The new nodes do not assume a counterexample or construct the desired R: they are reusable inputs, not restatements of the existential reduction. Each new node has an empty proof and empty proof_deps.

Each item and new-node search has LeanFinder, Loogle, source grep and LeanSearch, plus a second semantic wording. Results were read from the saved output. All services returned answers in this run. No match states quasi-excellence or Nagata lifting; the normality hits concern integral closedness of localizations, not completions. In the descent grep, Greco matches a substring of strongRecOn; these are explicitly irrelevant. There are zero Mathlib leaves.

## Not duplicates

lem-per-qe-jacobson-g-ring-criterion vs lem-per-quasi-excellent-finite-type-stability: the new lemma deduces J-2 from a G-ring and one Jacobson quotient, whereas the existing result starts with a quasi-excellent base.

lem-per-qe-finite-surjective-descent vs lem-per-quasi-excellent-finite-type-stability: descent is the reverse implication along finite surjective spectra, without flatness.

lem-per-adic-nagata-lifting vs lem-weil-pbc-finite-over-nagata-nagata: lifting assumes a Nagata quotient and completeness, whereas the existing lemma assumes the base itself is Nagata.

lem-per-adic-normal-completion-lifting vs lem-per-henselian-normal-completion-preparation: the new lemma assumes only a normal complete pair and a quasi-excellent closed fibre; it does not assume the ring itself quasi-excellent or excellent. The old preparation's normal-completion clause assumes an excellent local domain and cannot be applied here.

lem-per-adic-normal-completion-lifting vs lem-per-henselian-excellent-completion-domain: the existing statement assumes excellence and henselianity and concludes only domainhood; the new input is the weaker Nagata Z-ring lifting consequence needed before quasi-excellence is proved.

## Review by Q23

I read Kurano–Shimomoto Theorem 5.1 Step 1 (1-1) through (1-4), printed pp.7–8, and Step 2 through (5.3), printed p.9. For the new G-ring criterion I read Theorem 4.1, including its hypothesis that I is in the Jacobson radical. For finite descent and Nagata lifting I read their explicit invocations in (1-3) and the lifting-property table and explanation in Appendix A. For the fourth node I read (1-4) and (5.3): normal completions come from the Nagata Z-ring lifting theorem, not from the quasi-excellence lifting theorem being proved. I also read ILO Exposé I §9, which warns that universal catenarity itself does not lift; I have not made that false inference.

In step 1, the definition of a Noetherian ring gives finitely many generators, the finite-module completeness statement applies to the cyclic modules A/I_i, and the subideal lemma applies because the next ideal is principal. I checked that the Jacobson-radical lemma says every maximal ideal contains the complete ideal, so the selected x cannot be a unit. Zero or unit ideals I cannot provide a counterexample and are covered by this argument rather than extra hypotheses.

In step 2, I opened the maximal-condition node: its second clause gives a maximal member of an arbitrary nonempty collection of submodules, which is exactly what is required (ACC on one preselected chain alone would not suffice). Quotient completeness follows from finite-module completeness. The existing quasi-excellent finite-type stability node applies to the affine finite-type morphism Spec(C/(J+xC)) to Spec(C/xC). The nonzero ideals of the chosen quotient correspond to strictly larger ideals upstairs.

In step 3, the new criterion requires a G-ring and a Jacobson ideal; step 2 supplies the quasi-excellent quotient and the radical lemma supplies the latter hypothesis. I read the pair-of-primes criterion's full equivalence and its explicit identification of the quotient generic formal fibre. This lets a failed pair force Q=0, because every nonzero quotient is quasi-excellent, hence a G-ring by the definition. The domain conclusion therefore has a proof, rather than an unsupported reduction to a component.

In step 4, quasi-excellent implies Nagata by the existing statement. Marot lifting needs precisely Noetherianness and completeness already established. I read the Nagata-domain N-2 lemma and the Japanese-domain definition: the identity fraction-field extension is allowed and gives finite normalization. The integral-closure statement supplies both normality and domainhood; the finite-over-Nagata statement supplies Noetherianness as well as Nagata permanence. Finite-module completeness applies before any completion claim is made. Lying over gives the surjectivity hypothesis for Greco descent; no flatness is assumed. The newly introduced normalization is not silently assumed to be bad.

In step 5, I checked the omitted preservation of (A2) explicitly: choose 0≠b∈K and express b=a/s inside Frac(D); then 0≠a=sb∈K∩D. Thus a finite-type algebra over a nonzero quotient of D is really in force. This is a few-line argument, retained as an elementary step using the existing finite-type-stability statement; it is not a new node. K=R is allowed, giving the zero quotient.

In step 6, I checked all hypotheses separately for each arbitrary finite field extension L. N-2 gives finiteness; the integral-closure statement gives a normal domain even for a nontrivial extension; finite-over-Nagata gives Nagata and Noetherian; finite-module completeness gives x-adic completeness. The finite quotient over R/xR is quasi-excellent. These are exactly the hypotheses of the normal-completion lifting input. This yields completions at every prime, and in particular at maximal ideals, without incorrectly assuming B_L already quasi-excellent. L=Frac(R) is included and identifies B_L with R by its definition.

In step 7, I opened the localization-Noetherian and localization-normal-domain statements and the Ratliff criterion. At a prime localization there is exactly one minimal prime, zero; the completed domain has exactly one irreducible component, so its spectrum is equidimensional. Thus Ratliff applies without a hidden equidimensionality hypothesis. This criterion is strictly weaker than excellence. In step 8 I wrote the local-to-global catenarity argument on whole prime intervals, preserving both chain length and saturation; it does not appeal to the definition node for an unstated theorem.

I checked B–E of delivery-errors against every new node: objects and hypotheses are introduced, notions have definition references, TeX uses single mathematical backslashes, source places are exact, no proof is placed in a new statement, and no node merely relocates a clause of the item. The four inputs have wider hypotheses and supply distinct reusable facts. No step exceeds 2000 characters. Full verbatim cited statements are in citations.json, so each citation can be checked against precisely what it supplies. I checked the existing lemma closures for a path back to this item and found none. Small cases include I=0, the unit ideal, fields, identity normalizations, nonzero unit ideals K, finite extensions of degree one, and the prime zero. In particular the normal-completion input does not purport to hold for arbitrary normal rings without the complete-pair and closed-fibre assumptions.

## Unfinished work

The four new nodes are deliberately unsplit and require their own stage-1 work. No part of the item's eight-step assembly is deferred without a named input. No Lean is delivered. Literature integration is requested above.
