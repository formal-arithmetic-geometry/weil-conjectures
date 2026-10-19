# Q62: lem-per-regular-normal-crossings-constant-image

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-normal-crossings-constant-image.json`: statement node, now split into nine proof steps; not a Mathlib leaf. Statement, statement dependencies, provenance and inherited searches retained. Logged searches from the interrupted attempts were read and appended with their actual queries and results.
- `citations.json`: one verbatim statement quotation for each of the 31 step/node citations.
- `report.md`: this report.

There are **0 new nodes and 0 Mathlib leaves**. The root-level saved item copy and `ilo.txt` are retained as interrupted-attempt material; only the node under `dag/nodes/` is the delivery. No Lean file, compiler, Lake or build tool was used, and the shared project and launcher files were not changed.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item tag, normal-crossings names and absolute-purity names returned no declaration giving this statement. The read-only upstream master was also searched for the item tag and normal-crossings names; it is reference material, not evidence of a finished proof.

## WANTED

None. The ILO volume and Stacks source needed here are already available.

## Findings and retained work

The current repository and both saved item copies agree: the item is unsplit and has no proof. There was no saved report or citations file, and no interrupted delivery process remained active. Thus there was no completed split requiring an initial dry run. I retained the statement, source, blueprint ancestry and earlier search log instead of restarting those searches. In particular, the saved Loogle query `R j_* constant etale normal crossings` reports an unknown identifier; I recorded that failed query as unavailable, not as a mathematical no-match result. The inherited item searches remain present, as requested by the resumption brief; searches newly appended to the item are exactly those in its saved `searches.jsonl`. Several distinct natural-language formulations had already been tried. Their hits concern structure sheaves, exterior algebra in ordinary algebra, and general derived-functor machinery; none computes etale higher direct images across a regular boundary.

I read ILO XVI Theorem 3.1.1, Corollary 3.1.3 and its proof (printed pp.242–243), XIII Proposition 3.6.2 (printed p.203), and XV Theorem 2.1.2 (printed p.220). The corollary proves a stronger exterior-algebra description. The item's conclusion needs only constructibility and the component-count degree bound. I give an agent-written divisor-deletion induction from the same absolute-purity input, rather than introducing another node that merely restates that corollary or one of the item's clauses. This is explicitly marked `proof_origin.by: agent`. It stays below the ancestor's regular-boundary finiteness input and changes neither the unit nor the chapter route. No SGA source is used.

The strengthened induction allows disconnected regular closed divisors with transverse regular intersections. Requiring irreducible components at every inductive stage would be a gap: the intersection of one component with another need not be irreducible. Simultaneous induction for all Tate twists also avoids assuming a projection formula without proving its invertible-line case.

There is no statement dispute and no change to the imported statement. In particular, I have not imposed excellence, finite type over a field, separatedness over a base, finite Krull dimension, or a nonempty boundary.

## Not duplicates

No new node was created. I searched the whole DAG for normal-crossings, exterior-algebra, absolute-purity, localization, constructibility and direct-image composition statements, and the whole imported blueprint with `tools/blueprint_refs.py search 'normal crossings'` and `search 'absolute purity'`. Neither blueprint search found a matching blueprint node. The ancestor command confirms `lem-per-artin-gabber-affine-curve`. The existing regular-pair purity node is used directly; the existing finite-pushforward constructibility node is used with its explicit finite-stalk and Noetherian-target hypotheses. I did not create a second copy of either fact. The item's `blueprint.same_as` remains `[]`.

## Review by Q62

I read the chapter `sec-deligne-laumon-a1` and unit `sk-p-dl-a1-perverse` records. This item serves the existing finite-residue-duality/open-immersion-finiteness branch under ancestor Step 3, rather than being the unit's key statement, so no unit realization fields need changing. I compared the nine steps against delivery-errors B–E, the ILO source just listed, and the actual statement of every cited node. Each citation's whole statement is copied verbatim into `citations.json`, so its coefficient category and hypotheses are visible to the reviewer.

Step 1 uses the definition of strict normal crossings only for the finite regular-intersection family and dimension equalities it actually supplies. The Tate-line lemma states local rank-one freeness, so the empty-family base case is a constructible degree-zero sheaf. The direct-image definition supplies bounded-below injective resolutions and hence no negative higher direct images. I strengthened the induction to disconnected regular divisors, empty intersections and every integer twist; I did not add these as new lemma nodes because this is the induction proposition being proved here.

Step 2 uses the actual derived adjunction and monoidal inverse-image statements, not invertibility of the projection map asserted by its definition. I wrote out the four Hom identifications for an invertible Tate line. The local rank-one calculation supplies its inverse, and the identity-correspondence argument supplies mutually inverse derived maps. This is a formal few-line adjunction calculation, marked elementary. It does not invoke a general proper projection formula or silently change to pro-etale coefficients.

Step 3 checks codimension one and the regular-immersion hypothesis using the regular-lci geometric-calculus statement, then applies the existing Gabber regular-pair theorem with n=1 and c=1. That theorem explicitly has no excellence assumption. The identity-open compactification of a closed immersion identifies Ri_! with Ri_*; finite exactness and the module/abelian comparison identify its bounded-below value with termwise i_*. Thus the right adjoint in the purity theorem and in the localization triangle is the same right adjoint. I wrote out the second Hom calculation that carries the purity isomorphism from A to A(t), rather than assuming a general exceptional tensor formula. Both its source and target Tate lines are identified by the cited Tate-line lemma. The empty closed subscheme gives zero and needs no codimension assertion at a nonexistent point.

Step 4 is the explicit inductive geometry. On V and E the local rings are the corresponding local rings of X and C, so regularity and Noetherianity hold. On C, the indexed intersection with J is exactly C_{J union {m}}. Subtracting the two displayed local-dimension identities gives codimension |J|, so the induction applies with m-1 even when intersections split into several components. The regular-lci node states precisely the regularity-of-immersion fact used here. No quasi-excellence or affine hypothesis is introduced.

Step 5 uses the actual statement of the ordinary unbounded etale closed-support triangle, which allows every finite coefficient ring and every derived input. Its support term is the regular single divisor E in V, not the singular union. The preceding calculation therefore supplies A_E(t-1)[-2] with the correct cohomological sign.

Step 6 uses triangulatedness of the right derived functor and the existing ringed-topos composition theorem twice, for vb=u and va=ik. I read Stacks sites-cohomology.tex Tag 0D6E, `lemma-derived-pushforward-composition`, and inspected the recorded source project's triangulated right-derived instances at lines 94–99. Constant A-coefficients and small representatives of the etale sites satisfy that theorem's ringed-site assumptions. The finite exactness statements used to replace Ra_* and Ri_* are cited in this step as well as explained in step 7.

Step 7 checks a common citation trap: the finite-pushforward exactness node is for abelian sheaves, so I also cite the higher-direct-image forgetting comparison for arbitrary commutative coefficients and all degrees. This gives the corresponding module assertion without pretending the abelian statement already said it. The finite-pushforward constructibility node has no finite-type-over-a-field or excellence requirement; it requires Noetherian target, source-library constructibility and finite geometric stalks. All three hold: the target is X, the existing comparison node converts the constructibility notions, and A is finite. I read Stacks etale-cohomology.tex Tag 095R, `lemma-finite-pushforward-constructible`; over the present Noetherian targets the closed immersions are finite and finitely presented. No use is made of the narrower `lem-fin-finite-morphism`, whose target hypothesis would not fit this item.

Step 8 uses exactly the cohomology long exact sequence of a distinguished triangle and exactly the kernels/cokernels/extensions clauses of `thm-constructible-serre`. The shift [-2] places the first term in [2,m+1], and the connecting arrow involves its cohomology in degree q+1, namely i_*H^{q-1}(Rk_*A(t-1)); consequently q>m kills both neighbors of the middle sheaf. I checked the shift on m=1: the possible boundary cohomology is degree 1, not degree 2. I specified the image as a cokernel and the quotient as a kernel before using extension closure, rather than citing only a definition of constructibility.

Step 9 uses the same forgetting comparison for both coefficient rings. Since B is finite free of dimension d over A, its underlying abelian constant sheaf is a finite biproduct of d copies of A, and the additive derived abelian direct image preserves that finite biproduct. I do not claim a change-of-rings theorem from a node stated only for proper maps. The module-local-constancy lemma upgrades finite locally constant underlying sets on each stratum to locally constant B-module sheaves; finiteness of their sets supplies finite module values. Thus the constructibility definition applies with B and the degree bound is unchanged.

Small cases checked: empty ambient scheme; empty boundary r=0; one regular divisor; disjoint divisors (empty intersections contribute zero); two transverse divisors; disconnected intersections on one component; B=A; and a proper finite field extension B/A. The argument never uses Krull dimension boundedness: the uniform bound is the finite number r of boundary components. Each proof step is below 2000 characters. No hidden long-step lemma, new statement-only restatement, hollow definition, unlogged new-node Mathlib search, or statement change remains. The local read-only dependency-closure scan found no path from any cited node back to this item. Off-unit foundational tools are declared individually in `split_report.tool_uses`; no `tool_uses` field is set by this delivery.

## Unfinished work

None in the mathematical split. The required server dry run and direct delivery are the remaining packaging operations; their results will be recorded below.
