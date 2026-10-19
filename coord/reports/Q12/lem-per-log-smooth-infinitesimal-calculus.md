# Stage 1 report: lem-per-log-smooth-infinitesimal-calculus

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-log-smooth-infinitesimal-calculus.json: repaired split; its statement is byte-identical to main and the returned N4 statement.
- dag/nodes/sec-deligne-laumon-a1/lem-per-compatible-abelian-group-lifting.json: new statement-only unsplit group lemma; Mathlib verdict: no match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-strict-smooth-log-differential-sequence.json: new statement-only unsplit strict smooth differential sequence, with its strict etale case; Mathlib verdict: no match.
- citations.json: exact statement quotes for all proof citations.
- report.md: this report. The previous report is retained in scratch/report-before-repair.md; all earlier searches remain in searches.jsonl together with the new searches.

## Attachments

None. I searched the read-only slopmaster2 WeilConjectures/ for the item id, blueprint tag, log schemes, logarithmic differentials and group lifting. No project declaration states this item or either new lemma. The read-only master source's logarithmic derivatives concern zeta series. No Lean was written or compiled.

## WANTED

WANTED: Kato, Logarithmic structures of Fontaine--Illusie (1988), section 3, Theorem 3.5 and logarithmic differentials/transitivity around 3.12, for this item and both new nodes.

I read ILO XVI Proposition 3.6.3, printed p.252, which invokes Kato 3.5, and ILO X Proposition 1.2, printed pp.136–138, especially the strict comparison and differential calculation at p.138. Kato is absent from the local literature catalog. Neither new general lemma is stated verbatim in ILO; their source fields explicitly say this. The item's expanded proof is agent-written. No unavailable proof is represented as a transcription, and no SGA source is used.

## Returned faults repaired

The retained dry run first exited successfully at 32f7fd878c; this did not repair its mathematics. I compared the retained sandbox with current main: the statement agrees exactly, while main still has an unsplit record. I retained provenance, searches, blueprint ancestry and the accepted derivation/action/difference/torsor arguments, replacing defective Steps 1–4 with the expanded chart proof. There are now thirteen steps; no unit or chapter route changed.

1. Old Step 4 (E3/E5/D5): new Steps 6–8 prove group exactness and the cartesian monoid identity, solve the group diagram using both invertible orders, put the Q-image in L and spread it to a neighborhood. Its structure map then gives T→W. Only now is smooth lifting along c applied, followed by logification. The group lemma is an independent compatible extension problem, not a restatement of log-smooth lifting.
2. Old Step 1 (C1): Steps 1–2 cite algebraic finite-presentation base change, the affine fibre-product formula and fppf-source locality (Tag 036N). Composition through etale B_i→Y and descent through V_i→X are explicit.
3. Old Step 2 (E5/C1): Step 3 computes ω_{W/B}=O_W⊗C with both generator maps and kills C_tors after pullback to V, where its order is a unit. Step 4 uses an actual locally split short exact sequence, including left injectivity, and ordinary smooth finite locally free differentials.
4. Old Step 3 (C4): the etaleness-descent citation is removed. Step 13 uses actual differential identifications, lfp descent, and formal etaleness/thickening-site invariance for localization of lifts.

Old Steps 5–8 are retained as Steps 9–12, with alpha compatibility displayed in Step 10. The free/transitive action deduction is elementary. There is no statement dispute: the proof was wrong, not the N4 statement.

## Searches and new inputs

I searched the whole DAG by notions, source places and statements, and used blueprint_refs.py search for abelian group, compatible lifting, strict smooth, logarithmic differential and logarithmic differentials. Specific searches found no blueprint match. I read the nearby differential local-freeness/generator, strict Jacobian, equivariant chart and lattice realization nodes. They state different results or depend on this item.

All Mathlib searches ran through msearch.py and are recorded as logged. The retained second group-lifting phrasing was reused. AddMonoidHom.liftOfSurjective descends an existing map vanishing on a kernel; it does not solve this extension problem. Module.Baer.extension_property_addMonoidHom, read at Mathlib/Algebra/Module/Injective.lean:392, requires injective/Baer coefficients, not merely invertibility of two integers. Ordinary Kaehler exactness and the formally etale tensor equivalence, read at Mathlib/RingTheory/Etale/Kaehler.lean:38, do not concern log structures. The lone logarithmic grep hit concerns field-theoretic logarithmic derivatives; its header was read. Neither new statement is a one-line Mathlib specialization.

The new nodes carry statements only. For the future workers, the arguments behind their formulation are:

**Group lifting.** Set H=B×_{E_0}E and U=u(A). The map a kills K because a(K)⊂J is annihilated by |K| and multiplication by |K| is injective on J. It therefore gives a section s:U→H. Its image meets J trivially, and quotienting gives an extension 0→J→H/s(U)→C→0. Decompose the finitely generated C into free and finite cyclic summands. Lift free generators freely. For a cyclic generator of order d dividing |C_tors|, choose a lift x; dx∈J has a unique d-division y∈J, so replace x by x−y. This splits the extension. Equivalently Ext¹(C_tors,J)=0 and the free quotient is projective. The preimage in H of the splitting's image maps isomorphically to B: kernel in J is zero, and any lift can be adjusted by J to enter it. Its inverse gives the section extending s and hence b:B→E. This uses both orders without assuming J divisible by every integer.

**Differential sequence.** For a strict morphism, relative log differentials equal ordinary relative differentials: extra log sections are pulled-back sections times units, with dlog v=v^{-1}dv. Quotienting the absolute log presentation by target symbols gives right exact transitivity. For left injectivity, on an affine strict smooth chart A→B set J=B⊗_A ω_{W/S}. The universal derivation gives A→B⊕J, a↦(a,1⊗da). Formal smoothness extends it to B→B⊕J reducing to id_B. Strictness extends the log component by the pulled-back M and the unit formula v^{-1}D(v). This is a retraction of the left arrow, proving injectivity. Smoothness makes Ω_{B/A} finite projective locally, giving the local splitting. For strict etale c, formal etaleness and Ω_{B/A}=0 give the canonical isomorphism. The arbitrary map g need not be log smooth; the lemma neither restates the item nor invokes its lifting property.

## Not duplicates

lem-per-compatible-abelian-group-lifting vs lem-per-integral-monoid-unit-pushout: embedding a monoid pushout into its group completion does not solve a prescribed group diagram through E→E_0.

lem-per-compatible-abelian-group-lifting vs lem-per-integral-chart-logification-thickening: the existing node gives thickening fibres/kernel, not a compatible extension from P^gp to Q^gp.

lem-per-compatible-abelian-group-lifting vs lem-per-divisible-unit-lattice-extension: the existing node enlarges a free lattice mapping into a group modulo a divisible subgroup; the new node keeps a prescribed A→B fixed.

lem-per-strict-smooth-log-differential-sequence vs lem-per-log-smooth-differential-local-freeness: free stalks for a chart-log-smooth map differ from a split transitivity sequence for a strict smooth comparison over an arbitrary fine log base; the existing node depends on the item.

lem-per-strict-smooth-log-differential-sequence vs lem-per-log-smooth-differential-generators: choosing a log basis and characteristic cokernel does not supply an injective left arrow and split sequence.

lem-per-strict-smooth-log-differential-sequence vs lem-per-strict-log-jacobian-criterion: the existing node infers smoothness from a residue-field injection between log-smooth objects; the new lemma assumes strict ordinary smoothness and gives transitivity.

lem-per-strict-smooth-log-differential-sequence vs lem-trf-formally-etale-differentials-base-change: ordinary ring differentials with vanishing cotangent data differ from logarithmic sheaves with a possibly nonzero smooth relative quotient.

## Review by Q12

I read the ILO sources above, the item, both new statements, and every cited statement. I distinguished indirect source references from the agent-formulated lemmas and tested their arguments. Citations.json quotes actual statements, never a fact merely from their proofs. My checks by repaired step are:

1. The monoid statement supplies finite congruence relations. I wrote their binomial algebra presentation and the P-generator equations. Algebraic base change supplies finite presentation of R′⊗_R S, and the fibre-product statement identifies this tensor algebra with W. The lfp definition is precisely the affine finite-equations criterion. Chart monoids are finitely generated.
2. Smoothness includes lfp and etaleness includes flatness and lfp. The composition statement supplies exactly lfp stability. The source-locality statement applies to jointly surjective flat lfp V_i→X without quasi-compactness.
3. Logification supplies the associated structure and universal property. The chart statement supplies invertibility on V, not W. The finitely generated abelian group structure theorem supplies C's free/torsion decomposition. Both differential maps and the monomial derivative formula are written out; invertible annihilation kills O_V⊗C_tors.
4. The new differential lemma supplies left injectivity and local splitting. The ordinary smooth-differential statement gives finite local freeness of Ω_{V/W}. Strictness follows from the same Q-chart on source and target. No downstream log-freeness result is used.
5. Etale base change applies to arbitrary schemes. I²=0 makes the immersion a thickening, so site invariance applies. The flat-unramified statement gives unique affine first-order lifts without Noetherian hypotheses. The etale base neighborhood has those hypotheses, and logification supplies its strict log extension.
6. Strict integral-chart fibres are nonempty free/transitive unit torsors. A fine chart on T and strictness identify L_0 with the reduced logification. I derived group exactness and the cartesian monoid identity from these fibres. The first-order definition gives I²=0.
7. The new group statement gives exactly hu=a and πh=b_0. The chart statement supplies finite K and C_tors with invertible orders on V. Pullback and lifting an inverse modulo I make their orders units on T, hence automorphisms of I. Step 6 then forces h(Q)⊂L.
8. Finite relations come from monoid presentation. The geometric stalk is a neighborhood colimit, and the cofiltered-neighborhood statement allows finitely many equations on a common refinement. The chart definition identifies W and c. Only after α_Lh gives T→W does the smooth definition apply. Logification then yields the compatible log map, with compatibility on P already proved.
9. The retained presentation argument matches every ω relation with a derivation identity. Pullback scalars act through a_0; I is an O_{T_0}-module because I²=0.
10. The strict-chart statement gives multiplication by units on the log sheaf. Square zero kills cross terms. I checked product expansions and the explicit alpha-compatibility identity.
11. Strict-chart fibres give the unique ratio in 1+I. Ring subtraction gives Leibniz modulo I², and structural compatibility gives D(α(m))=a_0^*(α(m))δ(m).
12. The constructions are inverse on ring and log sections. Unique difference for every pair proves freeness/transitivity on each open with a lift, using only the square-zero structure.
13. The new differential statement gives the strict etale source identification. Ordinary Kaehler base change gives the tensor identification for arbitrary base rings; tensor right exactness preserves the extra log presentation. Logification supplies unit relations. Algebraic finite-presentation base change and fppf-source locality really give lfp conclusions. Formal etaleness gives unique lifted source maps; thickening-site invariance and composition of covers give the cover assertions. No citation here merely descends etaleness.

I checked small cases. Trivial log structures give ordinary smooth calculus. Identity maps have rank zero and one lift. For tame Kummer u:Z→Z, u(1)=n with n invertible, K=0 and C_tors=Z/n, the chart tensor term vanishes and group lifting applies. For n=p in characteristic p, multiplication on I need not be invertible: every possible e(1+a epsilon) has pth power e^p, never e^p(1+epsilon). The repaired proof therefore fails its group hypothesis on the returned counterexample. The kernel assumption is necessary too: u:Z/p→0, J=E=Z/p, E_0=0 and a=id gives a compatible diagram with no extension to 0, while multiplication by |K| is not injective. Zero groups/ranks are allowed. No Noetherian assumption was added on T.

I checked delivery-errors B–E against these files: the new inputs are self-contained statement-only lemmas with real searches and blueprint ancestry; citations supply the facts used; there is no downstream cycle, relabelled item clause or SGA source. Every step is under 2000 characters, and I inspected even these shorter steps for hidden comparisons, isolating the two genuine lemmas. Off-unit generic tools are declared in split_report.tool_uses. The server check_dag on the repair reports no finding introduced by the sandbox or on its nodes.

## What remains unfinished

The initial resumed dry run found that the group lemma cited no definition node. I repaired this by identifying finitely generated abelian groups with finitely generated integer modules and citing def-weil-finitely-generated-module, whose statement I read. The lemma already defines exactness, its torsion subgroup, and the integer automorphism condition explicitly. I updated the Step 7 quotation to the revised statement. On resuming I reread ILO XVI 3.6.3 at printed p.252 and X 1.2 at pp.136–138, all 23 proof-dependency statements, and both new statements. I checked the group extension argument in the report: after splitting H/s(U) over C, its inverse-image subgroup maps bijectively to B, giving the required compatible lift. The strict smooth differential input assumes ordinary smoothness, so it does not invoke this item circularly.

The two new lemmas are intentionally unsplit stage-1 queue items, with statements, logged searches and prospective arguments above. Kato remains WANTED. No Lean proof is claimed. Final dry-run and push results are reported by the delivery tool.
