# Worker report: lem-per-kummer-etale-local-chart-criterion

Group Q40, stage 1, 2026-10-24. Direct delivery, with self-review and independent maintainer review after delivery.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-kummer-etale-local-chart-criterion.json: statement; split in nine proof steps. Statement, statement dependencies, source and inherited searches preserved. Added five actually executed searches, complete proof dependencies, blueprint explanation and declared generic tool uses. Mathlib verdict: no match.
- citations.json: 27 entries, one for each use in each step; every quotation is a literal substring of the live cited statement.
- report.md: this report. searches.jsonl is the search command's own log; split.py is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: this item is not the unit's statement node.

## Attachments

None. Searched lean/WeilConjectures for the item id, KummerEtale, LogEtale, LogScheme, kummer_etale and log_etale, and inspected the broader Kummer/log keyword results. The project hits concern ordinary Kummer sequences, Tate twists and pro-etale covers, not logarithmic Kummer morphisms or the chart criterion. No eligible declaration states the item.

## WANTED

None for this delivery. The required ILO volume is available locally. The proof is honestly marked agent-written: it assembles existing lemmas into the criterion recalled in ILO rather than claiming ILO prints this nine-step argument. No unavailable text or SGA source is used.

## Findings and changes

The item was an unsplit statement-only node with no sandbox predecessor. There was no repair note for its id. Its statement is mathematically correct and is unchanged. In particular, the invertible annihilator must hold on the target neighbourhood, the comparison need only be etale, chart monoids need not be sharp in the statement, and neither global finiteness nor surjectivity follows or is used.

ILO VI 2.1 gives precisely characteristic Kummerness plus log etaleness; VI 2.2 gives standard Kummer covers and the local standard assertion. XVI 3.6.3--3.6.4 supplies the differential-basis and divisible-unit lattice route. I used the existing prescribed-lattice realization lemma at r=0, rather than creating a node repeating the forward implication. The additional kernel and positive-multiple calculations are written in the item's proof. The converse spells out the passage from chart monoids to characteristic monoids; the two injectivities are not silently identified.

Read the latest blueprint's ancestor lem-per-artin-gabber-affine-curve and its proof, the chapter sec-deligne-laumon-a1, the unit sk-p-dl-a1-perverse, and the item's existing ancestry. The present latest ancestor text has no explicit logarithmic-chart theorem; this node belongs to its existing regular-pair purity refinement. No chapter/unit route is altered. Whole-blueprint searches for Kummer, log etale and lattice chart found no blueprint statement of this item; the original same_as=[] is retained.

## Searches

Ran the mandated msearch command for this item with LeanFinder, Loogle, grep and LeanSearch, and then a second LeanFinder phrasing. Read all returned types. They concern ordinary etale schemes/rings, standard presentations, localizations and number-field unit logarithms. Neither the literal LogEtale search nor AlgebraicGeometry grep found a logarithmic notion. All five services returned successfully, and their exact queries/results are preserved in searches.jsonl and appended to mathlib_searches. Earlier Q24 searches remain untouched. No new nodes require separate searches.

## Not duplicates

No nodes were created. Reused lem-per-very-tame-equivariant-sharp-chart with trivial group instead of introducing a sharp-chart lemma; reused lem-per-log-smooth-differential-generators, lem-per-divisible-unit-lattice-extension and lem-per-kato-lattice-chart-realization instead of making a local Kummer-chart restatement; reused the existing face-localization and sharpening statements for the converse. I opened each statement, not merely its title or its proof. The downstream fs-base-change-stability theorem and the finite strict-local standard-model theorem are not used, so this split does not depend on a consequence or add finiteness hypotheses.

## Review by Q40

I read ILO VI 1.1 (printed p.69), VI 2.1--2.2 (pp.71--72), VI 3.7(a) (p.75), VIII 3.1.1--3.1.2 (p.98), X 1.2 and its proof (pp.136--138), and XVI 3.6.3--3.6.4 (pp.252--253). VI 2.1 is the item's definition and VI 2.2 its local standard model. The XVI proof explicitly constructs the inverse-image monoid in a lattice and an etale comparison; the r=0 specialization is the route used here. The sharp chart in VI 3.7(a) works with the trivial group without log regularity. There are no new-node sources to audit.

Step 1: I checked the full statements of the strict-local-invariance and inverse-image-stalk-germ nodes. The former applies to etale maps as the one-term ind-etale case, and the latter gives the canonical germ formula, so multiplication and the unit subgroup are respected. The log-structure definition gives the associated-log pushout; once the local rings agree, it introduces no new units. The covering-lift node gives a lift with the same geometric field, not just an underlying point. The etale-base-change node gives precisely the source neighbourhood above a chosen target neighbourhood. The affine-shrink and composition nodes give the needed affine etale restrictions. The definition of etale includes local finite presentation, and pqf-lem-locnoeth-lft then preserves local Noetherianness. These generic tools are all declared in split_report.tool_uses where off-unit.

Step 2: I checked that log-smooth-composition explicitly includes log etale implies log smooth. The fs infinitesimal criterion states local finite presentation and unique GLOBAL lifting for all fine strict square-zero test schemes, without requiring their underlying schemes to be Noetherian. The infinitesimal-differential-calculus statement explicitly ends with omega_f=0 under unique global lifting. Thus it supplies the exact vanishing used, not merely local freeness or existence of lifts. Compatible etale localization is allowed in that statement and follows for the criterion from restriction of the chart data. No theorem about the underlying map being etale is asserted.

Step 3: In the equivariant sharp-chart statement I set G=H=1; invertibility of its order and triviality of its characteristic action are then automatic. Its chart has the actual characteristic monoid P at the chosen point. Applied to the source it also makes R sharp fs. The face-sharpening lemma gives free finite-rank group completions for these monoids. Differential-generators applies because the base chart is fixed and torsion-free and the morphism is log smooth; zero differentials force its basis length to be zero. Its statement supplies all three facts used: finite cokernel, an invertible annihilator n, and n-divisible units. I checked the target invertibility carefully: the strict local ring homomorphism is LOCAL, so an integer that becomes a unit in the source is already a unit in the target local ring. Shrinking the target to its unit locus therefore does not discard the chosen point. No flatness or dominance is needed for this reflection of units.

Step 4: The divisible-unit extension lemma is applied to L=P^gp, B=M_x^gp, D=A^times and the exact chart-pullback homomorphism. Its hypotheses are supplied in step 3. Its conclusion gives an injective finite-power-index lattice extension and a map onto B/D. I then proved injectivity of that latter map in the item: a kernel element has a multiple in i(L); characteristic Kummer injectivity kills the corresponding element of L, and freeness of G kills the original element. This argument does not assume the conclusion or use the proof of the lattice-extension node.

Step 5: This is an elementary calculation from the log/unit definition and steps 3--4. A monoid stalk is the inverse image of its characteristic inside its group completion: a lift of a characteristic differs by a unit. Therefore Q is rho^{-1}(R). For q in Q, the positive-multiple condition on P to R and the already proved injectivity of rho yield an equality aq=i(p) in G. This proves a Kummer chart rather than asserting it. Finite generation of the free lattice and an annihilator n^k give finiteness by bounded coefficients; n^k is still invertible on V. The identification of Q^gp with G is explicitly deferred to the existing realization theorem, with no circular use of the Kummer chart conclusion.

Step 6: I reread the entire prescribed-lattice-realization statement. It takes the specified inverse-image monoid and keeps the specified base chart and specified germ. Every hypothesis is present: log smoothness, torsion-free P^gp, empty basis of omega, n a unit at x, G finite free, i injective, the n-power quotient, hi=phi, and surjectivity to the characteristic group. Its conclusion supplies fs Q, the actual inclusion-induced identification Q^gp=G, a compatible chart, and an ETALE comparison to the ordinary scheme fibre product. It does not require log regularity. The proof then affine-shrinks and ranges over all points; it does not claim the original f is finite. This is a use of a more general existing theorem, not a newly created clause of the item.

Step 7: I checked the abelian-group-structure statement gives a finite product of cyclic prime-power factors and a free factor. Finiteness forces the free factor to vanish. Since C is killed by n, every nontrivial prime factor in its order divides n. Units of n on V pull back to units on U. This verifies the ORDER condition of the log-etale definition from the item's ANNIHILATOR condition. Kernel zero has order one. The definition itself quantifies over exactly the given covering chart family, so no additional descent theorem is smuggled in.

Step 8: I read both chart-face-localization-logification and fs-face-sharpening. The first states the exact characteristic R/U formula, not just existence of a chart; the second identifies the group completion with the quotient group and makes it torsion-free. The inverse-unit sets are faces, and local reflection gives h^{-1}(E)=F. A positive multiple of e in E coming from P must come from F, again by reflection of units. Writing a difference and taking a common multiple then handles E^gp. These calculations work when either face is the whole monoid.

Step 9: I checked the quotient injection directly: a class in its kernel has a positive multiple in F^gp; the quotient P^gp/F^gp is torsion-free by step 8, so the class is zero. Every characteristic class of Q_E/E^gp is represented by an element of Q, because the localization denominator is killed in the quotient. Monoid Kummerness therefore gives the required positive-multiple condition. Step 1 covers every geometric point and identifies these localized characteristic maps with f's maps, completing the precise definition in def-per-kummer-log-morphism. Only that definition's first (characteristic) paragraph is used; the separate strict-local standard-chart data in its second paragraph is not used as a theorem.

I checked B--E of delivery-errors.md against the actual files. There are no new nodes to fail the statement-only/self-contained/search/duplicate tests. Every non-elementary step cites existing nodes giving precisely its assertions; citations.json contains only verbatim statement quotations. Steps 5 and 9 are marked elementary because their explicit arguments use only the preceding steps, monoid/group definitions, cancellation, multiples and torsion-freeness. No step exceeds 2000 characters. I checked dependency closures for the significant log-chart inputs: none reaches this item, so no use of its downstream base-change theorem is hidden. No SGA source, Lean change, compiler, Lake tool, local DAG checker or repository git operation was used.

Small cases: the empty source permits an empty family; trivial characteristic P=R=0 gives G=Q=0 and an ordinary etale comparison; n=1 and k=0 give trivial cokernel; P=Q with identity chart gives the strict etale case; the standard root chart N to N by multiplication m works when m is invertible and is correctly excluded when the residue characteristic divides m. Faces equal to all of P or Q give zero characteristics, not a spurious failure of injectivity. Non-sharp charts in the reverse direction are treated by localization at their actual unit faces. None of these tests needs a reduced ring, regular log structure, flat underlying f, finite f or surjective f.

## Unfinished work

No mathematical part remains in this one-level split. The statements of existing cited nodes remain their owners' work. The required server dry run and direct push are recorded by the delivery command.
