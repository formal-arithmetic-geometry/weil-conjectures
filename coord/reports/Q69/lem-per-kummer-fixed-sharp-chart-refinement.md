## Worker report

Item: lem-per-kummer-fixed-sharp-chart-refinement. Group Q69. Stage 1 only, 2026-10-24.

Files written: dag/nodes/sec-deligne-laumon-a1/lem-per-kummer-fixed-sharp-chart-refinement.json (statement, split, no Mathlib match), citations.json, this report. No new DAG nodes, Mathlib leaves, Lean files, compilation, repository writes or manual git commands. The sandbox initially contained only dispatcher brief markers; there was no earlier split or report to recover.

Attachments: none. Searches in lean/WeilConjectures for the blueprint tag and for logarithmic etaleness, sharp charts and Kummer charts found no declaration of this theorem. Ordinary Kummer field theory and coefficient-sheaf declarations have different objects.

WANTED: Kato, Logarithmic structures of Fontaine--Illusie (1988), section 3, especially Theorem 3.5 and the infinitesimal criterion, for the primary source underlying the existing chart-realization and differential-calculus nodes. This document is not present locally. The split reads ILO's explicit reconstruction and cites the existing nodes for the missing primary inputs; it is marked agent-written.
WANTED: Stix (2002), 3.1.4, cited by ILO VI 2.2 for the standard-cover assertion. The present proof does not use that assertion as a black box: it follows the lattice construction spelled out in ILO XVI 3.6.3--3.6.4.

The item's statement is unchanged and is consistent with the cited source's intent. The original source entry mentioned the standard-cover statement and sharp-chart splitting but did not identify the prescribed-base-chart construction. I refined its source place to include ILO XVI Proposition 3.6.3 and Lemma 3.6.4, pp.252--253. The new proof keeps the base chart's actual log germ throughout the lattice extension, rather than inferring a fixed-chart conclusion from an unspecified standard chart. There is no statement dispute.

Nothing mathematical is left unfinished in this one-level split: its seven proof steps use existing nodes, and the algebra that additionally makes the chart sharp is written out. The supporting nodes remain responsible for their own proofs.

## New nodes

None. In particular, the characteristic-group injectivity argument and the finite-exponent quotient calculation are elementary steps, not new lemmas, and no clause of the item was repackaged into a new node.

## Searches and blueprint provenance

Read the chapter and unit records, the three-level rule in SETUP.md, GOAL.md, the worker brief, stages/1-dag.md and delivery-errors B--E. Read the current literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.md. The latest ancestor contains the affine perverse estimate statement, without a proof section; its older inherited geometry is described in the existing from.place chain. I have not changed the chapter, unit or that ancestry.

Whole-DAG searches for sharp charts, Kummer charts, Stix and lattice constructions found the already split local-chart criterion, lattice realization, divisible-unit extension, characteristic differential generators and fs-face sharpening nodes. Opened their statements and checked dependency reachability; none leads back to this item. The local-chart criterion itself does not prescribe the given base chart or require sharp chart monoids, so it alone would not discharge the item. Its proof supplied a useful comparison with the present construction, but every theorem used here is cited by its statement, not by that proof.

Ran tools/blueprint_refs.py ancestor for the item and search for 'sharp chart', 'prescribed', and 'Kummer' across the whole blueprint. There is no equivalent logarithmic sharp prescribed-chart statement: 'sharp chart' had zero hits, and the other imported hits concern coefficient Kummer theory, purity or unrelated prescribed data. Thus same_as remains []. No new node needed a duplicate or same-tag comparison.

Ran the required msearch command for leanfinder, loogle, grep and leansearch, then a second semantic leanfinder phrasing. Read all returned types: standard etale algebras/schemes, manifold atlases and number-field unit lattices do not state this logarithmic chart theorem. Loogle and source grep had no hits. The exact queries/results are appended to mathlib_searches and are in searches.jsonl; the imported earlier search records are retained. No query was invented or silently recorded as unavailable.

## Not duplicates

No new nodes; no new/existing same-tag pair. Existing supporting results are reused directly.

## Review by Q69

I read ILO VI 2.2--2.3 (printed pp.72--73), VI 3.7(a) (p.75), X Proposition 1.2 and its proof (pp.136--138), and XVI Proposition 3.6.3 and Lemma 3.6.4 with its proof (pp.252--253). The latter explicitly begins with a prescribed torsion-free base chart, forms the auxiliary lattice extending its actual map into the log group, and uses the inverse image of the log monoid. This supports the proof route without assuming log regularity or finiteness. The sharpness conclusion is the additional Kummer argument in steps 4--5, not an assertion that ILO's general log-smooth chart is automatically sharp. No SGA source was used.

Step 1 uses lem-per-log-smooth-composition-strict-base-change precisely for log etale implies log smooth, lem-per-fs-log-infinitesimal-criterion for local finite presentation and unique global strict square-zero lifts, and lem-per-infinitesimal-log-differential-calculus for unique lifts imply zero logarithmic differentials. I checked that the tests are fine log schemes on arbitrary underlying schemes in both statements, and that compatible etale localization is permitted. Formal smoothness alone would not give the zero differential conclusion.

Step 2 uses lem-per-very-tame-equivariant-sharp-chart with the trivial group solely to identify the characteristic as sharp fs. No equivariance hypothesis remains, since the group has order one. The statement of lem-trf-fs-face-sharpening gives finite free group completions after sharpening; its unit-face specialization is applicable to both sharp monoids. The statement of lem-per-log-smooth-differential-generators supplies the differential basis, finite characteristic cokernel killed by a local unit integer, and divisibility of the unit group. Its prescribed chart hypothesis is exactly the chart a in the item, and rank zero follows from step 1. This checks all hypotheses of the next step, rather than assuming general divisibility of all units.

Step 3 applies the full statement of lem-per-divisible-unit-lattice-extension (ILO XVI 3.6.4). L is finite free, E/D is torsion-free, D is n-divisible and the characteristic cokernel is finite killed by n. The lemma extends the original map, not just its characteristic quotient. I checked its statement supplies an injective lattice map and a power of n killing its cokernel, but only a surjection onto the characteristic group: injectivity of that last map must still be proved.

Step 4 supplies that missing injectivity explicitly. Multiplying an element in its kernel into i(L) reduces to injectivity of the characteristic group map, which follows from the integral monoid Kummer injection in def-per-kummer-log-morphism. The free auxiliary group has no integer torsion. I read def-trf-fs-log-blowup for the log monoid, units, characteristic and integral/fs chart conventions: belonging to the stalk monoid is equivalent to having characteristic in the sharp monoid, because a residual unit can always be multiplied in. This proves Q equals the inverse image of R under an isomorphism, not merely under a surjection. It proves sharpness and the characteristic identification with a short algebraic argument; no new node is justified.

Step 5 uses the positive-multiple clause of def-per-kummer-log-morphism and the isomorphism of step 4 to obtain actual equality dq=i(p) in G, not equality only modulo units. The finite-cokernel argument is also written: a finite basis of G gives finitely many coefficient residues modulo n^k. It does not assert a finite-exponent group is finite without finite generation. Both steps 4 and 5 are elementary consequences of already supplied statements and definitions.

Step 6 uses lem-per-kato-lattice-chart-realization, whose statement explicitly realizes the prescribed inverse-image monoid and prescribed germ without changing the base chart. I checked each binder with its names exchanged: base monoid P, r=0, lift s, injection i and integer n. The statement gives compatibility through this very injection and etale comparison, not just a stalk chart. The characteristic map of the resulting chart is rho restricted to Q, already an isomorphism. Thus the equality required in the item is equality of log sections.

Step 7 uses lem-weil-pbc-etale-composition-cancellation for the open immersion U to be etale, and lem-weil-pbc-etale-scheme-base-change twice, once for W over X times_Y U and once for the scheme comparison. Both are existing Mathlib leaves (Stacks base change Tag 02GO; open immersion Tag 02GT). Invertibility descends from the source stalk to the target stalk because that ring map is local, and the inverse germ is represented on an open; no dominance or flatness is used. Restriction along this open leaves the chosen geometric germs unchanged. This also checks the potentially important distinction between W etale over the relative source and the desired comparison etale over the monoid-ring base change.

Small cases checked: trivial log structures give P=R=Q=0 and ordinary etale neighbourhoods; the identity map has zero cokernel and n=1; a root chart N to N by multiplication by d invertible at the point has characteristic cokernel Z/d, and the lattice construction recovers the standard sharp root chart, including unit twists via the divisible-unit extension. In residue characteristic p a p-root chart is not log etale, so it cannot incorrectly pass the empty-differential and invertible-cokernel inputs. No reducedness, regularity, finite underlying map, or flatness has entered. An empty source has no geometric point, so the pointed implication is vacuous. All seven steps are shorter than 2000 characters; no long step conceals an unnamed comparison lemma.

The sole off-unit non-leaf citation is lem-trf-fs-face-sharpening, used as general monoid algebra to obtain finite free characteristic groups. It is declared in split_report.tool_uses for the maintainer's review; no top-level maintainer field is written. It does not replace the unit's geometric route. Every step/node pair has a verbatim statement extract in citations.json. New-node field, definition, Mathlib match and Stacks-tag duplication requirements are vacuous because no nodes are created. The original statement and all import/provenance fields are retained; no cited node has been edited.

Dry-run repair: the citation gate requested a longer extract for the log-etale-implies-log-smooth input. Expanded that quote to its complete supporting sentence; no proof or statement change was needed.
