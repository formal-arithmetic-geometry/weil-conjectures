# Q138: lem-per-regular-log-smooth-monomial-chart

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-regular-log-smooth-monomial-chart.json`: split into eleven proof steps, using existing nodes only. Mathlib searches give no match for the item. The statement is unchanged.
- `citations.json`: a verbatim statement quotation for every cited node in every step.
- No new nodes, no new Mathlib leaves, no unit edits. `searches.jsonl` preserves the five searches run with msearch.py; `ilo-text.txt` is a sandbox-only text extraction of the source, and `write_split.py` regenerates the item and citations.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for log-smoothness, monomial charts, and regular logarithmic characteristic monoids. There is no project declaration giving this statement. The ordinary polynomial and standard-smooth declarations found by Mathlib search do not give the logarithmic chart argument.

## WANTED

None for this split. The proof and the results used in it are stated in the local ILO volume and the local Stacks sources. I did not use SGA.

## Findings and changes

The initial item was statement-only. It is a faithful expanded version of ILO XVI Proposition 3.6.5, p.253. I retained it, including arbitrary points, an arbitrary prescribed uniformizer, zero exponents, and affine regular Noetherian neighbourhoods. No statement dispute was needed. In particular the regularity assumption concerns the underlying scheme, not a free initial chart monoid.

The nearest blueprint ancestor is `lem-per-artin-gabber-affine-curve`. I read its current statement and proof in `literature/blueprint/latest/` (main-20261024), the chapter record, and unit `sk-p-dl-a1-perverse`. The present item is the previously extracted regular local-model input below that ancestor's Step 3 duality route, through its recorded ancestry. This split follows precisely the ILO route already fixed for this input; it changes no chapter or unit argument. Searches with blueprint_refs.py for monomial chart, log regular, characteristic monoid, regular characteristic and 3.6.5 gave no blueprint node stating this item. Full-DAG statement searches found existing nodes for every substantial ingredient, including `lem-trf-free-characteristic-regular-boundary`, which is stronger than the pointwise criterion needed here. I reused them.

The source's sentence choosing nonnegative torus coordinates is made explicit by reversing the signs of basis vectors. Its final map is explained by a Laurent-monomial ring calculation: it factors through the open where all torus variables are invertible. The vector of exponents cannot be zero because the original injection of N remains injective in the monoid group completion. This addresses the case of a point in the generic fibre, where the sharp characteristic is zero but the unit-group factor still contains the nonzero image of 1.

## Not duplicates

No new nodes. The potentially new chart, face-localization, splitting, regular-characteristic and regular-ascent facts are already existing nodes, and I cite them directly.

## Review by Q138

I read the proof of ILO XVI Proposition 3.6.5 on printed p.253 in full, including its appeal to Proposition 3.6.3 on p.252, and VI 1.2 and 1.7--1.8 on pp.69--70. These are respectively the strengthened chart, the free-characteristic criterion, and preservation of log regularity. I also read the statements of every node cited by the eleven steps, and the Stacks statements 06LJ, 06LK, 04GP(4) and 07NF in the local .tex sources. I corrected the source labels in the proof metadata to 04GP (`lemma-strict-henselization`) and 07NF (`lemma-regular-goes-up`).

Step 1 uses strict-henselization Noetherianity and dimension, and the maximal-ideal statement, for the two local rings of the trait. At the closed point the nonunit ideal is (pi), the characteristic is N, and the stratum is a field, so dimension is 0+1. At the generic point the log structure is trivial and dimension is 0. Thus the target really satisfies the definition of log regularity used by the preservation theorem; this is not an extra assumption on the trait.

Step 2 applies `lem-per-log-smooth-invertible-torsion-log-regular`, which permits exactly the finite invertible torsion allowed here, rather than applying the older torsion-free-cokernel version. It then applies only the pointwise equivalence in `lem-trf-free-characteristic-regular-boundary`. Its locally Noetherian fs and log-regular hypotheses have just been verified, and ordinary regularity is the item's assumption. The algebraic-closure and geometric-point statements justify choosing a lift over the original point x.

Step 3 now uses `lem-per-log-smooth-differential-generators` directly. I read its entire statement against XVI 3.6.3: it accepts a fixed torsion-free fs base chart and chart-defined log smoothness. The canonical chart N has group completion Z, so it meets that hypothesis. The conclusion supplies a logarithmic differential basis, a positive integer m invertible in the geometric local ring, torsion-freeness of the characteristic group C, m-divisibility of the unit subgroup D, and the finite cokernel killed by m for L → C. It does not falsely assert finite cokernel for L → B.

Step 4 uses `lem-per-divisible-unit-lattice-extension`, the statement of XVI 3.6.4. I read its subgroup and quotient hypotheses and checked all of them against Step 3, with n=m and L=Z^d⊕Z. It supplies an actual finite free G and the maps i and h, with h extending the prescribed map, G/i(L) killed by a power of m, and surjectivity onto C. No injectivity of the initial map to B or C is assumed.

Step 5 applies `lem-per-kato-lattice-chart-realization` with exactly that differential basis and those maps. I read its full statement: the base chart is prescribed, P is the inverse image under h of the log monoid, P is fs, P^gp is G, and the comparison is etale. Thus the major Kato chart-realization argument is a cited theorem, not an inline assertion. Every hypothesis comes from Step 3 or 4 or the stated log-smooth morphism. Its pointed neighbourhood already lifts the geometric point, so the former extra geometric-point-lifting citation is removed. The restriction-stalk and strict-local-invariance statements identify its characteristic with N^r from Step 2. The original uniformizer remains fixed, and injectivity of N→P follows by restriction of i.

Step 6 takes from the localized-chart theorem the face, its local group completion and the identification with the characteristic. The face-sharpening statement supplies exactly the fs localization, the unit group, and finite free group completion of the sharpening. Step 7 inverts the finite face generators on the actual chart. The proof that these generate the face is written out. The localization identity is checked by the universal property, and the etaleness is justified using the existing composition/cancellation node. This is an elementary calculation, not an unnamed logarithmic theorem.

Step 8 uses the monoid splitting theorem with sharpening N^r. It does not claim that all fs monoids are free. The original P has torsion-free group completion by Step 5 and finite generators by fs; the existing finite-abelian-group structure theorem and subgroup theorem give a finite basis for H. Step 9 changes signs of that basis independently and proves the nonzero exponent condition from the injection, with no residue-characteristic assumption and allowing r=0 or s=0.

Step 10 writes both ring universal properties, so the comparison target is really the Laurent open of the displayed monomial hypersurface. The affine fibre-product theorem gives the tensor algebra, and the comparison and the open immersion are etale by the composition theorem. Step 11 uses the affine-shrinking node at the specified geometric point and restricts to the inverse image of a regular Noetherian affine open in X. The etale map to that affine is smooth by the cited smooth-morphism definition; its explicit affine-local smooth-ring interpretation permits the regular-ring smooth-ascent theorem. Thus U is Noetherian and regular, not merely an arbitrary affine chart.

Small cases checked: X empty (vacuous), X=S with its canonical log structure (one exponent 1), a chart on the generic fibre (r=0, a nonzero torus exponent), zero exponents (ordinary polynomial variables), a chart without torus factors (s=0), and different uniformizers (the fixed chart theorem starts from the prescribed pi). No source claim or cited node requires excellence, henselianity of R, perfect residue field, or positive exponents in all coordinates. No new self-contained statement has been introduced, and no item clause has been moved to a new node. Every step is below 2000 characters; the monoid/ring calculations each have their maps and inverse universal-property descriptions in the step itself.

The off-unit citations declared in split_report.tool_uses are generic log-chart and local-algebra inputs. They supply no trace, duality, or perverse result; the perverse unit has no substitute for these algebraic inputs. A source-only transitive dependency scan confirmed that the major cited existing nodes do not depend on this item. The server's check_dag and review_split are the required final validation.

## Returned-route repair, 2026-10-24

The returned head is 4720dcd3c23. The current read clone has the N0-reopened statement-only item. I compared all its fields with the retained packet: the statement, source, statement dependencies, and blueprint provenance agree exactly; the retained split and additional logged Mathlib searches are preserved. I reread the return, `coord/changes/20261024-N0-log-smooth-purity-inputs.md`, and the released repair note. N0 re-admits only this item and two other exact interfaces, not its old proof graph.

The return is correct: the former Step 3 introduced `lem-per-trait-log-smooth-uniformizer-chart`, still excluded at line 1951 of `coord/route-pivot-dropped.txt`. I removed its citation and dependency. I did not restore that node, create a duplicate alias, edit route metadata, or inline the major Kato theorem. Instead the former application has been replaced by three separately justified steps, applying the existing differential-generator, lattice-extension and prescribed-chart-realization statements. I reread XVI 3.6.3–3.6.4 on pp.252–253 for this reconstruction. These are genuine subsidiary inputs with their own hypotheses; they do not restate the monomial-chart conclusion. Each new step is under 1100 characters.

The four directly cited nodes below remain in the dropped list, so their presence requires an explicit explanation. Each is already reached independently of this item's proof through the sfb-Gabber exception that the return accepts for Step 2. Their existing paths are:

- `lem-sfb-field-log-smooth-gabber-modification` → `lem-per-gabber-abelian-stage-toric-chart` → `lem-per-log-smooth-invertible-torsion-log-regular` (Step 2; dropped line 1698).
- `lem-sfb-field-log-smooth-gabber-modification` → `lem-per-gabber-absolute-equivariant-modification` → `lem-per-kummer-boundary-restriction` → `lem-per-kummer-strict-local-standard-model` → `lem-per-kummer-fixed-sharp-chart-refinement` → `lem-per-log-smooth-differential-generators` (Step 3).
- The same path through `lem-per-kummer-fixed-sharp-chart-refinement` reaches `lem-per-kato-lattice-chart-realization` (Step 5).
- `lem-sfb-field-log-smooth-gabber-modification` → `lem-per-log-smooth-composition-strict-base-change` → `lem-per-fs-log-infinitesimal-criterion` → `lem-per-divisible-unit-lattice-extension` (Step 4).

I checked this on the entire current DAG with an independent breadth-first traversal starting at every `nt-target-*`. With the live statement-only item, 27908 nodes are reached; substituting the repaired packet reaches the identical set of 27908 nodes. The set of added nodes is empty, so the set of newly reached excluded nodes is empty. In contrast, the uniformizer-chart interface is absent from the live target closure. These paths establish already-existing reachability; they do not supply the mathematics of the proof. The proof takes only the generic logarithmic and lattice statements quoted in citations.json, no modification, alteration, uniformization, duality, or perverse theorem. The repair therefore does not revive the discarded Artin–Gabber route.

I also traversed every cited dependency to check that none reaches this item, checked each citation verbatim against its current statement, and regenerated citations.json for the eleven steps. No node was created and no Mathlib search question changed, so the retained searches were not repeated. The earlier source review and small-case tests above still apply. The source's invertible-torsion conclusion for the uniformizer chart is not needed in the subsequent face-localization argument, and I make no uncited claim about that conclusion.

## Unfinished work

None in the one-level split. No Lean was written or compiled. Independent maintainer review remains part of the normal delivery process.

## Server validation

On resumption, the required dry run of the retained packet completed successfully at dcb3486f78c. That mechanical pass did not repair the returned route fault. The repaired eleven-step packet then passed the required server dry run at 481a6be9ee5: preflight, check_dag and review_split passed. This report records that result; the final packet is checked again before push.
