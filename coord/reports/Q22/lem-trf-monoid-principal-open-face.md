# Q22 stage-1 report: lem-trf-monoid-principal-open-face

## Files written

- dag/nodes/sec-trace-formula/lem-trf-monoid-principal-open-face.json: statement, split into seven elementary steps; no Mathlib match.
- citations.json: one verbatim statement quotation for the definition node cited in each of the seven steps.
- searches.jsonl: output recorded automatically by the required msearch command; all new recorded searches were actually run and read.

No new nodes, no Mathlib leaves, no Lean files, no builds. The sandbox initially contained only dispatcher markers; there was no previous item or report to reuse. The live item was unsplit, with no released repair note.

## Attachments

None. Searches in lean/WeilConjectures for the blueprint tag, monoid spectra/primes, principal faces, and monoid/principal-open combinations found no project declaration giving this statement. The principal Cech-face declarations concern different objects. No sorry-containing declaration was treated as finished.

## WANTED

None. The source PDF is present and was read locally.

## Findings and changes

The statement is correct and unchanged. The original empty proof is replaced by an explicit direct argument. The source is ILO, Travaux de Gabber, Expose VIII 3.1.1--3.1.4, printed p.98 (PDF page 104); the adjoining printed p.99 was also read. The source gives localization as a submonoid of the group completion, the monoid-spectrum basic-open basis, and the triviality of affine covers. The face witnesses and fraction-rewriting details suppressed there are written out. This is a monoid calculation; no Stacks theorem, SGA source, or non-elementary theorem is used.

The covering assertion uses covers by relative opens of D(a), as in the source equation U = union U_i. Step 3 writes that convention explicitly, without altering the statement. Merely covering D(a) by larger ambient opens would only imply that a member contains D(a), which is the preceding neighborhood assertion.

The imported ancestry is historical: latest blueprint lem-trf-local-term-locality and unit sk-i-curve-zero now use Varshavsky's contracting-correspondence route, not the former nearby-cycle/alteration branch. This supporting item retains its existing from.node, exact historical place and via chain; no unit/chapter record or route is changed. Its blueprint.same_as remains empty after whole-blueprint searches for principal face and monoid spectrum, as well as examination of broader monoid hits. DAG statement searches located the definition, the parent affine-localization-sections node and neighboring fan nodes, but no independent duplicate of this result. The parent relies on this item and is not cited back.

All inherited search history is retained. Fresh logged searches tried the spectrum formulation and then the divisors-of-multiples formulation, together with Loogle and Mathlib grep. LeanFinder returned ring-spectrum localization/order-isomorphism theorems for the former and natural-number closure/antidiagonal divisibility facts for the latter; neither states the item. LeanSearch and Loogle returned ring/semiring basic-open results. Read Mathlib/RingTheory/Spectrum/Prime/Topology.lean, lines 501--542: basicOpen and basicOpen_le_basicOpen_iff_algebraMap_isUnit require CommSemiring and ring ideals. The monoid spectrum includes the empty ideal and is not the ring prime spectrum, so these are not one-line specializations. The required grep command recorded the declarations' lines 509 and 539. There is no Mathlib match.

## Unfinished work

None within this one-level split. The item needs only the existing definition and elementary calculations, so creating further lemma nodes would duplicate clauses of the item or separate two-line arguments.

## Not duplicates

No new nodes; no new/existing pairs require comparison.

## Review by Q22

I read ILO VIII 3.1.1--3.1.4(i),(iii), especially the definitions in 3.1.2--3.1.3 and the trivial-cover assertion in 3.1.4(iii). I opened the full statement of def-trf-fine-fan-blowup: it defines fine/integral monoids, group-completion localizations, units, sharpening, ideals and primes, and the basic-open spectrum topology. It asserts no face theorem that this proof silently borrows. There are no new nodes with separate sources to check.

Step 1 uses only the displayed F_a definition and monoid addition: witnesses for zero and a, sums of witnesses, and the equations x+(y+d)=na and y+(x+d)=na prove all face clauses. Step 2 uses the cited ideal/prime definitions: the face condition makes the complement an ideal, addition closure makes it prime, and the witnesses exclude each member of F_a from every prime avoiding a. Properness follows from zero in F_a; every proper monoid ideal avoids zero. Step 3 uses the cited basic-open topology: an actual basic neighborhood of m_a contains every smaller prime, then the relative-open representation U_i=D(a) intersect V_i proves equality with the covering member. No specialization-topology theorem, finiteness theorem or sheaf theorem is assumed.

Step 4 reads the unit definition literally, using x+d=0, and explains why every prime avoids zero. Step 5 takes the already proved prime m_c for the forward implication; its reverse implication uses only the ideal condition and closure of the prime complement, including n=0. Step 6 uses the cited integral-localization definition inside the common group completion: p-ma=(p+md)-(mn)c is the explicit membership witness. Integrality is supplied by fineness, so equality of different presentations is equality in that same group; no universal-property theorem is needed, since P and -a generate the submonoid. Step 7 uses the cited unit and sharpening definitions: inverse pairs remain inverse, and adding a source unit becomes adding its target unit, which is precisely the quotient relation. Each quotation in citations.json was checked as an exact substring of this definition's statement.

Small cases checked: P={0} and arbitrary finite abelian groups have only the empty prime, all faces equal P and all opens D(a)=X. In P=N, F_0={0} while F_a=N for a>0; D(0)=X and D(a)={empty ideal} for a>0, so the direction of the containment criterion is correct. In P=N^2, a=(1,0) has F_a=N times {0}; a=(0,1) does not lie in that face, confirming that the two coordinate basic opens do not contain one another. If c=0, the criterion reduces to a being a unit, and n=0 is allowed: -a=d and the restriction into P_0=P is still defined. If a=0, the map is the canonical inclusion P into P_c. Nontrivial torsion units do not affect the argument: no torsion-free or saturation hypothesis occurs. Empty prime ideals remain legal throughout, and D(a) is never empty because it contains m_a.

Against delivery-errors B--E: no statement-only child or self-containedness issue arises because no child is created; TeX is serialized once; the source and precise places are recorded; no fictitious searches or Mathlib matches are claimed; blueprint searches and historical ancestry are retained; there is no Lean attachment, cycle, off-unit theorem, clause relabelling, moved argument, omitted standard lemma, missing hypothesis, or unproved transport. All seven proof steps are elementary calculations from definitions, explicitly written out rather than merely labelled elementary. Their lengths are 154--494 characters, so none reaches the long-step threshold. The statement, existing metadata and inherited searches were preserved; only proof/status/search/split-report fields were filled. This is my own review for direct delivery; the maintainer remains the independent reader.
