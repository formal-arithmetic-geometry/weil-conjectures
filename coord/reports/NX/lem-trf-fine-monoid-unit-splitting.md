## Worker report

Files written: dag/nodes/sec-trace-formula/lem-trf-fine-monoid-unit-splitting.json (statement, split), citations.json, and this report. No new nodes and no new Mathlib leaves. The scratch script write_split.py and the search-command log searches.jsonl remain local to the sandbox.

Attachments: none. Searching /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint id and for sharp-monoid, monoid-splitting and unit-splitting terms found no declaration stating the item. The sole broad unit/splitting hit concerns conjugation in a reduced-norm argument and is unrelated. No upstream sorry declaration was treated as a proof.

WANTED: none.

The statement was already correct, including both torsion-free assumptions, and is unchanged. Its original source explicitly calls this an agent algebraic refinement; ILO VIII 3.1.11 and 3.1.26 motivate the comparison but do not state this extra-hypothesis algebra theorem verbatim. I read these passages (printed pp.100 and 102; PDF pp.106 and 108), including 3.1.13--3.1.15 and 3.1.25--3.1.27 for the surrounding use. The proof is therefore marked agent-written. No SGA source is used.

The empty imported proof has been replaced by six steps: compute the group kernel; choose a finite basis for the sharp group; lift its basis to define a group section; prove the section lies in the monoid; write the inverse product formulas; and identify the units as finite free. The final step proves finite generation of units directly: any generator appearing in a unit expression is a unit. This avoids a redundant subgroup-freeness dependency.

Nothing remains unfinished at this level. The inherited blueprint ancestry is preserved. I read the trace-formula chapter record, sk-i-curve-zero unit record, and current main-20261015 lem-trf-local-term-locality text; the latter follows the contracting-correspondence route. This item belongs to the explicitly recorded historical monoidal-resolution auxiliary branch. I have not replaced any unit step or changed the chapter or unit. Its immediate parent lem-trf-sharpening-fan-bijection uses precisely this product decomposition in its steps 2, 4 and 9.

## Existing-node and Mathlib searches

Whole-DAG searches for finite generation, torsion-free groups, free abelian groups, units, sharpening and splitting found lem-trf-fg-torsionfree-group-free and lem-weil-subgroup-finite-free-abelian-group-free. I opened both statements. The first is the exact general theorem needed twice, and is already a Mathlib leaf in this unit. The second is also a leaf, but is unnecessary after the direct finite-generation argument for units. No duplicate was created.

Whole imported-blueprint searches with tools/blueprint_refs.py for "free abelian", "monoid", "unit splitting" and "torsion-free" found no blueprint statement of this splitting; ancestor confirms lem-trf-local-term-locality. The six "free abelian" hits concern divisors, Kummer coefficients, torsors and hypercovers. The broader monoid hits concern monoidal categories and unrelated monoid constructions. Thus same_as stays empty.

The item's prior six Mathlib search records have been preserved. Five fresh queries ran through msearch.py: LeanSearch, Loogle, grep, and two differently phrased LeanFinder searches. Their actual results were read and recorded with exactly their logged query strings. The answers include Grothendieck-group finite-generation instances, the two-unique-products property, units of a product, associates equivalences and number-field units. None constructs the required section. In particular associatesEquivOfUniqueUnits assumes that units are trivial and is not applicable here. I read its definition at Mathlib/Algebra/GCDMonoid/Basic.lean:1013, and read the finite-basis declaration at Mathlib/LinearAlgebra/FreeModule/PID.lean:383 used by the existing leaf. No search was invented and no unavailable service was recorded as a negative match.

## Not duplicates

No new nodes. The existing group-freeness and subgroup-freeness nodes were reused or considered instead of duplicated.

## Review by NX

I checked the item against the actual ILO VIII comparison passages and the parent's stated use. The statement assumes P integral and finitely generated, G=P^gp torsion free, and H=(P/U)^gp torsion free. These are all retained. No saturation or smoothness is assumed, and neither is used. The quotient section is not presumed to land in P: Step 4 supplies the missing argument.

Step 1 cites def-trf-fine-fan-blowup for integrality, units and sharpening and def-trf-fs-log-blowup for the generators-and-relations meaning of group completion. I opened both statements: these notions are actually defined there, rather than merely named. The embedding B into G/U is proved by the unit equivalence relation. Since B is cancellative, its difference group embeds B; explicitly equality of b-0 and b'-0 means b+c=b'+c for some c and cancellation gives b=b'. Writing every group element as p-p' then computes both surjectivity and kernel U. There is no appeal to an uncited exact-sequence theorem.

Step 2 cites the fine-monoid definition and lem-trf-fg-torsionfree-group-free. The latter's statement explicitly gives a finite basis with unique integer coordinates. The images of a finite P-generating list generate H as a group; the assumption on H is precisely the torsion-free hypothesis needed to apply that leaf. Step 3 uses only that previously obtained basis and Step 1's surjectivity, choosing lifts and writing the coordinate formula for t. Its additivity and pi t=1 follow term by term; it does not invoke a projectivity theorem without a citation.

Step 4 cites the unit/sharpening definition again. If p represents b, then t(b)-p lies in the kernel U, and adding this unit to p stays in P. The section is the restriction of t, hence independent of representatives and additive; injectivity B into H proves qj=1. Step 5 checks the two inverse formulas, including that p-j(q(p)) lies in U and that q(u)=0. Thus the isomorphism is over B and has exactly the prescribed unit factor. These steps are elementary explicit computations from the preceding steps, not clauses delegated to replacement nodes.

Step 6 cites the same fine/unit definition and finite-basis theorem. I checked the potentially hidden finite-generation assertion directly: for u=a_i+v a unit, v-u=v+(-u) belongs to P, so it is an inverse for a_i. Therefore only unit generators occur in any expression for u. This proves finite generation of U, and its inclusion in torsion-free G proves the remaining hypothesis of the basis theorem. The resulting coordinate map U to Z^s gives the required finite integer s. No separate subgroup theorem is silently used.

I checked B--E point by point. There are no new-node format, source-tag, duplicate or leaf-match obligations beyond the unchanged existing nodes. The item and all steps introduce their objects; TeX has single decoded backslashes, and every cited statement has a verbatim excerpt in citations.json. Proof dependencies are exactly the union of uses. All proof steps are below 2000 characters, and the non-elementary content is the existing finite-basis theorem, not a long hidden sublemma. The elementary kernel, basis-lifting and inverse calculations are spelled out. No dependency is the item or a descendant: both definitions and the freeness leaf already exist and are upstream of this calculation.

Small cases checked: P=0 gives r=s=0 and empty sums; P a torsion-free finitely generated group gives B=0 and U=P; sharp P gives U=0 and j the inverse of the sharp quotient; the nonsaturated sharp monoid generated by 2 and 3 in Z is allowed and splits with s=0. For an arbitrary allowed sharp B, B plus Z^s satisfies the formulas. The two assumptions must not be silently dropped: a finite nontrivial group would violate the conclusion U=Z^s without torsion-freeness of G; the fine monoid generated by (2,0), (-2,0), (0,1), (1,1) in Z^2 has U=2Z times {0} and sharp group Z/2 plus Z, so its group quotient cannot admit a section. This confirms the role of the separate hypothesis on H.

During self-review I replaced an unnecessary subgroup-freeness citation by the direct unit-generator argument, checked both basis-theorem applications against their exact hypotheses, and retained the source's agent-refinement designation instead of attributing the constructed proof to a theorem that ILO does not state. No statement correction or dispute was necessary. The required remote dry run and final push follow this report.
