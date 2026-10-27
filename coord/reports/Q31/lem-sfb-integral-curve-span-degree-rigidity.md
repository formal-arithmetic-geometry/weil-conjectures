# Stage-1 report: lem-sfb-integral-curve-span-degree-rigidity

1. Files written: dag/nodes/sec-six-functors-basics/lem-sfb-integral-curve-span-degree-rigidity.json (item, statement kept, split into nine steps; no Mathlib match), citations.json, and this report. No new nodes and no Mathlib leaves. write_split.py is sandbox-only authoring support.
2. Attachments: none. Searches of lean/WeilConjectures for the blueprint tag and rational-normal/span-degree notions found no project declaration proving all clauses. Existing sorry declarations were not counted as proofs.
3. WANTED: literature/gieseker-lectures-on-moduli-of-curves.pdf, Proposition 1.0.3 printed pp.30--31, for this item. Read its online transcription at https://doczz.net/doc/7664568/lectures-on-moduli-of-curves---school-of-mathematics--tifr (Proposition 1.0.3 and its restricted-linear-form estimate). The proof is marked agent-written: the equality case is reconstructed, not falsely attributed to those pages.
4. The imported statement is correct as written, including singular Y and e=1; its empty proof needed completing. No unit statement or target is changed. Stacks curves.tex Tag 0CCS has an unrestricted equality sentence that cannot be applied at d=0 (O_C on a positive-genus curve gives h0=1=d+1). Here e>0; nevertheless our equality proof does not use that sentence. It uses the existing linear-series bound for g>=2 and Riemann--Roch for g=1. This is an audit of the source, not STATEMENT-DISPUTED for this item.
5. Unfinished: nothing in the mathematical split. Final delivery requires passing the server dry run and push.

## Blueprint and searches

Read the fixed six-functors chapter, the constructible-stability unit and latest direct-images proof (3), and the inherited stable-curve/GIT prerequisite route. The item is a below-unit geometric prerequisite; no direct-image argument is replaced. The ancestor command prints None, agreeing with its inherited null ancestor; preserve its detailed from.place and full via chain. Searches of the whole DAG and blueprint for rational normal, span degree, genus zero, complete systems and normalization-section injection found no exact duplicate. The existing specialized smooth-curve section cap and linear-series bound, normalization-section-defect, and low-genus rigidity are reused. General tools in other units are declared in split_report.tool_uses.

Mathlib searches were exclusively through the required msearch.py command; searches.jsonl is the actual command log. Read all returned results, using alternate normalization-injection, positive-degree-section-bound and extremal-series phrasings. Recorded queries are exact, including the initial item's four searches, which were retained. Normalization structure hits do not give global-section degree bounds; residue/cycle degrees and Weierstrass configurations do not state this theorem. No declaration specializes in one line to the item. No new-node searches are needed because no node is created.

## Not duplicates

No new nodes. Existing general results are cited directly; none is copied, narrowed into a fresh node, or promoted from a clause of the item.

## Review by Q31

I read the item and the Gieseker Proposition 1.0.3 transcription, including its positive-degree restricted-section estimate, and checked local Stacks varieties.tex normalization, ample-on-curve and degree sections and curves.tex Tags 0CCS, 0C6T and 0C6U. I read the entire statements of every cited node. There is no new node whose source needs an additional audit. The equality argument is mine and exposes its comparisons rather than hiding a normalization-image lemma or Pic(P1) lemma.

Step 1 uses only the structural first paragraph of projective-curve-normalization-section-defect: integral Y is connected and generically reduced with one component, so it gives smooth proper connected C and e>0. I do not infer the m=1 injection from an eventual-m bound. normalization-properties explicitly says finite, surjective and birational. proper-dim-one-projective applies because C is proper of dimension one. None of these dependencies leads back to the item.

Step 2 uses generic-stalk clause (3), whose injectivity is for every nonempty open of the integral scheme Y. Birationality identifies the generic line fibres, and its zero-germ argument proves precisely the injection needed. Coordinate generation is checked on the standard charts, and pullback preserves these local generators.

Step 3 uses the affine quotient meaning of closed immersion and the coordinate definition of a projective morphism. A basis of the restriction kernel cuts out the own span scheme-theoretically. I checked the s=0 and s=1 cases explicitly; a constant closed immersion cannot have dimension-one source. This also verifies that the map of C is induced by U, not by an incorrectly identified ambient complete space.

Step 4 specializes the smooth-curve cap to B=0,m=1,q=0, all expressly allowed. It gives finite h0 and n<=e+1. Equality s=e+1 forces equality of finite-dimensional subspaces U=H0(C,L), which is the essential completeness conclusion.

Step 5 first uses Riemann--Roch on L and O to reconcile Euler and divisor degrees. For g=1 the large-degree hypothesis is e>=1, already known; its formula gives e. For g>=2 the existing linear-series theorem has smooth projective connected C, nonzero finite U and a<=e, all established. Both bounds are strictly below e+1 because e>0. Thus no incorrect implication from the g=0 Riemann--Roch formula alone is used.

Step 6 uses only the genus-zero clause of low-genus-pointed-automorphism-rigidity, supplying the identity automorphism; no fixed-point assumption is needed for that clause. degree-2g1-very-ample has threshold 1 at g=0, and def-sc-ample explicitly says the complete system is a closed immersion. Completeness from step 4 identifies this map with the actual pullback coordinate map.

Step 7 does not assume that a bijective finite morphism is an isomorphism. The two closed-immersion presentations give I subset J, surjectivity gives equal radicals, and integrality makes I prime. Consequently I=J on every chart. This handles possible singularities or positive-characteristic inseparability without an unjustified scheme-theoretic-image assertion.

Step 8 uses rational-section to write L=O(D), the degree homomorphism to get deg D=e, and the explicitly defined divisor valuations on the standard P1 charts. I computed div(t-a) at a, at infinity, and elsewhere. The finite product identifies D with e infinity in the divisor class group; divisor-class-curve supplies exactly its line-bundle conclusion. The transition relation for O(e infinity) is checked against def-sc-p1-standard, including its sign, and agrees with the projective twist.

Step 9 uses precisely the H0 clause of p1-monomial, with e>=1; ambient linear forms restrict onto all forms on the own span by basis extension. This gives the converse for the actual s, and the final strict integer inequality follows. Tested a line (e=1,s=2, equality), smooth plane conics, rational projected non-complete systems (strict inequality), singular rational curves (normalization cannot be an isomorphism if equality held), and positive-genus cases. The proof is characteristic-independent. There are no proof steps longer than 2000 characters, no SGA citations, no new auxiliary that restates a clause, and no Lean or build work.

citations.json records a verbatim statement for every node used by every numbered step. The full contracts are retained to expose their hypotheses as well as their conclusions. The union of uses is exactly proof_deps. The only writes are in this sandbox.

## Source error

Stacks curves.tex Tag 0CCS (lemma-grd-inequalities) includes genus zero in its unrestricted equality assertion. At d=r=0 this fails: the trivial line bundle on a smooth proper positive-genus curve has one section, giving a g^0_0. Only the inequality is used here. The positive-degree equality case is instead established by the cited genus-one Riemann--Roch and genus-at-least-two linear-series bounds, so the item statement needs no correction.

## Continuation audit

Resumed the existing sandbox rather than replacing its proof, searches or citations. The initial required dry run exited successfully at c98c163c17a before any push. Compared with the current repository: the item remains unsplit there and its statement, statement dependencies, blueprint fields and source are unchanged in this delivery. Rechecked all 20 step/node citation pairs against the current verbatim statements, equality of the dependency union, and all nine step lengths (maximum 1023 characters). Repeated the project attachment search and whole-blueprint rational-normal search; neither produced an exact finished declaration or duplicate. Read the Gieseker restricted-linear-form estimate on printed pp.30--31 and the local Stacks source statements. Corrected the step-6 source tag and proof-origin reference from 0E3D (a zero-dimensional restriction-surjectivity result) to 0H2V (lemma-degree-at-least-2g+1, the very-ampleness theorem). This changes no mathematical inference or citation pair.
