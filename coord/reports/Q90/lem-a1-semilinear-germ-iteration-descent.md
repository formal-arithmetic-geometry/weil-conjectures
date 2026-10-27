# Stage-1 worker report

Group Q90; item lem-a1-semilinear-germ-iteration-descent; 2026-10-24.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-a1-semilinear-germ-iteration-descent.json: statement, now split into eight explicit proof steps; no Mathlib match.
- citations.json: nineteen step/node citations with verbatim statement quotations.
- report.md: this report. searches.jsonl records the six actual searches made in this attempt.

No new nodes; no Mathlib leaves. No Lean files written and no compilation or build commands run. The live repository and launcher were only read. There was no prior sandbox item or report to resume.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, semilinear/germ combinations and iteration vocabulary. The semilinear germ hits concern stalk changes of rings, ordinary comparisons and scalar transport; none states the completed geometric evaluation theorem, its positive iterates and coefficient descent. Existing sorry declarations do not count as proofs. The item has no attached declaration.

## WANTED

None. Read Deligne, Weil II, printed pp.150--153 (PDF pp.15--18), especially (1.1.3), (1.1.7), (1.1.10)--(1.1.14), and Stacks sites-cohomology.tex, Tag 0D6D, lemma-derived-pullback-composition, including its K-flat proof. These sources motivate the coefficient and transport conventions; neither is claimed to contain this completed-system theorem. The explicit conditional argument is marked agent-written. Read the current blueprint latest/ evaluation paragraph of lem-a1-finite-boundary-weights and the chapter and unit records. No SGA route is used.

## Corrections and scope

The imported item had an empty proof. Its statement, statement dependencies, source, creation record and blueprint ancestry are retained. Its hypotheses already assume the one-step integral identity for every finite coefficient field, so the split does not prove that mate identity again or cite its separate sibling. The proof supplies the conditional consequences.

The Frobenius orientation is consistent: def-weil-frobenius-detailed defines Frob_q to be the inverse of the q-power field substitution. Thus the point transport cited by the item applies to exactly h=Spec(gamma); no extension to an unrelated inverse map is required. The maps g and h are treated as scheme automorphisms over k_0, without asserting k-linearity of g. The moving point x_j is k-linear because a_Y x_j = h^j(a_Y x)h^{-j}=id.

## Search results and reuse

The previous item's recorded searches were read and retained. The six newly logged queries use leanfinder twice, leansearch, loogle and grep twice, with a changed second semantic phrasing aimed at coherence and localization. All services answered. Read Mathlib CategoryTheory/NatTrans.lean:44--68, Localization/Construction.lean:247--284, Products/Basic.lean:352--375, Algebra/Category/ModuleCat/Presheaf/Pullback.lean:129--162, and AlgebraicGeometry/Modules/Sheaf.lean:238--286. The nearest results are naturality, localization extension, ordinary presheaf pullback associativity and scheme module pullback coherence. They are ingredients, not an exact or one-line specialization of the completed germ/iteration/descent statement.

Searched the whole DAG for semilinear germs, moving points, iteration, transport, coefficient naturality and the Stacks tag 0D6D; searched blueprint_refs for semilinear, iteration and germ, and checked its ancestor result. No imported blueprint node states this conditional theorem. The existing parent proper-sections-semilinear-germs assumes no one-step identity and uses this item, so it cannot be cited here. The proper-Weil-iterate-germ-formula adds a Weil structure and is downstream. The already-existing generic composition and coefficient nodes supply everything needed, so no new node is warranted.

## Not duplicates

No new nodes. Elementary naturality, induction substitutions, inverse cancellation and fraction linearity remain proof steps. The proof does not move a clause into a renamed lemma.

## Review by Q90

I checked the source pages and each cited node statement against the actual use, rather than relying on their titles or proofs. The eight steps have the following inputs and hypothesis checks.

1. fix-prop-adjunctions(1) supplies the ordinary counit. The naturality of an adjunction counit and of the specified pullback compositor gives Z_x(t)v_x=v_x R(t); the proof displays the two substitutions. lem-pod-integral-pullback-composition expressly supplies naturality. def-weil-frobenius-cohomology-transport states that its transport is natural. def-weil-frobenius-detailed gives precisely the scheme automorphisms and inverse convention used. The moving-point calculation checks that the one-step hypothesis can be used at every x_j. Properness and finite type in the item are retained, so the integral direct image and point fibers in these formulas have their stated domains.

2. lem-weil-frobenius-point-transport-natural(2) states naturality for every derived morphism, not just a chain map. Apply it to v at x_1, after applying V to the assumed square. This gives the first conclusion with the prescribed exchange; it does not require an exchange isomorphism.

3. The same statement is used only at the explicitly typed map widehat b : J_r N to Z_(x_1) S_r M. The induction is simultaneous for all points, with its base in step 2, so its invocation at x_1 is legitimate. Its target moving point is x_(r+1). The displayed naturality equation yields the exact order iota_(J_r N) widehat I_r; no swap of powers is tacit.

4. Read the full associativity equation in lem-pod-integral-pullback-composition and the final whole-system normalization clauses of lem-trf-integral-pullback-comparison-realization. The latter expressly gives equality compatibility, associativity, unitality and arbitrary finite iterations. I wrote b_r as c_(x,g^r) c_(h^r,x_r)^(-1) and the pasting equation before invoking it. Its three triples (x,g,g^r), (h,x_1,g^r), (h,h^r,x_(r+1)) are composable in the indicated order, with gx=x_1h and g^r x_1=x_(r+1)h^r. This checks the orientation of C_r and H_r. No equality of completed maps is inferred from separate finite reductions.

5. The same whole-system node supplies the unital base and coherent composition choices. Substitution of step 4 followed by naturality of b_1 yields the explicit induction for Z_x(d_r)b_r=widehat b_r f_r. The conclusion is then conjugated by the two inverses. The argument is a routine cancellation from the cited associativity theorem, not a new comparison theorem left implicit.

6. The final contraction uses the germ naturality already proved in step 1 and the equations of steps 3 and 5. The proof writes all four composites; the point-transport node is cited for the inherited naturality. This is marked elementary because it consists of direct substitution and functoriality. There is no use of a Weil structure or a Tor bound.

7. def-weil-rationalization-karoubi states the raw Hom tensor localization and that its objects are unchanged. def-weil-finite-coefficient-point(3) states the action on morphism tensors. lem-fix-operation-reduction explicitly preserves operations, comparison maps, units and counits under rationalization; hence it applies to the actual germ and exchange factors. The point-transport naturality node includes E. The proof explicitly extends each integral naturality equation to a sum of tensors by linearity; it does not assume every rational morphism is integral or choose a new lattice.

8. lem-fix-operation-reduction gives coefficient compatibility for the operations and counits; the whole-system comparison-realization node gives the same for finite compositor words. lem-weil-point-sections-scalar-extension gives the specified point comparison and its identity and successive-extension equations, and lem-weil-frobenius-point-transport-natural(2) explicitly gives compatibility of iota using those comparisons. Finally def-weil-algebraically-closed-coefficients states that morphisms are common-stage classes and equivalent representatives agree after a further extension. A fixed finite r involves a finite diagram; I form its equation at a common finite field and check its persistence on enlargement. This supplies naturality for arbitrary common-stage morphisms, not only components originally defined over one field.

I checked delivery-errors B--E point by point: self-contained item retained; no unsplit proof-bearing helper, no new notions lacking definitions, no fabricated search, no duplicate or downstream citation, no new node that restates a clause, no hidden use of a cited proof, and no unjustified coefficient or boundedness assumption. All proof steps are below 2000 characters (maximum 1579). Small cases checked: r=1 gives identities d_1=f_1=id and the given one-step factors; r=2 matches both recurrences and the pasting equation; Y=s with x=id reduces to naturality and comparison cancellation; the zero object and empty Y cause no exceptions (there are no points in the empty case). At E=L the scalar comparisons are identities; a further extension E subset L subset M uses the explicit associators. Torsion integral objects may become zero under rationalization, and the functorial argument remains valid.

The generic off-unit tools are declared in split_report.tool_uses for independent review. They realize the comparison and coefficient formalism already fixed in the statement; they replace no step of the affine-line unit's route.

## Unfinished work

None in this conditional split. The one-step mate identity remains a hypothesis and is handled by its existing separate DAG item. No additional lemma is created or left unrecorded.
