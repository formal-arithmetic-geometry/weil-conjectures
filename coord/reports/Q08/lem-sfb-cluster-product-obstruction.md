# Stage-1 delivery: lem-sfb-cluster-product-obstruction

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-cluster-product-obstruction.json: statement, split; statement and statement dependencies unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-proper-subspace-separating-functional.json: statement, Mathlib leaf, Submodule.exists_le_ker_of_lt_top, Mathlib/LinearAlgebra/Basis/VectorSpace.lean:323.
- dag/nodes/sec-six-functors-basics/lem-sfb-nondegenerate-orthogonal-dimension.json: statement, Mathlib leaf, LinearMap.BilinForm.finrank_orthogonal, Mathlib/LinearAlgebra/BilinearForm/Orthogonal.lean:286.
- citations.json: every step/node pair, with a verbatim statement quote.
- report.md and searches.jsonl: report and actual search log. Auxiliary Python scripts stay only in this item sandbox.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, cluster/subcluster, Franciosi/Tenni and multiplication of sections. The few cluster hits are topological cluster points, and section multiplication hits are unrelated constructions. No project declaration states this item or either new linear-algebra leaf.

## Literature wanted

WANTED: literature/franciosi-tenni-canonical-ring-3-connected-2014.pdf, Section 2, Lemma 2.12 and proof, printed pp.42--43, for lem-sfb-cluster-product-obstruction. I read the primary author PDF online at https://pagine.dm.unipi.it/franciosi/lavori/franciosi-tenni2.pdf; no local file was downloaded or invented. The entire argument here is marked agent-written because it replaces the source's extension/Serre-duality argument by the diagonal-form argument available for the already restricted reduced cluster. Neither new leaf needs this PDF: each cites the actual current Mathlib declaration read locally.

## Corrections and scope

There is no statement dispute. The source's target H0(S,O_S) uses its convention of trivializing an invertible module on a cluster (Remark 2.11). The item correctly retains the actual restricted tensor-square line. Choosing bases only inside the proof makes the product coordinate calculation legitimate and does not change the target map. The item's smooth-support, nodal and generically nonzero section hypotheses are preserved, although this argument does not need them once S is reduced. No SGA source, Lean write, compiler, Lake, git command, or repository write was used.

The sandbox initially had no node or report, so there was no prior split to supersede. The live item is unsplit, with no repair note or Lean audit declaration to inspect. Existing item searches, source, blueprint ancestry and other fields were retained. tools/blueprint_refs.py ancestor reports the existing nearest ancestor as None; the inherited from.node=null and via chain are preserved, and each new leaf extends that chain. I read both the unit record and the current latest unit page; this is a prerequisite below its direct-image route and changes neither the chapter nor the unit. This item is not the unit's key theorem, so no unit record is delivered.

## Not duplicates

lem-sfb-proper-subspace-separating-functional vs lem-trf-local-common-summand-surjections: the latter constructs a common summand for two surjections over a local ring, not an annihilating functional on a proper vector subspace.

lem-sfb-proper-subspace-separating-functional vs lem-trf-vector-space-quotient-dimension: the latter states dimension additivity for a quotient, not existence of a functional. Neither is cited for functional existence.

lem-sfb-nondegenerate-orthogonal-dimension vs lem-weil-alternating-form-dimension: the existing theorem concludes parity for a nondegenerate alternating form in characteristic different from two; the new leaf gives the dimension of any orthogonal complement, in arbitrary characteristic, without alternation.

lem-sfb-nondegenerate-orthogonal-dimension vs lem-sfb-residue-valuation-product-dimension: the latter bounds products of subspaces of a valued field and has no bilinear form or orthogonal complement.

Before writing, I searched the entire DAG by both declarations and concepts, and tools/blueprint_refs.py search for orthogonal, bilinear, nondegenerate, proper subspace, annihilating and both exact Mathlib names. The only blueprint orthogonality nodes concern additive characters; no blueprint node states either new leaf. Searches for subcluster and finite reduced gave no duplicate of this item. No new node uses a Stacks tag already assigned to a different node; all Stacks inputs are existing citations, not new nodes. The two new statements are general linear-algebra tools, not clauses or restatements of the cluster obstruction.

## Review by Q08

I read Franciosi--Tenni Lemma 2.12 and its entire proof on printed pp.42--43, with the conventions in Section 2 and Remark 2.11. The source uses a minimal failing cluster, an extension class and Serre duality. Here reducedness lets one instead take the nonzero coordinate support of any annihilating functional. I wrote out that argument, rather than cite the source as a proof step. I read the local Stacks statements for 02O5 (coherent-proposition-proper-pushforward-coherent), 01XZ (coherent-lemma-coherent-Noetherian), 02UV (cohomology-lemma-cohomology-and-closed-immersions), 02UZ (cohomology-proposition-vanishing-Noetherian), and 015B (derived-lemma-higher-derived-functors). For the two new nodes I read the actual Mathlib source, including the orthogonal definition and the theorem contexts; the online search index has an older extra reflexivity hypothesis, but the current local finrank_orthogonal declaration needs only nondegeneracy. I corrected the new leaf to use Mathlib's right orthogonal convention B(w,v)=0. Every search recorded is an actual command in searches.jsonl; I read the candidates and ran different phrasings before concluding the item itself has no match.

Step 1 uses projective-implies-proper and the proper definition for finite type, finite-type-over-Noetherian for Noetherianity, invertibility for quasi-coherence and local finite type, 01XZ for coherence and 02O5 for finite-dimensional H0 and H1. Each cited statement explicitly gives this consequence. A field is Noetherian since its only ideals are zero and the whole field.

Step 2 was corrected during self-review: I removed an uncited assertion that a finite scheme over a field is zero-dimensional. Instead it now starts with the defining affine finite-dimensional algebra, cites finite-dim-algebra-artinian and reduced-artinian-residue-product, then cites spec-finite-product-fields for the disjoint singleton charts. Closed-point-residue-field-base applies to S itself, which is finite type over the algebraically closed field; it identifies each field factor with k. Invertible-module provides one-dimensional fibers, and invertible-section-ring supplies the product formula. All these existing statements were opened and read. Gluing on the resulting disjoint opens gives the coordinate section identifications directly.

Step 3 cites the new separating-functional leaf, applied to the proper image of the original tensor restriction map. Its finite-dimensional hypothesis holds because the coordinate space is finite. Evaluating the functional on coordinate vectors writes it as a finite sum. The support coefficients give a genuine open and closed subscheme T of S, nonempty because the functional is nonzero. Every product of two global sections lies in its annihilator, which is exactly the displayed diagonal equation. This does not assume minimality or surjectivity to a smaller cluster.

Step 4 checks both nondegeneracy conditions by testing coordinate vectors and using every nonzero coefficient on T. Thus the new orthogonal-dimension leaf applies even in characteristic two. W is isotropic, so inclusion into its right orthogonal is injective. The existing rank-nullity node applied to this inclusion bounds its dimension and gives 2r <= n. No square-root choice, division by two or parity claim is used.

Step 5 uses the actual ideal-sheaf definition on affine charts and the tensor-exactness theorem for the locally free rank-one module L. The identification of the tensor quotient with i_*(L|T) is checked on local frames, including its transition units; it is not an uncited projection formula. The dimension-zero vanishing node applies on T, a finite disjoint union of fields, to its quasi-coherent restricted line. The abelian closed-immersion cohomology statement is not silently applied in module cohomology: the existing Zariski module/abelian comparison is invoked on both schemes first. These statements give H1(C,Q)=0, while H0 is direct-image evaluation by definition.

Step 6 checks the enough-injectives and left-exact-additive hypotheses against the two cited scheme-module nodes before applying the derived-functor long exact sequence, with the ringed-space module-cohomology definition. The two resulting short exact vector-space sequences have finite-dimensional ends. Basis lifts show the middle spaces are finite-dimensional; rank-nullity then gives h0(F)=a-r and h1(F)=b+n-r. Adding yields precisely the original conclusion from 2r <= n.

I tested S empty: its target is zero, so the failure hypothesis is impossible; the nonzero functional step automatically excludes it. For one supported point with failure, W=0 and the cohomological sum rises by one. For C=P1 and L=O with two distinct points, the image consists of constants and the diagonal functional (1,-1) has full support: r=1, n=2 and equality holds, including characteristic two. For more constant-section points the same construction may select only two points, which the theorem permits. I also checked that a point where every section vanishes merely gives W=0 on that coordinate, and that no connectedness or irreducibility assertion about T is assumed. All steps are below 2000 characters and hide no separately stated comparison lemma. New nodes carry no proof or proof dependencies. Every cited statement is quoted verbatim in citations.json, and the dependency union agrees with the steps. Generic off-unit prerequisites are declared in split_report.tool_uses; none replaces the unit route.

## Unfinished work

None at stage 1. The two new nodes are Mathlib leaves. The maintainer's independent mathematical review remains the normal next step after delivery.
