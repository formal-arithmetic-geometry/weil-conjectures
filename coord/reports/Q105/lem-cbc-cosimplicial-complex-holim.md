# Stage-1 worker report — Q105

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-cosimplicial-complex-holim.json`: existing statement, now split into seven steps; no exact Mathlib match. The statement and its statement dependencies are unchanged.
- `citations.json`: eleven exact quotations, one for every cited-node occurrence in the seven proof steps.
- `item-searches.json` and `diagram-searches.json`: verbatim output of additional logged searches, also appended to the item's `mathlib_searches`. This is local research material, not a new DAG node.
- `report.md`: this report.

New nodes: **0**. New Mathlib leaves: **0**. No unit or chapter record is changed. No Lean source was written or compiler invoked.

## Attachments

None. Searches of the specified `WeilConjectures/` source on slopmaster2 and upstream master for the blueprint id, cosimplicial complexes, homotopy limits and derived limits found no project declaration stating this whole unbounded product-total theorem, including its augmentation clause. Existing alternating Čech complexes are not attachments for it. Upstream master was used only as reference material.

## WANTED

WANTED: Choudhury–Gallauer Alves de Souza, *Homotopy theory of dg sheaves*, arXiv:1511.02828v1, §3.3, Lemmas 3.18–3.19, printed pp. 12–13, for `lem-cbc-cosimplicial-complex-holim`. I read the PDF online at https://arxiv.org/pdf/1511.02828. Lemma 3.19 explicitly gives the product total for arbitrary cosimplicial unbounded complexes. Its proof dualizes the preceding simplicial-total statement; I supply a separate explicit representable-resolution argument rather than treating that short reference as a complete split. The document remains unarchived, so `proof_origin.by` is `agent`, with the archived current-blueprint opening as ancestry. No source was downloaded or archive edited.

Stacks `derived.tex`, label `lemma-derived-adjoint-functors`, Tag 09T5, gives the ordinary derived adjunction, not the enriched coherent-limit comparison needed here. I read it and the more general labels `lemma-pre-derived-adjoint-functors` and `lemma-pre-derived-adjoint-functors-general` (Tag 0FND). Those cannot replace the existing enhanced Quillen-adjunction and section-rectification nodes. I do not assign a misleading Stacks tag to the enhanced theorem.

## Findings and corrections

The item is an unsplit statement created by the hyperdescent-local-orthogonality split, not an imported proof. Its unbounded statement is correct and is preserved. The common lower bound needed for a coproduct total is absent on purpose: this theorem uses the product total. Its supplied blueprint ancestry leads to the current finite-level-proétale compact-support proof opening, through the affine-local compactification and hypersheaf foundations. The unit `sk-prop-sf-cbc` has no separate prescribed internal proof steps. I read that unit, the smooth-purity chapter record and the current blueprint proof opening; this split changes none of their routes or coefficient domains.

I initially considered introducing a general derived diagram-limit adjunction. The current DAG already has projective module models, coherent section rectification, derived Quillen adjunctions, and a limiting-cone criterion. The explicit free-resolution calculation together with those statements suffices, so I created no such redundant node. The existing `lem-cbc-presheaf-dg-function-complex` is applied with its category equal to the opposite simplex category: its presheaves are precisely the covariant diagrams used here.

The four off-unit inputs in `split_report.tool_uses` are general tools: `lem-coef-projective-cochain-monoidal-model`, `lem-coef-pointed-model-stability`, `lem-coef-quillen-section-rectification`, and `lem-coef-model-infinity-derived-adjunction`. No node of the compact-support unit supplies these model-category foundations; they do not replace a geometric step of that unit.

## Mathlib and duplicate searches

I searched the whole DAG and imported blueprint for cosimplicial complexes, Moore/normalized complexes, product totals, homotopy limits, and derived diagram adjunctions. The item's inherited searches are retained as inherited searches, not claimed as Q105's calls. Additional calls were made through the required `msearch.py Q105 lem-cbc-cosimplicial-complex-holim` command using leanfinder, loogle, grep and leansearch, including a second natural-language formulation. The appended records preserve those calls' output. They found ordinary limits, Ext, constant/limit adjunctions and ordinary derived adjunctions, not this enhanced explicit totalization theorem. I read Mathlib `AlgebraicTopology/AlternatingFaceMapComplex.lean:303–349` and `CategoryTheory/Functor/Derived/Adjunction.lean:44–110`: the first constructs the alternating coface complex only; the second derives an ordinary adjunction given derived-functor comparison data. Neither is a one-line match. Unsuccessful Loogle queries, including rejected unknown identifiers, are retained honestly; these calls supply no evidence of absence.

## Not duplicates

No new nodes were created, so there are no new/existing duplicate pairs. The existing bounded-below column-total comparison and proétale hypercover-total definition use coproduct totals and bounds, and cannot replace this unbounded product assertion. The existing coherent-end and dg-model homotopy-colimit statements describe abstract coherent totalizations; they do not themselves compute this concrete product-total complex.

## Review by Q105

I checked the item against Choudhury–Gallauer Lemma 3.19 and its preceding Lemma 3.18, read online. The source says product totalization, permits unbounded internal degrees, and distinguishes the normalized and unnormalized models. Our proof does not assume normalization: the free representable resolution directly gives the unnormalized alternating coface complex. There are no new-node sources to review. I read the entire statement of each existing node cited in the proof, rather than borrowing constructions hidden in its proof.

Step 1 uses the projective-model node for its quasi-isomorphisms, surjective fibrations and dg-projective cofibration criterion; the stability node for its cofibrant-pushout and suspension criterion; and section rectification for the objectwise projective model and the equivalence over evaluations with coherent diagrams. The model theorem is for arbitrary commutative rings and unbounded cochains. I expanded the dg compatibility check: the Hom comparison has kernel Hom(coker i,ker p); dg-projectivity handles a trivial p, while an acyclic dg-projective cokernel is contractible and handles a trivial i. Degreewise splitting and projectivity give surjectivity. This proves the needed enrichment axiom even after forgetting to abelian groups. I supplied the missing stability check explicitly: two contractible mapping cones glued along Q project to Q[1] with a contractible kernel. The projection is onto the second shifted coordinate, and its kernel has differential (db+a,-da); its contraction is (0,b). Thus the rectification theorem's stability hypothesis is actually verified. The indexing category is the small category Delta and every transition adjunction is the identity, so no varying-ring or non-small-diagram hypothesis is smuggled in.

Step 2 is an explicit construction and contraction. At [m] the basis is the weakly increasing vertex lists in [m]; prepending zero supplies the augmented contracting homotopy. The contraction is only objectwise, and I explicitly did not assert its naturality in m. The differential and augmentation themselves are natural. Tensoring this contraction with an arbitrary module complex still contracts the augmentation: the internal-differential cross terms have coefficients (-1)^(p-1) and (-1)^p and cancel. This avoids both a hidden K-flat resolution and an unbounded-total comparison theorem.

Step 3 uses the bounded-above/free-source clause of the presheaf-function-complex node, not its mapping-space clause. P is supported in cochain degrees at most zero and each term is exactly one of its free representables on Delta-op. The target K is allowed to be unbounded. The explicit basis-element formula establishes Hom(P^{-n},K^q)=K([n])^q and its naturality. The size convention makes the countable products and all representable basis sets small. The node explicitly identifies ordinary Hom with derived Hom, so it legitimately supplies homotopy invariance and acyclicity into an acyclic target.

Step 4 cites the same projective-model and presheaf-function-complex statements for the right-Quillen verification. I checked the tensor/Hom transpose sign: m of degree r sends p to (-1)^(r|p|)p tensor m. Degreewise surjections lift in each evaluated coordinate, and the product of lifts exists. For a trivial fibration its kernel is acyclic and the computed Hom kernel is acyclic by Step 3. I wrote the cycle-lifting argument that an acyclic kernel makes a surjective chain map a quasi-isomorphism; no definition of a model category was substituted for this fact. This step is marked non-elementary and names its two theorem inputs.

Step 5 uses the actual mapping-space and unit/counit conclusions of the derived-Quillen-adjunction node, the rectification comparison over evaluations, and the exact limiting-cone criterion of the cone-calculus node. Both functors are homotopical: the left one has the natural objectwise equivalence to the constant functor, and the right one computes derived Hom by Step 3. Consequently the derived left adjoint is the coherent constant functor. Its right adjoint's counit gives the very cone that the mapping-space criterion makes limiting. This establishes the enhanced statement, including higher compatibilities, rather than just a statement in the ordinary homotopy category.

Step 6 is the sign calculation. I checked epsilon(r,n)=(-1)^(rn+n(n-1)/2) in adjacent degrees: the internal ratio is (-1)^n and the coface coefficient is -(-1)^r times (-1)^(r-1), hence +1. Only two incoming coordinates occur in any output coordinate; no convergence or infinite summation argument is needed. The formula is natural in all cosimplicial chain maps and descends through quasi-isomorphisms by the already constructed right adjoint.

Step 7 uses the derived-adjunction node's explicit unit/counit provenance, not mere abstract uniqueness of some isomorphism. Transposing the actual augmentation composed with epsilon_M leaves only cosimplicial degree zero; its value at the identity is a^0. Both transpose and totalization signs are +1 there. The strict augmentation equation d^0 a^0=d^1 a^0 makes the remaining coface differential zero. This verifies the requested specific augmented map.

I tested zero coefficients, zero K, the constant cosimplicial diagram on an arbitrary unbounded M, and complexes concentrated in a single internal degree. For a constant diagram the free-resolution augmentation gives its homotopy limit M; the augmentation formula sends m to (m,0,...). At cosimplicial degrees 0 and 1 the sign formula gives exactly the coefficients in the displayed total differential. The contraction works also at [0], where repeated zeros are allowed. Nothing requires a field, a noetherian ring, finite generation, or a lower cohomological bound. The proof uses no SGA source.

I checked the proposed dependencies for a return path to this item; none returns to it. Every `uses` occurrence has a verbatim quote from that node's current statement in `citations.json`. All changes are in the sandbox. The fresh second reader should review the seven steps and run the required delivery after this worker's successful no-push dry run.

## Unfinished work

The independent second reading and actual delivery are reserved for the next worker, as instructed. The source archive remains WANTED. The remote `review_split` invocation passed with zero new nodes. The full `deliver.py Q105 lem-cbc-cosimplicial-complex-holim --no-push` validation is the final required check; no push is authorized for this worker.

## Remote validation

On 2026-10-17 the required no-push delivery dry run printed `OK (not pushed) deliver/Q105/lem-cbc-cosimplicial-complex-holim at ca6861ac74: preflight passed`. It created no delivery push. A final identical no-push check follows this report update so the second reader receives the exact validated sandbox, including the explicit dg-compatibility argument.

## Second reading by Q105

- Item statement: checked against Choudhury--Gallauer Alves de Souza, Lemma 3.19 (arXiv:1511.02828v1, printed p. 13) and the displayed product total; verdict PASS. The product indexing, alternating cofaces, unbounded internal degree, coherent homotopy-limit interpretation, and augmentation clause are retained faithfully.
- Step 1: checked every model-category hypothesis against the full statements of `lem-coef-projective-cochain-monoidal-model`, `lem-coef-pointed-model-stability`, and `lem-coef-quillen-section-rectification`; verdict PASS. The direct dg compatibility and stability calculations are explicit, and the constant identity system over small `Delta` supplies the required section model.
- Step 2: checked the representable resolution, deletion differential, augmentation, and prepend-zero contraction in degrees 0 and 1 and for arbitrary unbounded tensor factors; verdict PASS. The report correctly records that the contraction need not be natural.
- Step 3: checked the variance (`Fun(Delta, Mod)` as presheaves on `Deltaᵒᵖ`), representable formula, bounded-above source condition, product indexing, and size hypothesis against `lem-cbc-presheaf-dg-function-complex` and `def-weil-size-convention`; verdict PASS.
- Step 4: checked the tensor--Hom adjunction signs, coordinatewise lifting, acyclic-kernel argument, and Quillen conclusion against the projective model and presheaf function-complex statements; verdict PASS.
- Step 5: checked derived unit/counit provenance, homotopicality of both functors, coherent section rectification, and the limiting-cone criterion against the three cited node statements; verdict PASS.
- Step 6: independently recomputed the regrading ratio `epsilon(r,n)=(-1)^(rn+n(n-1)/2)` and the internal/coface coefficients, including the `n=0` boundary and infinite-product locality; verdict PASS.
- Step 7: checked the strict augmentation transpose, its degree-zero-only component, signs, and the equality `d^0 a^0=d^1 a^0` against the derived-adjunction unit/counit statement; verdict PASS.
- New nodes: none; there were no new-node statements or sources to audit, and no duplicate or Mathlib leaf was introduced.
- Changes: appended this independent second-reading record only. No mathematical or DAG repair was required; `citations.json` already contains one verbatim quotation for each cited-node occurrence, and the author's recorded searches are retained unchanged. An independent LeanFinder query, “The derived inverse limit of a cosimplicial module complex equals its unnormalized Moore bicomplex totalization using products”, returned eight Dold--Kan/Moore-complex declarations, none stating this enhanced product-total theorem; the actual call is recorded in `searches.jsonl`.
