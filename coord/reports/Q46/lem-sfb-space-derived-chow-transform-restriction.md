## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-derived-chow-transform-restriction.json`: statement, split; six proof steps, no Mathlib match. The statement is unchanged. Added the existing definitions of the module functors, closed subspaces, K-flat complexes and K-injective complexes to statement dependencies.
- No new nodes or Mathlib leaves. `citations.json` records each step/dependency pair with a verbatim statement quotation. `searches.jsonl` retains the actual Q46 search records; `prepare.py` is sandbox-only preparation code.

## Attachments

None. Searched the exact blueprint tag and item identifier and the concepts Chow transform, Fourier–Mukai, and derived restriction in `lean/WeilConjectures`. There is no project declaration stating this algebraic-space computation. Ordinary scheme Chow constructions and module pullback functors are not attachments.

## WANTED

None. All sources used are present under `literature/stacks-project/`.

## Corrections and provenance

The unsplit item had no proof. I retained its statement, source, created record, inherited search results, and blueprint ancestry. The item is the displayed computation of Stacks Tag 0CTS, `spaces-more-morphisms.tex`, `lemma-compute-Fourier-Mukai-for-derived-chow`, generalized only by retaining the kernel-restriction and etaleness assumptions actually used by that proof. The original Stacks construction also produces finite-presentation data; this calculation needs neither finite presentation of the closed immersion nor a Noetherian base, and I use neither.

I read `dag/chapters/sec-six-functors-basics.json`, `dag/units/sk-thm-sf-ctf-stability.json`, and their current latest blueprint texts. The inherited supporting-input chain points to the 0CTT transform-identification sentence below direct-image stability. `blueprint_refs.py ancestor` returns `None`, matching the inherited null ancestor; I preserve that provenance rather than invent an imported ancestor. Whole-blueprint searches for `derived Chow`, `Chow transform`, `Fourier Mukai`, `projection formula`, and the nearby generic localization/exactness notions found no blueprint statement of this algebraic-space calculation. The current chapter and unit are untouched; this node is not their key statement.

I used actual msearch.py calls for two semantic phrasings, LeanSearch, Loogle, and two grep queries. Both grep searches and Loogle returned no hits. LeanFinder/LeanSearch returned ordinary scheme module restriction/adjunctions, generic sheaf pullback, and ideal-kernel constructions. I read the relevant `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` and `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` passages: these do not state the derived transform identity, and obtaining it from their underived adjunctions is not a one-line specialization. No unavailable service is recorded as a negative match. Inherited Q102 searches remain distinct from the additional actual Q46 searches.

## Not duplicates

No new nodes were created. `lem-sfb-derived-chow-transform-restriction` is the scheme analogue, Tag 0CSK: its hypotheses require an open U in X with W isomorphic to U. Here X is an algebraic space and W is only etale over X; an arbitrary etale chart need not be an open embedding. Thus the scheme node cannot be used as an identical statement. Existing `lem-sfb-space-derived-etale-chart-calculus`, `lem-sfb-space-qcqs-derived-projection-formula`, and `lem-sfb-space-affine-module-higher-image-vanishing` provide the actual algebraic-space tools, so no copies of them were created.

## Review by Q46

I checked the split against delivery-errors B–E with the source and each cited statement open. There are no statement-only new nodes to audit or search. All six steps have actual arguments and citations; none moves this item's conclusion to a renamed child. Only Step 1 is marked elementary, and it explicitly performs the fibre-product and affine-chart checks. All other steps are non-elementary and cite the relevant existing theorems. Every step is under 800 characters, so there is no long step concealing a separate lemma. No statement dispute or source error was found.

For Step 1 I checked `def-sfb-space-closed-subspace` gives representability by scheme closed immersions, and `def-weil-closed-immersion` explicitly gives the quotient-ring affine description. A scheme test of the restricted h is a scheme test of h, so no unquoted geometric base-change theorem is hidden here. Its affine quotient charts make i quasi-compact, and its diagonal is an isomorphism, so the projection formula's qcqs assumptions hold. Testing the given representable j on V itself shows W is a scheme. I do not infer a scheme factorization merely from a set-theoretic image.

For Step 2 I read Tag 08GE, `spaces-perfect.tex`, `lemma-restrict-direct-image-open`, and the entire statement of `lem-sfb-space-derived-etale-chart-calculus`. That node gives total unbounded direct-image localization for arbitrary derived objects, and derived pullback composition along a and p, using La*=a* for the etale open a. This is stronger than just a degreewise higher-image isomorphism and is used in its derived form. `lem-sfb-ringed-site-restriction-kflat` states both exactness of restriction and preservation of K-flatness, justifying computation of the tensor after restriction. No properness, flatness of p, or boundedness of K is assumed.

For Step 3 I checked the exact ordinary restriction formula in `lem-trf-space-etale-module-pushforward-restriction`: applying it to h and a gives the pushforward of the restricted structure module on W. The same statement identifies etale tensor pullback of the structure sheaf with its slice restriction. The hypothesis on E then replaces exactly the restricted kernel used inside R(q_V)_*. The derived chart-calculus node also explicitly preserves quasi-coherent cohomology under every derived pullback, which checks the input L of the projection formula. The definition of quasi-coherent modules admits the empty-relation, single-generator presentation of O_W. I did not cite a definition for the theorem about derived pullback.

For Step 4 I checked `lem-weil-pbc-ring-sheaves-grothendieck` and `lem-sp-grothendieck-enough-injectives` permit choosing the nonnegative ordinary injective resolution, and `lem-weil-pbc-bounded-below-injectives-kinjective` makes that same resolution valid for the unbounded total derived functor. These agree with the K-injective construction in `sites-cohomology.tex`, the unbounded-cohomology section and Tag 07A6. `lem-sfb-space-affine-module-higher-image-vanishing` is the MODULE-valued vanishing theorem, Tag 073H, not merely a theorem about underlying abelian sheaves; its exact hypotheses are affine i and quasi-coherent O_W, already checked. Negative cohomology vanishes termwise, positive cohomology vanishes by that theorem, and the degree-zero kernel is i_*O_W because the specified module direct image is right adjoint to tensor pullback and hence preserves kernels. The actual augmentation is therefore a quasi-isomorphism. This is a short resolution argument from the cited facts, not a new lemma or an assumption that closed pushforward is exact on all structure modules.

For Step 5 I read Tag 08IN, `spaces-perfect.tex`, `lemma-cohomology-base-change`, including its canonical adjunction-mate description. The cited `lem-sfb-space-qcqs-derived-projection-formula` says exactly that formula for unbounded quasi-coherent inputs on algebraic spaces. It applies to i with F=O_W[0] and L=Lp_V^*K. I checked the symmetry and structure-module unit in `lem-sf-ringed-derived-closed-symmetric-monoidal`, so the order of factors is legitimate and O_W tensor Li^*L reduces to Li^*L. This is structure-sheaf tensor, not constant torsion-coefficient tensor. No perfectness or finite Tor hypothesis was inserted.

For Step 6 the chart-calculus statement explicitly supplies both derived composition comparisons, and exact etale pullback as slice restriction. With p_V i=b_W and q_V i=j from Step 1 they give the two required identifications. I read the underlying composition argument in `sites-cohomology.tex`, Tags 0D6D/0D6E: it uses composition of derived pullbacks and uniqueness of right adjoints, not preservation of injectives by an arbitrary nonflat pullback. Etaleness is used only for Lb_W^*=b_W^*. Naturality is in K after fixing the supplied kernel isomorphism; each transformation in the composite is natural in that variable.

The off-unit dependencies are explicitly declared as generic tools in `split_report.tool_uses`: ordinary algebraic-space module localization, the Grothendieck/enough-injectives and bounded-below K-injective facts, and ringed-site tensor symmetry/unit. They replace no step of the current unit's route. All geometric dependencies otherwise belong to the inherited unit. I checked that none of these cited nodes depends back on the item.

I tested empty W or V, K=0, n=0, an identity immersion, nonreduced closed subschemes, and unbounded K. The formula gives zero for an empty kernel support, the identity computation in the identity case, and retains the derived pullback for a nonflat i. Only the etale b_W is replaced by ordinary restriction. No Noetherian assumption, finite Tor assumption, arbitrary direct-sum argument, or change of coefficient category enters the proof. No SGA source was used.

## Unfinished work

None for this stage-1 split. No Lean was written and no compiler, Lake, or build tool was run. Delivery remains subject to the required server dry run and maintainer's independent review.

## Dry-run repairs

The first dry run stopped before preflight because three verbatim quotation fragments were shorter than the citation checker minimum. I replaced all citation fragments with the full statements of the cited nodes, preserving the mathematical proof.

The next dry run passed preflight. In a final mathematical reread I corrected Step 2's wording: restriction of Lp* along the source open a is identified using composition L(pa)*=La*Lp* and exactness of a*, rather than calling the p/a triangle a cartesian square. The cited node explicitly states these composition comparisons. I reran the dry run after this correction.
