## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-frobenius-kernel-induced-dual-pbw.json`: split statement, eleven complete proof steps, six existing proof dependencies. No new nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement quotation for every citation in every step.
- `report.md`: this report. `searches.jsonl` records the five additional searches actually run with msearch.py.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the item tag, Frobenius kernels, induced duality, PBW, Borel subgroups and distribution algebras. There is no declaration stating this item. The matches about sheaf and discrete-group coinduction concern different categories and do not supply an attachment.

## Literature wanted

WANTED: J. C. Jantzen, Representations of Algebraic Groups, 2nd edition (2003), I.8--I.9 and II.3.2, II.3.18, II.9.1, for lem-sfb-frobenius-kernel-induced-dual-pbw. There is no local book in literature/. I have not claimed to inspect it.

WANTED: M. Kaneda, On the Frobenius morphism of flag schemes, Pacific J. Math. 163 (1994), pp.315--339, especially Sections 2.3 and 2.5, for lem-sfb-frobenius-kernel-induced-dual-pbw. The primary PDF https://msp.org/pjm/1994/163-2/pjm-v163-n2-p07-s.pdf was read online at printed pp.320--322. Its left regular action, evaluation reciprocity and opposite-kernel product corroborate the conventions; the tensor-duality calculation here is not attributed to Kaneda. No download was written into the repository.

The local source actually read for the geometric argument is Milne, Algebraic Groups (2017), 2.25--2.30, printed pp.47--49, and 21.72, 21.80, 21.84--21.86, printed pp.447,450--452. The inherited unit record was read alongside the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof. These are the newest main-20261024 snapshot. The proof remains on the inherited infinitesimal prerequisite route: it uses neither global induced-module dimensions nor Kempf vanishing to establish the finite-kernel calculation. Its origin is explicitly agent-written.

## Source error

STATEMENT-DISPUTED: the imported definition of Z_r(eta) did not quantify x or b. If b were read as an arbitrary element of B(D), f(xb) need not be defined: for S=SL_2, B upper triangular, r=1 and x=1, take b with diagonal 1 and upper entry 1. Its Frobenius image still has upper entry 1, so b is not in L_r. A function in F[L_r] cannot be evaluated there. I corrected the formula to quantify over every commutative F-algebra D, x in L_r(D), b in P_r(D). This is exactly the convention in the parent `lem-sfb-steinberg-infinitesimal-induced-simple` statement and makes explicit the intended restricted Borel action; it does not change the character or any conclusion.

The imported statement also had doubled literal TeX backslashes; these were normalized. The root-parametrization node was removed from stmt_deps because the statement chooses no parametrizations; it remains a proof dependency where root factors are used. All other maintainer metadata, including the inherited blueprint.from.node=null, from.place and via chain, is retained. The blueprint ancestor command itself reports null for this created-node chain; I have not fabricated a different ancestor.

## Not duplicates

No new node is delivered. I searched all DAG statements and titles, not only the current unit, for big cells, opposite Borels, root products, finite Hopf duality and Frobenius kernels, and ran blueprint_refs searches for Frobenius kernel, big cell, distribution, opposite and Borel. Initially I considered a uniqueness-of-opposite-Borel node. Reading the existing intersection and root-product statements showed it is a short deduction from them; it is now step 2, not a redundant node. The existing Steinberg socle and freeness nodes have stronger special-weight conclusions or different hypotheses and were not used to hide this argument.

The item's original five Mathlib searches were read and retained. Five further logged searches tested the opposite-Borel subclaim in two semantic phrasings, with Loogle, LeanSearch and Mathlib grep as well. Every service answered. Their hits are abstract-group opposites, Sylow extensionality, Lie Cartan subalgebras and measure-theoretic Borel spaces, rather than Borel subgroup schemes. I read the grep/Loogle BorelSpace instances at Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:643--650 and the abstract-group opposite definitions in Mathlib/Algebra/Group/Subgroup/MulOpposite.lean; neither can state the geometric claim. No Mathlib match is asserted. There are no newly created nodes requiring a separate search log.

## Review by Q120

I checked the actual statements of every cited node before assembling the proof. In step 1, `lem-sfb-reductive-borel-pair-structure` expressly says that semisimple implies reductive, so the reductive hypotheses of `lem-sfb-bruhat-longest-cell-charts` hold for S. The latter expressly supplies the longest element, its involution, the scheme intersection with the conjugate Borel, the open multiplication chart and U isomorphic to affine N-space. I wrote the coordinate change after translating that chart by n_0, including the n_0 squared factor in B; omitting that factor would give the wrong multiplication map.

In step 2, the intersection node is used for its scheme-theoretic product formula for B intersect B', not merely for a statement about points. The root-parametrization statement says each factor is an affine line. The positive-system clause of the Borel-pair node applies separately to each Borel containing the same maximal T. Empty common positives therefore forces the negative positive-system, and the root-product node identifies both radicals with the very same ordered product of root subgroups. This is the argument that makes the conclusion valid for every opposite Borel. Uniqueness was not taken from the proof of a cited node or asserted from the existence of one example.

Steps 3--4 use the specified affine Frobenius formula itself: powers commute with coordinate maps and tensors, the inverse image ideal is generated by q-th powers, and the two closed fibres in the open product chart impose their equations separately on its two coordinates. I checked containment of the whole nonreduced L_r and S_r in the open chart using their support; I did not replace either kernel by its reduced identity. I also wrote the test-algebra equations and the right P_r action on the product, which are needed later for the eigenfunctions.

For step 5 the Borel-pair statement supplies precisely B=U semidirect T. Together with the already established chart it gives the kernel products. Polynomial division by a monomial ideal supplies the finite bases, including a bound proving nilpotence of the augmentation ideal. The cited distribution-calculus node defines distributions by vanishing on a power of that ideal; this is exactly the property used to compare its notion with the full finite coordinate dual. No primitive-generation or characteristic-zero enveloping-algebra assertion is used.

Steps 6--7 are explicit finite-basis and balanced-tensor arguments. The pullback of scheme multiplication has the matrix whose transpose is h tensor b mapping to hb, so it really is convolution and really is a bimodule isomorphism. The inverse for the induced tensor module is written out and checked against the balanced relation. This avoids assuming a PBW theorem for the very module being proved free.

In step 8 the only cited notion is the coaction definition in the distribution-calculus node. The proof that the covariance kernel is stable is written out: commuting left and right translations give a tensor-kernel equation, and independent coefficient functionals show each first tensor factor remains in the kernel. Step 9 uses the actual product L_r=U^-_r times P_r and explicitly constructs the inverse to restriction. Thus dimension q^N counts the retained monomials rather than relying on a global Weyl dimension formula.

I checked the signs and order in steps 10--11 against the left translation in the item and Kaneda's convention. Both the antipode and the left regular action insert inversion, so their inversions cancel at identity. Evaluation is therefore a D_B eigenvector of character eta, not minus eta. Anti-multiplicativity gives the displayed A-linearity equation in the correct order. The matrix on the coefficient duals and the extended monomials is the identity, proving bijectivity rather than simply citing a perfect-pairing slogan.

I tested S=1 (all maps become the identity of F), N=0, arbitrary torus rank in the intermediate formulas, and the SL_2 upper/lower chart for both q=2 and q=4: the negative coordinate has equation c^q=0, the positive coordinate b^q=0, and the torus coordinate t^q=1 on S_r while t remains invertible and unrestricted on L_r. The function extension is g(c)t^m for eta(t)=t^m, including negative m. This gives the claimed q-dimensional space and the evaluation matrix on its monomial basis without factorial denominators. It also catches the missing b in P_r quantifier. All other steps use arbitrary characteristic p and no division by p.

There is no new statement needing a separate source or small-case test. No step exceeds 2000 characters, and none abbreviates a standard induction-duality comparison: all the fibre, tensor and pairing maps and their inverses are specified. The deeper group structure is cited from existing nodes; the ensuing elementary steps are direct coordinate, finite-basis and balancing calculations. citations.json contains verbatim quotations from the actual statements, including the complete statement when a step uses several of its clauses. I checked B1--B10, C1--C8, D1--D5 and E1--E7 against these files: in particular no new clause restatement, off-route tool, missing non-elementary black box, reduced-points argument, or uncited scalar comparison is being substituted.

## Unfinished work

The split, source checks and self-review are complete. No Lean was written, no compiler or Lake tool was run, no agent was started, and no direct write or git command was made in the shared repository or launcher. The required dry run and direct delivery follow this report.
