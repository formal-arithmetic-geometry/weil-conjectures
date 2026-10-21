# Worker report: lem-sfb-dense-lattice-derived-invariants-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dense-lattice-derived-invariants-comparison.json`: item, split; statement unchanged, seven proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-condensed-derived-restriction-calculus.json`: statement, unsplit; no Mathlib match. Formal action-category, derived restriction, scalar and cup-product infrastructure; no analytic comparison assertion.
- `dag/nodes/sec-six-functors-basics/lem-sfb-trivial-ladic-derived-exterior.json`: statement, unsplit; no Mathlib match. The specified derived coordinate-cup morphism for the trivial coefficient module is an isomorphism. This is the remaining analytic obligation, explicitly all-continuous for the noncomplete algebraic closure.
- `dag/nodes/sec-six-functors-basics/lem-sfb-discrete-lattice-cup-exterior.json`: statement, unsplit; no Mathlib match. The algebraic coordinate-cup normalization for trivial discrete-lattice invariants over any condensed ring.

`citations.json` contains literal statement quotations for every citation in every item step. Searches are preserved in `searches.jsonl`; full newly run results are in `search-results.json`. No Lean, repository, launcher, unit or chapter file was written.

## Attachments

None. Searches of the project's `lean/WeilConjectures/` by the exact blueprint tag, dense-lattice wording, continuous invariants, and related cohomology notions found no declaration stating this item. The discrete-invariants/continuous-cohomology comparison is for discrete coefficients and does not give this statement. No Mathlib hit gives the derived internal-module comparison.

## WANTED

WANTED: an exact reference or proof for the trivial-representation derived coordinate-cup exterior calculation with all-continuous noncomplete norm-topological algebraic-closure coefficients, for `lem-sfb-trivial-ladic-derived-exterior`. In particular, neither a complete Banach-space theorem nor a sequential closed-embedding colimit statement settles this obligation.

WANTED: an exact ordinary internal condensed-ring reference for the combined normalized restriction/scalar/cup calculus, for `lem-sfb-condensed-derived-restriction-calculus`. The formal ingredients have standard injective-resolution proofs, but the cited blueprint supplies none of this package.

WANTED: an exact internal-module reference for the coordinate-cup normalization of the discrete lattice Koszul calculation, for `lem-sfb-discrete-lattice-cup-exterior`.

I read Bhatt–Scholze, *The pro-étale topology for schemes*, §4.3, especially Definition 4.3.1 and Lemmas 4.3.8–4.3.11, in the obtained arXiv-1309.1198 PDF. These give classifying-topos context and conditional comparison with continuous cohomology; I did not claim they prove the analytic obligation. The hypotheses in Lemma 4.3.9 do not license replacing the topology of Omega by a union topology. I also inspected the Stacks source at Tag 013P, `derived.tex`, `lemma-morphisms-lift`, and Tag 0156, `section-right-derived-functor`, including `lemma-injective-acyclic`. These concern formal resolution computations, not the noncomplete coefficient calculation. I consulted the abstract of Emma Brink, *Condensed Group Cohomology*, arXiv:2512.03648 (https://arxiv.org/abs/2512.03648), only to check scope: its advertised solid-coefficient comparison is not the requested all-continuous analytic theorem. No new literature was downloaded and no SGA source was used.

## What was wrong or missing

The imported item had an empty proof and advertised its exact analytic reference as WANTED. Its mathematical statement is retained verbatim. Its unit record comes from the older six-functors unit, while the item's actual source is main-20261015, paragraph (3) of `sk-thm-sf-ctf-stability-direct-images.proof.md`; I read both the unit/chapter records and that current source, and follow the latter's open-direct-image/tame-boundary route. The current paragraph is context for this analytic input, not a proof of it. The proof origin is therefore honestly `agent`.

The ancestor command returns `None`. I retained the inherited null `blueprint.from.node` and complete inherited via chain, filled the precise places of the new inputs, and searched the whole blueprint. I did not invent an ancestor or edit someone else's metadata.

A tempting but invalid shortcut is to replace every derived internal Hom in `lem-sfb-condensed-derived-invariant-bar` by an underived continuous-function object. Its statement explicitly forbids this substitution. Likewise the discrete finite-coefficient procyclic node has the wrong coefficient category. The split instead isolates a smaller analytic statement on the trivial module and carries the finite-dimensional representation argument itself.

## Proof and why this is a split

For trivial coefficients, restriction sends each continuous coordinate character to the integer coordinate character, and preserves every ordered cup product. Hence it identifies two explicitly specified derived maps out of the same finite zero-differential exterior complex. Their invertibility gives the comparison on trivial representations.

For a general continuous E-representation, induct on its E-dimension. Put A_i=T_i-1. If some A_i is invertible, the central element acts as identity on invariants of an equivariant injective resolution, so the derived image of A_i is both zero and invertible. Both derived-invariant objects vanish. If all A_i vanish, density makes the action trivial. Otherwise a nonzero singular A_i has a nonzero proper kernel U, stable under the entire commuting action. The representations U and V/U have strictly smaller dimension. Their underlying finite-dimensional exact sequence remains exact on all continuous F-valued sections (a linear matrix splitting works even for noncomplete F=Omega). The normalized restriction transformation is a morphism of the resulting distinguished triangles, so the existing triangle two-out-of-three theorem finishes the induction.

The new analytic node does not restate the original comparison: it has no D, no restriction morphism and no nontrivial representation; it computes one fixed trivial-coefficient derived object with specified cup classes. The formal node has no dense-lattice isomorphism claim. The discrete node has no L or analytic coefficients and computes the cup-normalized lattice object over an arbitrary condensed ring. No new node carries the general representation argument; steps 4–6 carry it. Every new node is statement-only. No proof step exceeds 2,000 characters.

## Not duplicates

lem-sfb-condensed-derived-restriction-calculus vs lem-sfb-condensed-product-action-inflation: the latter gives categories and inflation adjunctions only for profinite product projections; the new statement handles restriction along general continuous homomorphisms including discrete-to-profinite maps, the derived restriction transformation, scalar pasting, and cup/character normalization.

lem-sfb-condensed-derived-restriction-calculus vs lem-sfb-condensed-derived-invariant-bar: the existing node gives a derived bar model for profinite groups, not the formal action/restriction/scalar/cup calculus for topological groups including the discrete lattice. Its derived internal Hom terms are not assumed acyclic here.

lem-sfb-condensed-derived-restriction-calculus vs lem-sfb-condensed-product-bar-comparison: product factorization of profinite actions and diagonal-to-iterated totalizations do not give group restriction to a dense discrete subgroup or the cup/character statements.

lem-sfb-condensed-derived-restriction-calculus vs lem-sfb-derived-composition-adjunction-normalization: the existing node derives an isomorphism conjugate to an isomorphism between composites of exact left adjoints. It does not construct the noninvertible-in-general group restriction mate or the internal cup products used here.

lem-sfb-trivial-ladic-derived-exterior vs lem-exc-procyclic-two-term: the latter assumes finite ell-primary discrete coefficients and uses continuous group cohomology; the new node computes an ordinary derived internal condensed-module object for trivial all-continuous E/Omega, with specified coordinate-cup maps, for every r.

lem-sfb-trivial-ladic-derived-exterior vs lem-sfb-tame-inertia-continuous-koszul: the latter is an ancestor which uses this item's comparison for nontrivial representations after prime-to-ell reduction. It cannot be cited downward without a cycle; the new analytic input is only the trivial-representation calculation and has no prime-to-ell group.

lem-sfb-trivial-ladic-derived-exterior vs lem-per-strict-local-snc-kummer-cohomology: the existing node computes etale F_ell cohomology of an algebraic punctured strictly henselian local scheme; it makes no statement about these internal condensed norm-topological coefficient modules.

lem-sfb-discrete-lattice-cup-exterior vs lem-sfb-discrete-lattice-koszul-resolution: the existing Koszul node gives an isomorphism normalized only in degree zero, natural in maps and coefficient restriction. It does not identify degree-one coordinate characters or their ordered cup products with its exterior basis, which is essential for proving that the canonical restriction morphism is invertible. The new node supplies that derived cup normalization, for trivial coefficients only, over arbitrary condensed R.

The DAG searches included tags, coordinate-character/exterior/cup/Koszul wording, central actions and derived restrictions across all nodes. Whole-blueprint searches included `dense lattice`, `procyclic`, `continuous cohomology`, `Fitting`, `Hochschild`, `Breen`, `exterior`, `cup product`, `derived invariants`, `trivial coefficients`, `coordinate characters`, and `restriction calculus`. No identical imported blueprint statement was found. The new nodes cite no Stacks tag as their source, since no Stacks tag states them; there is no same-tag new-node collision.

## Mathlib assessment

For each new node I ran LeanFinder twice with genuinely different formulations, Loogle, LeanSearch, and the prescribed grep command. All services answered in this pass. Every recorded query is exactly a query in the tool log. Full outputs were read, not inferred from the service status.

I inspected Mathlib's `Condensed/Module.lean`: `CondensedMod R` is a sheaf of modules over an ordinary ring, not this internal condensed-ring group-action calculus. I inspected `RepresentationTheory/Homological/GroupCohomology/Basic.lean`: its objects are ordinary Rep, its derived-isomorphism upgrade and profinite cohomology are TODOs. The finite cyclic resolutions do not treat the infinite lattice in internal module objects. The `rightDerived`/`CommShift` hits are relevant formal infrastructure, but not a one-line specialization giving the complete normalized group-action/scalar/cup statement; `Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean` itself notes the triangulated upgrade as TODO. Continuous-cohomology degree-zero results compute another category and only one degree. Mahler-equivalence and period-ring completions do not identify the requested derived objects. Consequently no new Mathlib leaf is asserted.

## Review by NP

I opened the exact current blueprint paragraph (3), the chapter and unit records, the three new node files, the unchanged item statement, and the complete statements of every node used in the proof. The blueprint gives only the tame-boundary context. The three new inputs are explicitly agent-formulated WANTED obligations, not misattributed to a Stacks tag or to Bhatt–Scholze. I checked B–E of delivery-errors in full: new nodes introduce their own rings, sites, groups, actions, derived categories and specified maps, have no proof sketches in the statement, carry real searches, and do not point back to the item.

Step 1 takes precisely the canonical restriction construction, exactness and shift compatibility from the new calculus. Step 2 takes only the definition of being fixed after every profinite base change from `def-sfb-condensed-action-module`; its density proof is explicit, including parameterized group elements rather than just global points. The Hausdorff hypothesis is satisfied by both norm-topological fields. Step 3 reads the actual derived morphisms in the two exterior nodes and the unit/cup/character compatibility in the calculus. The coordinate equality a_i(iota(n))=n_i is written out, so this is not an inference from arbitrarily chosen cohomology isomorphisms. Finite direct sums suffice; no tensor-product flatness or infinite-product preservation is assumed.

In step 4 I checked the resolution-naturality statement: it says the normalized comparison commutes already in the derived category with a commuting augmentation square. The central action gives exactly such a square on the chosen resolution. The termwise invariants force its image to be the identity. Thus subtracting the identity gives zero, and functoriality sends an invertible difference to an isomorphism. This is an explicit short calculation from the cited statements, marked elementary, not an uncited general vanishing theorem.

For step 5 I checked the subquotient lemma's actual profinite-group and continuous finite-dimensional E hypotheses, all satisfied by L. The continuity lemma is applied over complete E only, never over Omega. After scalar extension, continuity of each finite matrix and of the chosen inverse follows from finite sums/products in the given topological field. The underlying exact sequence is sectionwise split; equivariance of the splitting is not required. I corrected the formal node to explicitly state that kernels and cokernels are formed on underlying modules, so the step does not take that claim from a mere action definition. In step 6 the induction is on E-dimension, with a zero base, a trivial-action case and both strict dimension inequalities written down. The kernel is invariant under L because it commutes with T_i. I opened `lem-sf-triangle-two-out-of-three` and verified that the calculus supplies exactly its naturality and shift hypotheses, including the connecting square. It is used as a generic tool, declared in split_report.

Step 7 uses the calculus's exact coefficient-pasting equation with the specified coefficient map f(v)=1 tensor v. Both actions are the extension of the same E-matrices, so f is equivariant. The proof of invertibility does not define b, so no noncanonical subspace or basis choice enters the naturality clause. The r=0 clause follows from the normalized identity group map, not from a rank-only cohomology count.

Small cases: V=0 gives zero on both sides; r=0 gives V_F[0]; trivial V=E gives the empty and degree-one coordinate classes for r=1; a nontrivial one-dimensional character with T-1 invertible gives zero; a two-dimensional unipotent Jordan block uses its one-dimensional kernel and quotient and tests the singular induction branch. For the discrete cup node, r=0 and the zero ring give identities of the corresponding zero/regular objects, and r=2 has two ordered degree-one classes and one degree-two summand (no division by 2, so characteristic 2 is included). The analytic node's r=1 statement is a genuine remaining obligation, not deduced from completeness; no explicit counterexample is known from this review, and it stays unsplit. For the calculus I tested the identity homomorphism, the trivial group, and a noninjective group map: the canonical comparison need not be invertible, and the node does not assert it is.

All off-unit uses are generic tools and listed in the item's split_report.tool_uses. No target, unit route, statement clause or coefficient topology was weakened. There is no STATEMENT-DISPUTED correction, because I found no counterexample to the item itself. The mathematical work completed is its one-level split, not closure of its unsplit analytic descendants.

## What could not be finished

No unfinished work within the requested one-level split. Proving the three new statement-only obligations is subsequent stage-1 work; in particular the all-continuous noncomplete trivial-coefficient calculation remains visible as WANTED rather than being asserted as already proved.

## Validation

The server review_split check passed on the sandbox proof. The required full delivery dry run and final delivery are run after this report is written; their output is the delivery record.
