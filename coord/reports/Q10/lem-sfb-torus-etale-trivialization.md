# Stage 1 delivery: lem-sfb-torus-etale-trivialization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-torus-etale-trivialization.json: existing statement, now split in six steps. The statement and statement dependencies are unchanged. The item is not in Mathlib: the current logged semantic searches find etale morphisms/algebras or arithmetic matrix groups, not splitting of relative tori. Its earlier Mathlib records are retained and the actual current searches appended.
- citations.json: one verbatim statement quotation for every cited node in every proof step. The entire statement is retained for context, so the exact hypothesis and conclusion used can be read together.
- searches.jsonl: the five current msearch.py calls, including the second semantic formulation. No new nodes or Mathlib leaves were created.

## Attachments

None. Read-only searches of lean/WeilConjectures/ for the blueprint tag, torus, tori and diagonalizability find no declaration stating arbitrary-scheme fppf-to-etale torus splitting. The only torus text hit was a compact topological torus in a trace-bound argument, which is irrelevant. Definitions or sorry statements are not claimed as attachments.

## Literature wanted

WANTED: Brian Conrad, Reductive group schemes, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Appendix B.1 pp.280-281 and Proposition B.3.4 pp.291-292, for lem-sfb-torus-etale-trivialization; local archive as literature/conrad-reductive-group-schemes.pdf. The source statement and surrounding proof were read online; no download or repository edit was made.

## What was wrong or changed

The item was a correct statement-only prerequisite, with no proposed argument. There is no statement dispute. Conrad's Proposition B.3.4 includes this assertion, but its completion-and-torsion proof is not copied: this proof is explicitly agent-written, using existing character rigidity and the existing general fppf atlas bootstrap. This is below the unit level and keeps the same torus-splitting input to pinned splitting; it changes no unit or chapter route. No prohibited source is invoked.

The latest blueprint is literature/blueprint/latest (main-20261024). I read the current sk-thm-sf-ctf-stability unit and its direct-images proof, as well as the recorded chapter and unit. This item is a supporting input far below direct-images (3), not a key node requiring a unit realization edit. blueprint_refs.py ancestor reports None; its existing explicit origin chain and place are retained. Whole-blueprint searches for torus and diagonalizable returned zero equivalent nodes. Broader searches of DAG statements found the general ring character-duality and fppf atlas nodes actually used here, instead of creating duplicates. Field-only multiplicative-character antiduality and connected finite-type-field hom-family rigidity were rejected because their hypotheses do not cover this base.

## Not duplicates

No new node was created. In particular there is no replacement node that repeats the torus conclusion or a clause of it. The isomorphism functor's local description is a direct application of the existing character-duality statement, and its algebraicity is an application of the existing general bootstrap statement after writing out all scheme-test pullbacks.

## Review by Q10

I read Conrad's Appendix B.1 and Proposition B.3.4 online to check the item: its input is fppf-local diagonalizability, with no normality, henselianity or Noetherian hypothesis on the base. For tori the free character lattices are supplied by the original fppf trivializations. I also read the local Stacks statements of 01I1 (schemes.tex, lemma-morphism-into-affine), 03O3 (etale-cohomology.tex, lemma-representable-sheaf-fpqc, together with descent.tex 023Q), 021O (topologies.tex, lemma-fppf), 022C (topologies.tex, lemma-zariski-etale-smooth-syntomic-fppf-fpqc), 04S6 (bootstrap.tex, theorem-final-bootstrap, condition (3)), the source-locality list in descent.tex 04R3, and 02GN and 02VN for etale composition and fpqc descent. There are no new-node sources to check.

Step 1 uses the actual group-algebra construction of def-sfb-ring-diagonalizable-group. The affine adjunction node states precisely the natural ring-map/morphism bijection needed; the finite Laurent-monomial formula is written out and respects all three Hopf operations. The gluing node states existence and uniqueness of maps on an arbitrary open cover. def-sfb-relative-torus supplies the set-indexed fppf cover and finite ranks; its functor isomorphisms are identified with the group schemes represented by the explicit Laurent formula. I did not assume constant rank or a nonzero base ring globally.

Step 2 uses lem-trf-fppf-covering-base-change to cover both domain and codomain of each proposed isomorphism, and lem-trf-fppf-covering-is-fpqc to justify using representable fpqc descent. The latter descent node actually states existence and uniqueness of a morphism from compatible maps into any scheme. Applying it separately to each map and inverse, and using its uniqueness after product base changes, checks multiplication, unit and inverse. This is a sheaf argument for isomorphisms between specified schemes, not an assertion of effective descent of arbitrary schemes.

Step 3 uses exactly the first assertion of lem-sfb-relative-diagonalizable-character-duality: every homomorphism is uniquely locally induced by a character map. The inverses force the two character maps to be inverse by composition of their explicit monomial formulas. Its hypothesis A nonzero is checked on each nonempty affine test open; empty opens are handled separately. No field-only rigidity result is used. The coproduct node actually provides disjoint open-and-closed copies of the base, and the gluing node supplies the maps on these copies. Their statements justify the identification of the whole functor, including non-affine and nonreduced test schemes. All isomorphisms of free lattices are kept as a set; no finiteness of that set is asserted.

Step 4 verifies the substantial hypothesis that could otherwise be hidden in “descent”: for EACH Z and a in F_r(Z), the fibre product with the proposed atlas is the scheme coproduct of Z times_S V_i. The original cover pulled back to Z is jointly surjective, flat and locally of finite presentation by the cited base-change lemma. The coproduct inclusions are open immersions and hence etale by the cited composition/cancellation node; the source-locality node explicitly includes flatness and local finite presentation for arbitrary etale families. The cited bootstrap theorem then gives algebraicity of F_r. It assumes neither a representable diagonal in advance nor finite-type local isomorphism schemes. The size-convention node covers our set-indexed coproducts. This avoids incorrectly using the finite-type-only fppf effectivity node for an infinite disjoint union.

Step 5 uses the definition of algebraic space for a representable surjective etale atlas W_r -> F_r and its etale scheme-test pullbacks. The local model L_ri -> V_i is etale by source locality on its open components, including the empty union. The cited etale composition node gives etaleness of the composite W_r times_S V_i -> V_i. The fppf-to-fpqc lemma and lem-galois-fpqc-descend-etale apply to the SCHEME morphism W_r -> S; the latter node really states arbitrary-family fpqc target descent. Thus this step does not assume that an etale algebraic space over a scheme is itself a scheme. The only non-Mathlib off-unit citation, this fpqc descent node, is declared as a generic tool in split_report.tool_uses.

Step 6 checks joint surjectivity point by point: at s one chooses a covering V_i, then the rank r_i of its splitting, then a point of the surjective atlas over its splitting section (allowing a field extension as in the definition). Evaluation at the identity scheme map gives the actual tautological group-scheme isomorphism. This is the definition of F_r, not a new representability theorem. M_r = Z^r is finite free, and inversion gives the direction required by the item.

I tested the empty base, rank zero, varying ranks on a disconnected base, nonreduced affine tests, and unequal ranks. Over the empty base an empty cover works. Rank zero has the unique zero lattice and trivial group. Varying ranks cause no issue because a separate F_r is constructed for every natural number. On a nonreduced ring the character-duality statement explicitly retains idempotents; no reducedness is used. For unequal ranks the relevant isomorphism set can be empty, so the local model is the empty scheme, not an incorrectly assumed surjective piece. Surjectivity is proved only after taking all r.

Against delivery-errors B through E: only the item is written; all objects and hypotheses of the unchanged statement are explicit; the source identifies the intended theorem; no fabricated Mathlib query is recorded; all step citations have their full statements in citations.json; no field-only or definition-only theorem substitution occurs; and no clause is moved into a fresh lemma. I inspected every step for a hidden subclaim. All six are below 2000 characters and each gives its actual calculation or the exact hypotheses for the named theorem. A read-only dependency traversal found no return path from a cited input to this item. It did expose missing older descendants below the existing fppf atlas node; I have not modified those other nodes, and the authoritative dry run will determine whether current server state already resolves that background issue.

## Unfinished work

No mathematical step of this item remains open. The cited existing nodes retain their own statuses and are not claimed proved here. No Lean was written, no compiler or Lake command was run, and no repository or launcher file was changed. Dry-run and delivery outcomes will be appended below.

## Validation

Required deliver.py --no-push exited 0 and printed OK at 82b8f415e41 on 2026-10-24: server preflight passed. The dry run completed before the push invocation. No background missing-descendant diagnostic blocked this delivery on the current server state.
