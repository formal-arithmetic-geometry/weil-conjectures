## Files written

- `dag/nodes/sec-poincare-duality/lem-pd-total-oplax-conjugation-summands.json`: statement, split into five proof steps; no Mathlib match for the complete assertion. Original statement and statement dependencies retained.
- `citations.json`: twelve entries, one verbatim statement passage per cited node per proof step.
- `searches.jsonl`: actual results of the prescribed Mathlib search command; all seven searches are represented in the item. Existing searches retained.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for total/conjugation/op-lax comparison notions. The existing project file `Algebra/Homology/Monoidal/MapHomologicalComplex.lean` supplies the single-functor comparison, not the entire arbitrary-isomorphism square assertion. Its results already belong to `lem-sfb-termwise-strong-monoidal`; that existing node is reused.

## WANTED

None.

## Corrections and route

No STATEMENT-DISPUTED issue: the imported statement is well typed and is unchanged. No repair note exists for this item. The sandbox initially contained no item, report or old search log. I copied the live node and preserved its inherited search records and metadata.

The empty proof now contains the countability and coproduct comparison argument, the application of the existing totalization theorem, the full five-factor conjugation restricted to injections, and both terms of the signed differential equation. In drafting the last step I caught a type error: the source bifunctor is `(M,N) ↦ F_s(E_0 M ⊗ E_0 N)`, so its morphism is `F_s(E_0(f) ⊗ E_0(g))`, not `F_s E_0(f ⊗ g)`. The delivered formula uses the former throughout. This was an error in my draft proof, not an error in the item.

I read the chapter record, the assigned unit record and the current `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-verdier-exchange/_section.md`. This is a generic coefficient/cochain tool below the seeded Poincare target, not a change to the Verdier exchange route. `blueprint_refs.py ancestor` returns None; the existing null ancestor and its explicit seeded-target path remain. Whole-blueprint searches for `oplax`, `total tensor`, and `conjugation`, and a search of the latest blueprint for total/conjugation and bidegree comparison expressions found no equivalent imported statement. `same_as` remains empty.

## Unfinished

None for this one-level stage-1 split. No Lean was written and no compiler, Lake or build tool was run. All writes are within this item's sandbox; required delivery scripts manage their own delivery worktrees.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. The single-functor theorem `lem-sfb-termwise-strong-monoidal`, the equivalence-colimit theorem `lem-galois-equivalence-preserves-limits`, and existing definitions are reused. The first does not state the square conjugation through arbitrary, possibly nonmonoidal `a`; the latter only provides coproduct preservation. Neither is claimed as an exact attachment for the item.

## Review by Q95

I read sections B through E of `coord/delivery-errors.md` and reviewed the node's proof against those requirements. For the source conventions I read Stacks `homology.tex`, Tag 012Z, `definition-associated-simple-complex`, and `remark-triple-complex`: the total uses a direct sum and the second differential has sign (-1)^p. I also read Tag 0038, `categories.tex`, `lemma-adjoint-exact`, including its Hom/universal-property proof, and Tag 0FPQ, `sites-cohomology.tex`, `lemma-symmetric-monoidal-cat-complexes`. Tag 0FPQ is about ringed-site modules and omits details; I do not claim it states this general abstract functor-square theorem. The proof is explicitly agent-written and uses the already existing general single-functor theorem. No new node requires an additional source. No SGA source is used.

For step 1 I opened the statement of `lem-galois-equivalence-preserves-limits`: it asserts preservation of image colimit cocones for every diagram, precisely the fact taken here. The countable discrete index is small because p ↦ (p,n-p) is a bijection from the integers; the two non-equivalence functors preserve its coproducts by the item's actual hypothesis. `def-weil-pbc-category-colimit` states the unique factorization and uniqueness used to construct and invert kappa. I checked both composites on the respective injections, not merely that two abstract coproduct objects are isomorphic. The equivalence node is a Mathlib leaf, and I checked its colimit declaration at `Mathlib/CategoryTheory/Adjunction/Limits.lean:106-109`.

For step 2 I opened the whole statement of `lem-sfb-termwise-strong-monoidal`. Its categories, additive tensor, colimits, additive strong functor and countable coproduct assumptions all hold for each of our four functors after step 1. Its displayed tau injection identity, natural chain isomorphism assertion and j formula are exactly what this step takes. Its statement does not require exactness, boundedness or symmetry. I read the corresponding project construction and injection lemma at `WeilConjectures/Algebra/Homology/Monoidal/MapHomologicalComplex.lean:46-83`. The two definition nodes cited here actually define cochain maps and the tensor of maps. Naturality of a at a differential proves its termwise chain equation directly; nothing about a being monoidal is assumed.

For step 3 I verified the directions and domains of each map. Inverting the existing single-functor summand equation gives T_E0^{-1} v = E_0(u) gamma_E0^{-1}; naturality of a at u gives a_C^{-1} F_s E_0(u) = E_1 F_i(u) a_X^{-1}; the summand equation for T_Fi then gives the stated three-factor restriction. The cited node really states that injection equation, not merely existence of a monoidal structure. In step 4 the same node supplies T_E1 E_1(w) = t gamma_E1. The tensor-map definition supplies (a_P tensor a_Q)t = iota'(a_p tensor a_q). Substitution yields all five factors of the exact gamma-tilde in the item, in the correct order. The colimit definition supplies determination by these restrictions.

For step 5 I read `def-sfb-strong-monoidal-functor`'s explicit tensorator naturality equation, and `def-sfb-preserves-kflat-quasi-iso`'s signed differential and tensor-map formulas. Inverse naturality follows by multiplying by inverse components, and composition of the five squares is functoriality, so no separate transport theorem is hidden. The two displayed differential expressions have the same source F_s(E_0(P^p) tensor E_0(Q^q)), and equality follows separately for (d_P,1) and (1,d_Q). Additivity preserves the minus sign. The colimit definition then gives equality on the whole degree. Every use has a verbatim quote in `citations.json`; I checked each quoted passage is in the cited statement. No argument takes information solely from another node's proof.

I checked zero complexes, identity functors, single-degree complexes and negative/odd first degrees. For an arbitrary nonmonoidal a the argument uses only its naturality at u, never a tensor-compatibility equation. With identity functors and scalar a = c times the identity (invertible c), the coefficient conjugation is c, as the five-factor formula predicts; thus the argument does not inadvertently force the conjugation to be trivial. For unbounded complexes each I_n can be infinite but remains countable; each summand differential has two outgoing terms, and no infinite sum of maps out of a fixed object or exactness claim occurs. All categories and diagrams stay in the fixed containing universe. No new statement has been introduced. Each proof step is below 2000 characters; the elementary flags identify direct applications and explicit naturality/universal-property calculations rather than an unproved intermediate comparison. The sole general preservation theorem is cited with elementary false in step 1.

Mathlib searches were run through the prescribed command, including two semantic phrasings, LeanSearch, Loogle and grep. I read the returned graded trifunctor injection statement, the binary coproduct comparison naturality statement and the mapped inverse-tensorator identities. They do not give the square comparison on complexes. One Loogle pattern used a project-only identifier and reported it unknown; that record is marked invalid rather than evidence of absence, and a subsequent valid pattern was run. The generic results are already covered by the reused DAG nodes. I found no missing non-elementary ingredient requiring a new node and no elementary lemma worth creating as a separate item.
