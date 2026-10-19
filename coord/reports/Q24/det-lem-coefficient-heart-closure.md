# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/det-lem-coefficient-heart-closure.json`: existing item completed as a split; statement retained, proof steps and dependencies retained from the interrupted repair, with the continuous-representation subquotient step made explicit.
- `dag/nodes/sec-six-functors-basics/lem-sfb-continuous-representation-subquotients.json`: new statement node, `unsplit`; Mathlib searches found no exact or one-line generalization.
- `citations.json`: verbatim statement excerpts for every node used by every item proof step.

## Attachments

No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states the item or the new node exactly. No attachment was made.

## WANTED

None. The proof sources used here are present in `literature/`, including Bhatt--Scholze, the main-20261015 blueprint proof, and the existing DAG statements cited by the split.

## What was checked and corrected

The retained item was compared with the current repository node and the current main-20261015 blueprint. Its statement is unchanged: it asserts closure of lisse modules over (E) or \\(\\Qlb\\) under extensions, kernels, and cokernels on a topologically Noetherian scheme, followed by the constructible-heart consequences. The item has no Lean declaration in either source checkout, so it remains a natural-language split rather than an attachment.

The proof follows the unit route in `sk-lem-coefficient-heart`: local finite-free models and extension splitting; the finite-(E) monodromy realization and representation subquotients; finite-stage descent for \\(\\Qlb\\); scalar extension and cokernel preservation; finite-free duality for kernels; and common-stratification globalization. I checked the source locations recorded on all eight steps against the blueprint proof and Bhatt--Scholze §6.8. The long arguments are single routine constructions; no step exceeds the 2000-character review threshold.

## Review by Q24

I read the item statement, its blueprint statement and proof, the unit record `dag/units/sk-lem-coefficient-heart.json`, and every node named in `stmt_deps` and `proof_deps`. Step 1 uses the finite constant local-model definition, local epimorphism lifting, exact cartesian pullback, the module-cokernel construction, abelian sheaves, and tensor right-exactness; each cited statement supplies exactly that operation. Steps 2--3 use the finite-(E) coefficient identification, the lisse lattice coefficients, etale-local monodromy realization, the new continuous-representation subquotient statement, and exact restriction; the new node explicitly supplies closed invariant subspaces, continuous quotient actions, and the two underlying-exact sequences used there. Steps 4--6 use the finite \\(\\Qlb\\)-descent object/morphism statements, tensor-transitivity, change-of-scalars preserving finite colimits, the sheaf tensor, and the colimit \\(\\QbarX\\cong\\varinjlim_E E_X\\); the corresponding verbatim formulas are in `citations.json`. Step 7 uses the internal-Hom adjunction, Grothendieck abelian sheaves, and tensor right exactness to identify the kernel with the dual of a cokernel. Step 8 uses common stratifications and exact restriction, the constructible definition, and ambient module abelianity to obtain the global closure and exact inclusion.

I checked the hypotheses at each use: (S) is topologically Noetherian, hence the monodromy charts are qcqs with Noetherian underlying spaces; the coefficient comparison is the untwisted (E)/\\(\\Qlb\\) one and needs no \\(\\ell\\)-invertibility; finite composita remain finite; and all rank-zero cases are included. The new representation node was tested on zero, identity, injective, surjective, and split maps, including (U=0), (U=V), and empty-base behavior. Its Mathlib searches were run with Loogle, LeanFinder, LeanSearch, and source grep; the hits concern generic representation constructions but do not state the finite-dimensional (\\ell\\)-adic continuity result. I also searched the whole DAG and blueprint for duplicates and found none.

On continuation after the provider interruption, I reran the required dry run; it exited successfully at temporary commit `2b39e54681`. I compared the retained item with the current repository: the statement and blueprint metadata agree, and the differences are confined to the split, its searches and its report. I reread Bhatt–Scholze Corollary 6.8.5 and its proof on printed page 60: it explicitly passes to an etale cover and then to representations of the profinite etale fundamental group. This supports steps 2–3 and the source of the new subquotient node. In particular the split does not assume that every lisse sheaf globally comes from the profinite fundamental group. I reread the current statements for all 27 step/node citation pairs and checked every quote verbatim. The local basis construction in step 7 gives the kernel identification in both directions, including independence of basis, rather than assuming duality is exact. All eight steps have fewer than 2000 characters. I also reread Mathlib’s continuous-representation definitions: `ContRepresentation` records continuous linear operators but does not require joint continuity in the group parameter, so it is not an attachment or a one-line match for the new node. I restored the successful LeanSearch query of 2026-10-17T07:58:22Z from the existing search log to the new node’s search records; no query was invented or rerun. The whole-blueprint searches for continuous representations and subquotients still give no duplicate of the new statement.

## Not duplicates

`lem-sfb-continuous-representation-subquotients` vs `cor-galois-lisse-representations`: the existing corollary concerns lisse sheaf/Galois realization, while the new node is the topological linear-algebra closure of continuous finite-dimensional representations under invariant subspaces, images, and quotients.

`lem-sfb-continuous-representation-subquotients` vs `lem-weil-pbc-continuous-etale-local-lattice`: the existing node concerns etale local lattices and coefficient sheaves; the new node states continuity and exact kernel/image/quotient representations for an arbitrary profinite-group representation.

`lem-sfb-continuous-representation-subquotients` vs `lem-sfb-integral-lisse-reduction-equivalence`: the existing node is an integral-lisse/reduction equivalence, whereas the new node is the finite-(E) representation subquotient lemma used before monodromy realization.


## Unfinished

None for this one-level split. The new representation-subquotient node is deliberately statement-only and unsplit, as required.
