# Stage-1 delivery: lem-weil-pbc-total-tensor-homotopy-cone-signs

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-total-tensor-homotopy-cone-signs.json: item, statement, split into eleven steps; not a complete Mathlib match.
- citations.json: one entry per step/node citation, quoting the statement verbatim.
- report.md: this report.

There are zero new nodes and zero new Mathlib leaves. The sandbox had no item node, proof, report or search log on arrival. I copied the current live item, preserved its statement, provenance, blueprint fields and previous searches, and appended the searches performed for this split. No Lean or repository files were written and no compiler was run.

## Attachments

None for the item. The exact blueprint tag has no project-source hit. Searches for tensor homotopies and K-flatness found component results, not a declaration giving every clause of this item. In particular, the general K-flat material under FromJoel does not state the explicit signed cone projections in this statement.

Existing attachment inspected: CochainComplex.mappingCone.quasiIso_iff_acyclic belongs to lem-pur-quasi-iso-cone-acyclic (WeilConjectures/Mathlib/Algebra/Homology/HomotopyCategory/Acyclic.lean:31). Its statement supplies the cone criterion, and its displayed proof has no sorry. I have not edited that existing node or claimed a new attachment.

## Literature

No WANTED documents. I read sites-cohomology.tex, lemma-derived-tor-exact (06YM), definition-K-flat and lemma-K-flat-quasi-isomorphism (06YP); derived.tex, definition-cone, definition-distinguished-triangle and remark-double-complex-as-tensor-product-of (0G6E); and more-algebra.tex, item-shift-tensor (0FNH) and item-flip-tensor-product (0GWR). The tags were verified in the local Stacks tags table. No SGA source was used.

I read the chapter/unit records and the current main-20261015 perfect-projection-formula statement and proof. This item supplies the chain-level exact tensor calculations behind the first paragraph's closure under shifts and cones. It does not replace a unit-level geometric argument.

## What needed expansion

The imported item had a statement but no proof. It bundles several sign-sensitive assertions: the two homotopy formulas are different, the second-factor cone needs a sign while the first-factor cone does not, and preserving only cone inclusions would not establish compatibility with the third triangle arrow. The proof now checks both projection identities on both sorts of summands, then negates them to match the stipulated -p convention.

The statement is unchanged. The final sentence, “If each term of A is flat, the same holds for A[n],” means that each term of A[n] is flat. Step 11 spells out that reindexing argument separately from K-flatness. Nothing assumes that arbitrary unbounded termwise flat complexes are K-flat.

## Searches and existing nodes

The fresh logged searches were LeanFinder with two different formulations, Loogle, LeanSearch, and grep via msearch.py. Their exact queries and outcomes are appended to mathlib_searches. All services answered. LeanSearch's triangulated-functor hit concerns applying an additive functor termwise, not tensor-totalizing against a varying-degree complex. I read its source and the generic mapping-cone conventions. Grep found BifunctorHomotopy.lean; I read its two homotopy constructions. They cover the homotopy component but not the cone projections or all K-flat clauses. The existing integer-shift node already records the general Mathlib BifunctorShift match, so it is reused.

Before considering any new helper I searched the whole DAG for 06YM/06YP, the cone criterion, and tensor/homotopy/cone keywords, and ran blueprint_refs.py searches for tensor homotopy, tensor cone, and tensor homotopies (no exact blueprint match), as well as the broad tensor search. I read the existing tensor-cone node, the one-point K-flat tensor lemma, the cone criterion and the tensor-closed node. The tensor-cone node does not state the signed projection identity, and the one-point K-flat lemma concerns a different combination of hypotheses. No duplicate helper was created.

## Not duplicates

No new nodes, hence no new/existing same-tag pair. The explicit signed identities are proved in the item's steps, not moved into new nodes restating its clauses.

## Review by Q21

I checked the node files against delivery-errors B–E with the source passages open. The site is small throughout, so the module-sheaf category is abelian in the chosen universe. All complexes are integer cochain complexes, all totals use sums, and the sheaf ring is commutative so the balanced interchange maps exist. No argument uses points of the site, exactness of tensor with an arbitrary term, finite support of an entire diagonal, boundedness, or flat cohomology.

Step 1 uses the exact statements of def-weil-sheaf-of-modules-category (abelianness), lem-pc-sheaf-modules-tensor-closed (additivity in each variable and sectionwise-induced symmetry), def-pc-tensor-complex-sheaves (the actual direct-sum construction), def-pur-sheaf-tensor-product (sheafification of presheaf tensor), and def-weil-presheaf-modules-sheafification (factorization of module maps to sheaves). The binary distribution is justified by the biproduct identities written in the step. In particular, component formulas are checked on presheaf tensor maps and then descended; the argument does not pretend all global sections of a sheaf tensor are global pure tensors. This expands the bilinearity input to 06YM/0G6E.

Steps 2 and 3 use precisely the differential in def-pc-tensor-complex-sheaves. I expanded d k and k d separately: the mixed coefficients are (-1)^p and (-1)^(p+1) for the second-factor homotopy, and (-1)^(i-1) and (-1)^i for the first-factor homotopy. They cancel over every commutative ring, including characteristic two. The homotopy-category statement used in step 3 explicitly says that its morphisms are chain maps modulo homotopy, so descent is a consequence of the calculation, not an additional uncited theorem.

Step 4 uses the existing integer-shift node for both formulas and coherence, rather than taking coherence from an isolated shift isomorphism. Its hypotheses are checked using the additivity from step 1 and the countable direct sums in the tensor-total definition. These coherence and naturality assertions are actually in its statement.

Steps 5 and 6 use the displayed cone matrix in def-weil-abstract-derived-category and the displayed total differential. The substantive chain identities are written out. For step 5 the three terms after applying phi_L have signs (-1)^p on u, (-1)^(p+1) on d_A, and -1 on d_X. For step 6 the degree of x is i+1 in X but i in the cone; that distinction gives -(-1)^(i+1)=(-1)^i, explaining why phi_R is unsigned. These steps expand the cone/split-exact compatibility left implicit in 0G6E; they cite no node for a stronger signed identity than it states.

Step 7 uses the same cone definition and the exact summand formulas of the integer-shift node. I checked naturality for a strictly commuting square of maps (the ordinary arrow-category meaning of natural in u), then both inclusions and projections on the Y and shifted-X summands. Negating the projection identities gives exactly the stipulated connecting maps -p, rather than an unspecified isomorphic triangle.

Step 8 uses the existing triangulated-homotopy-category statement, which explicitly characterizes distinguished triangles by cone triangles with -p, and the definition of an exact triangulated functor. Its isomorphism of triangles has all three arrows checked by the preceding steps. This is 06YM's conclusion proved from the expanded calculation, not merely repeated as a cited source assertion.

Step 9 uses the total differential and the sectionwise-induced tensor symmetry of the tensor-closed node. The exponents in tau d are (i+1)j and i+i(j+1); the latter reduces modulo two to ij. The reverse swap squares to one, and naturality follows because chain maps preserve degrees. This is exactly the 0GWR formula, valid also for negative degrees.

Step 10 uses lem-pur-quasi-iso-cone-acyclic, whose statement says both directions for integer complexes in any abelian category, and the right-factor definition of K-flatness in def-pc-kflat-complex. I matched that order to H^A, used the unsigned right-cone computation first, then the proved natural swap for H_A. Applying cohomology to a conjugacy preserves invertibility by functoriality in def-weil-abstract-derived-category. Thus arbitrary endpoints of u are allowed; no K-flatness of X or Y is slipped in. This follows 06YP's cone argument.

Step 11 uses the integer-shift comparison, the right-order K-flat definition and the flat-module-sheaf definition. The acyclicity of a shift is justified by its kernel/image formula, and termwise flatness is just (A[n])^r=A^(r+n). The n=0, n=1 and n=-1 cases, the zero complex, u=0 and u=identity, and the one-point ringed site all agree with the formulas. In particular, when the first tensor degree is odd the left-cone shifted-X map must be negative; the right-cone map stays unsigned. These are useful small checks on the signs.

The only off-unit statement tools are generic sheaf tensor structure and the acyclic-cone criterion, declared in split_report.tool_uses. Definitions and the Mathlib shift/triangulation leaves are reused directly. Every cited node's statement was read, and citations.json quotes it verbatim for each step. All eleven steps are below 2000 characters; no auxiliary non-elementary lemma is hidden in a long step. New-node statement/search/proof restrictions are vacuous because there are no new nodes. The calculations, not renamed clause nodes, carry the proof.

## Unfinished work

None at stage 1. Server dry-run and delivery results are recorded below when completed.
