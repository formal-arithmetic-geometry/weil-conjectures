# Q125: lem-sfb-pointed-free-deletion-contraction

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-pointed-free-deletion-contraction.json — statement, split into seven explicit proof steps; Mathlib searches find relevant abstract machinery but no exact or one-line match for the whole statement.
- citations.json — 13 verbatim quotations, one for each step/dependency pair.
- report.md — this report.

No new DAG nodes and no new Mathlib leaves. Existing search records in the imported item are retained, with the four actual Q125 searches appended. searches.jsonl is the search tool's unmodified log. write_split.py is sandbox-only writing support, not a project tool or a delivered node.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and identifier, deletion/insertion/contraction terminology, and condensed free/bar terminology. There is no declaration stating all of the pointed internal-module construction, identities, naturality and arbitrary-tensor clauses. The coefficient-basis free-module code in SixFunctors/ProEtale/ModuleObject/Colimit/Compatibility.lean has a different purpose. No claim relies on a sorried upstream proof.

## WANTED

WANTED: an independent ordinary condensed-module reference for the free homogeneous deletion complex and its actual point-insertion contraction, for lem-sfb-pointed-free-deletion-contraction. The blueprint's paragraph (3) motivates the internal bar input but does not contain this calculation. The proof is therefore explicitly agent-written. The cited existing nodes supply free linearization, internal/section comparison, abelianness and additive tensor; the elementary cancellation and kernel argument are written in full here.

## Corrections and retained scope

The source item was statement-only. Its mathematical statement is retained, including naturality only for pointed maps, no group or flatness hypothesis, and no assertion of equivariance. The doubled TeX backslashes and literal paragraph escapes in the imported statement were normalized for rendering; this is not a mathematical correction or a statement dispute. No mathematical source error was found.

Read the current blueprint source literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, particularly paragraph (3), and the chapter and unit records. This is the formal internal-bar input below that paragraph, not a change of its direct-image route. The older unit record is filed under sec-six-functors; the item's assigned chapter/unit fields are retained. tools/blueprint_refs.py ancestor returns None for this already-created item's ancestry. Its existing null blueprint.from.node and via chain were retained, with its precise source place. Whole-blueprint searches for deletion, contracting, contractible, pointed and tensor additive find no other blueprint node stating this item. No unit realization was changed: this is not a unit's key node.

## Mathlib findings

The required search command ran LeanFinder, Loogle, grep in AlgebraicTopology, and LeanSearch, with two different natural-language phrasings. All four services returned results, so no unavailable result is recorded. Read ExtraDegeneracy.lean around lines 405–435: CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv assumes the augmented simplicial object and extra degeneracy already given. Establishing the specific free internal terms and insertion maps remains work; it does not state this whole item in one specialization. RepresentationTheory's classifyingSpaceUniversalCover results are for ordinary rings and monoids. The ShortComplex.Splitting results found by LeanSearch are abstract consequences once a splitting is supplied. They do not provide the construction and identities in the item. The exactness consequence here is only a few-line kernel factorization, so it is a step rather than a new node.

## Tool uses

- lem-pe-internal-section-tensor-comparison is a generic tool for the actual relative tensor of internal modules, on any appropriately small site, with the comparison respecting unitors. It is not used to replace a geometric route. The current unit has no statement giving this general comparison.
- lem-pc-sheaf-modules-tensor-closed supplies additivity and the unit of section-module tensor. It is used through that comparison for arbitrary T. The existing free-product/tensor lemma only concerns two free objects and cannot establish this arbitrary-module claim on its own.

These two off-unit statements are declared in split_report.tool_uses for maintainer review. No tool_uses field was set directly. lem-pur-ringed-site-module-category-abelian is already a Mathlib leaf. All other proof ingredients are existing definitions or the same-unit free linearization node.

## Not duplicates

No new nodes were created. In particular, no new node was made for double-deletion cancellation, insertion contraction, naturality, kernel-factorization exactness, or preservation of these identities by an additive functor: their explicit arguments are the item's steps. The free-generator result is already lem-sfb-condensed-free-linearization-tensor, which is cited rather than restated as a new dependency.

## Review by Q125

I read the item against its source paragraph (3) and the parent lem-sfb-condensed-internal-bar-resolution. That paragraph does not furnish a ready-made proof of this pointed-set generalization, so the proof origin is agent, and an independent reference remains WANTED. I also read the statement of every node used below. No new node needs a separate source review.

Step 1 uses the free-forgetful adjunction of def-sfb-condensed-free-module-adjunction and the generator characterization of lem-sfb-condensed-free-linearization-tensor. The latter really states that natural assignments on all generalized generators determine internal linear maps, identifies the functorial generator map, and identifies A[1] with A. The insertion of the global point and deletion commute with every restriction, so the maps constructed are internal, not merely maps on global sections. I did not assume that A[X](S) remains a free module after sheafification.

Step 2 uses only that same generator detection. I checked both ordered deletions of each original pair i<j: their signs are (-1)^(i+j) and (-1)^(i+j-1), respectively. This gives the zero composite in positive degrees; the separate degree-zero composite is 1-1. No simplicial homotopy theorem or uncited general exactness lemma is being applied.

Step 3 again uses generator detection, with the degree-zero identity checked separately. The first face of [e,x_0,...,x_n] gives the identity, and the remaining faces have signs (-1)^(i+1), opposite to insertion after deletion. The augmentation identity holds on every local scalar a. Step 4 explicitly uses f(e)=e' in addition to generator detection, proving the stated pointed naturality. A non-pointed map would fail this calculation, and none is allowed.

Step 5 uses def-weil-pbc-internal-abelian-sheaf-module-equivalence exactly for its equivalence with section-module sheaves and lem-pur-ringed-site-module-category-abelian exactly for abelianness. The site is small by the item's size convention, and A is commutative. I checked the latter node's Mathlib source Algebra/Category/ModuleCat/Sheaf/Abelian.lean, lines 16–23 and 40–42, and Stacks sites-modules.tex Tag 03DA, lemma-abelian. The kernel computation is written out: d_(n+1)=kq and the contraction give q h_n k=id, so q is split epic and its image is the whole kernel. Equivalences preserve these universal properties. This is a short elementary consequence, not an extra lemma hidden behind 'exactness follows'.

Step 6 cites lem-pe-internal-section-tensor-comparison for exactly its natural internal/section tensor isomorphisms and its compatibility with unitors, det-def-sfb-sheaf-tensor-structure for monoidal sheafification, def-sfb-modobj-relative-tensor for the coequalizer tensor and regular unit, and lem-pc-sheaf-modules-tensor-closed for additivity in each variable. The comparison's size and sheafification hypotheses hold on the coherent profinite site in the given coefficient universes. I read Stacks sites-modules.tex Section 03EK (section-tensor-product), Lemma 0GMW (lemma-sheafification-tensor) and Lemma 03EO (lemma-internal-hom-adjoint-tensor). These are supporting references for the existing nodes, not substitute citations for a missing step. Functoriality and additivity then carry each displayed equation to its tensor image. I checked the degree-zero unitors explicitly: the two middle unit identifications cancel in H_-1 D_0, and D_0 H_-1 becomes the identity on T.

Step 7 cites the same equivalence and abelianness statements as step 5, and repeats the kernel-factorization argument with the tensored differential. It does not assert that tensor is exact on arbitrary sequences. This is why arbitrary T is permitted. Its augmentation is split epic by the tensor image of the given section.

For the B–E review I checked that every cited fact is literally in the node's statement (citations.json contains verified verbatim substrings), that every non-elementary ingredient has such a citation, and that proof_deps is the union of uses. No new statement repeats a clause of the item. Every step is shorter than 2000 characters; the longest is 1030. The elementary flags apply to explicit finite-sum identities, functorial constructions, and the displayed kernel argument. The tensor structural step is marked non-elementary and has its full citations.

I tested the small cases: n=0 gives d_1[e,x]=[x]-[e]; n=1 gives cancellation in d_1d_2 and d_2h_1+h_0d_1=id. For X=1, Q_n=A and the differentials alternate between zero and the identity after augmentation, as required. The zero ring and T=0 give zero-object identities. In characteristic two the paired coefficients still sum to zero. A non-flat T is allowed because only additive functoriality is used. The empty condensed set has no global point and is outside the hypotheses. Nothing uses a group law or equivariance of h.

No mathematical task is left unfinished in this split; the independent source request is recorded transparently. Server dry-run diagnostics will be repaired before delivery.
