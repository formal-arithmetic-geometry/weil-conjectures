# Q56 stage-1 delivery

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-semisimple-scalar-extension-kzero-criterion.json`: item, split into five steps; statement unchanged; no exact project Lean attachment or Mathlib match found.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-matrix-division-module-classification.json`: new statement, unsplit; no exact Mathlib match or one-line specialization found.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-algebra-hom-scalar-extension.json`: new statement, unsplit; no exact Mathlib match or one-line specialization found.
- `citations.json`: one entry for each cited node in each item step, quotes copied verbatim from the statements.

There are two new nodes and zero new Mathlib leaves. Existing Mathlib leaves `lem-per-semisimple-algebra-matrix-division` and `lem-sfb-simple-algebra-scalar-endomorphisms` are reused. No Lean was written or compiled, and the shared repository was only read.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag, semisimplicity, Schur, Grothendieck groups, scalar extension and Hom comparisons. The existing composition-factor and representation files do not state this criterion for arbitrary finite-dimensional associative algebras.

## Literature requested

WANTED: Serre, *Linear Representations of Finite Groups*, Part III, fields of definition and Schur indices, for the representation lifting context before ILO Expose X Proposition 1.2 (5), and hence for `lem-per-semisimple-scalar-extension-kzero-criterion`.

I read ILO printed p.138 (PDF p.144), in particular the paragraph between (4) and (5) citing Serre 12 2.3 and 13 14.4. It supplies the representation lifting context, not this algebra criterion. The item proof is therefore explicitly agent-written. No forbidden SGA source is used. The current blueprint is `literature/blueprint/latest/`; I read its `lem-per-artin-gabber-affine-curve.md` and `.proof.md` and the recorded chapter/unit. The inherited ancestry describes an auxiliary algebra prerequisite on the existing Gabber route, not a quotation of the latest affine-curve proof. Neither the unit nor the chapter is changed.

## What was checked and changed

The imported statement is correct and unchanged. Its empty proof is replaced with an argument through the simple modules of the specified matrix factors. We do not merely move the criterion into a new node: neither new statement mentions representation groups, surjectivity, algebraic closures or splitting of division factors. The item itself proves the integral multiplicity argument and the resulting dimension-one conclusion.

The new matrix-module node follows Stacks Tag 074E, `brauer.tex`, `lemma-simple-module-unique`, parts (1)--(4), with the matrix-module equivalence in Tag 074D, `lemma-matrix-algebras`. I read both statements and the proof of 074E. Mathlib's `ModuleCat.matrixEquivalence` at `RingTheory/Morita/Matrix.lean:187--194`, its functors and linear refinement, provide the equivalence but not the full specified-column classification with unique finite multiplicity and explicit opposite endomorphism algebra in a one-line specialization. Wedderburn-Artin constructs matrix factors; it does not classify modules over a given factor with the requested identifications. The new node remains unsplit.

The new Hom node is deliberately not attributed as an exact consequence of Stacks 087R: I read `more-algebra.tex`, `lemma-pseudo-coherence-and-base-change-ext` (1), which is the commutative-ring Hom comparison. The new statement allows a noncommutative acting algebra. Its proof rationale is finite coefficient extraction: choose K-bases of V and W and express the finitely many matrix entries of an L-linear intertwiner as a linear combination of finitely many K-linearly independent elements of L. Write its matrix as a sum of these independent coefficients times matrices over K. Commuting with the action matrices, whose entries are over K, implies separately that each coefficient matrix is A-linear. This gives surjectivity. For injectivity, express a finite tensor sum using independent coefficients in L; if its image matrix vanishes, every coefficient matrix vanishes. The map preserves composition and identity by evaluation on pure tensors. This argument works for an arbitrary field extension, including an infinite extension; neither a finite extension assumption nor commutativity of A is used. The new node is statement-only; this rationale stays here.

All required search kinds and second natural-language phrasings ran through the supplied msearch command. Queries and actual result records are in `searches.jsonl`; the later batch's full hits are retained in `search-results.txt`. Sources for the relevant hits were read: the matrix Morita equivalence above, `RepresentationTheory/AlgebraRepresentation/Basic.lean:22--32`, `RingTheory/TensorProduct/IsBaseChangeHom.lean`, and `Algebra/Module/FinitePresentation.lean:696` onward. The latter comparisons concern maps over the commutative coefficient ring, so they do not by themselves impose A-equivariance.

## Not duplicates

`lem-per-matrix-division-module-classification` vs `lem-per-semisimple-algebra-matrix-division`: the existing node decomposes the algebra; the new node classifies modules of a specified matrix algebra and identifies the opposite endomorphism algebra. No existing node sourced at Tags 074D or 074E was found.

`lem-per-finite-algebra-hom-scalar-extension` vs `lem-weil-pbc-flat-base-change-hom-finitely-presented`: the existing node concerns Hom over the scalar ring R and base change of that ring; the new node concerns Hom commuting with an additional, possibly noncommutative algebra action A and base change of both A and its representations. This is not an application with R=A, since the existing commutative-ring tensor comparison cannot be specialized to a noncommutative algebra. Their source relation to 087R is an analogy, explicitly recorded as such.

I also searched the whole DAG and the imported blueprint for matrix algebras, division algebras, simple modules, Schur, scalar extension, Hom, intertwiners and the source tags. The existing scalar-Schur node was found and reused, rather than creating its general-algebra version anew. `lem-wf-schur-scalar` only concerns a group action over a fixed Qbar-l coefficient field; it was not used for an arbitrary algebraically closed Omega.

`lem-per-finite-algebra-hom-scalar-extension` vs `lem-weil-pbc-completion-internal-hom-affine-sections-lift`: the existing statement lifts compatible morphisms on formal quotient systems over an affine open of a Noetherian scheme; the new statement is an arbitrary field-extension comparison for finite modules with a possibly noncommutative algebra action.

`lem-per-finite-algebra-hom-scalar-extension` vs `lem-weil-pbc-completion-internal-hom-quotient-annihilation`: the existing statement is annihilation by an ideal at a quotient level; the new statement is bijectivity of the Hom tensor comparison under a field extension, with no ideal or quotient level.

`lem-per-finite-algebra-hom-scalar-extension` vs `lem-weil-pbc-completion-internal-hom-quotient-isIso`: the existing statement compares internal Hom into a level-n quotient by precomposition with a level-m quotient; the new statement changes the coefficient field and acting algebra and does not factor maps through ideal quotients.

`lem-per-finite-algebra-hom-scalar-extension` vs `lem-weil-pbc-completion-internal-hom-quotient`: the existing statement is ideal annihilation and factorization of internal Hom on a scheme; the new statement is the intertwiner-space comparison for base change of finite algebra modules.

`lem-per-finite-algebra-hom-scalar-extension` vs `lem-weil-pbc-completion-internal-hom-sections-lift`: the existing statement gives compatible global sections of completion quotients from compatible sheaf morphisms; the new statement gives an L-linear isomorphism for an arbitrary extension of fields, without a scheme or completion system.

`lem-per-finite-algebra-hom-scalar-extension` vs `lem-weil-pbc-completion-internal-hom`: the existing statement identifies a limit of global Hom quotient sections with morphisms of coherent formal modules; the new statement identifies extension of a finite-dimensional intertwiner space with intertwiners after extending the acting algebra. It has neither a completion nor an inverse limit.

The first dry run requested these six additional same-tag comparisons. I opened and read every one of their statements; none is a general noncommutative algebra-module Hom comparison.

## Review by Q56

I checked B--E against the source statements and the actual proof. The two new nodes introduce all their objects, define division algebra and the opposite algebra inline where relevant, cite the existing tensor/simple/matrix definitions, have empty proof fields and no proof dependencies, and carry precise inherited blueprint provenance. Every item step is shorter than 2000 characters.

Step 1 uses the new matrix-module classification exactly for its three asserted clauses: the column is simple, finite modules are sums of columns with unique multiplicity, and the endomorphism algebra is the opposite division algebra. The passage from one matrix factor to the product is written out using the orthogonal central idempotents; it needs no separate product-module theorem. Positivity of d_i and nonzeroness of D_i ensure S_i is nonzero. The empty product is handled before fixing i.

Step 2 applies the existing Wedderburn-Artin node to B=A_Omega, whose finite dimension follows from tensoring a finite K-basis of A and whose semisimplicity is explicitly assumed. That node permits any field, the zero algebra and a finite product. The new matrix classification then supplies both existence and uniqueness of all target multiplicities. Additive multiplicities induce maps from the specified split Grothendieck group solely by its presentation; no Jordan--Holder theorem is being hidden or borrowed from a representation-only node.

Step 3 cites the tensor definition only for bilinearity and the induced action. Orthogonal idempotents decompose every module, and on a simple module exactly one component can be nonzero. A nonzero vector space stays nonzero after field extension by its tensor basis, so W_i has a constituent. These are explicit elementary arguments; the tensor definition is not cited as if it asserted a Hom comparison.

Step 4 uses the multiplicity homomorphisms established in Step 2 and disjointness proved in Step 3. Any source class is an integer combination of the S_k because every actual module decomposes by Step 1. The coefficient equation a_i*m_j0=1 forces both positive m_j0 and integer a_i to be 1; all other constituents of W_i then have coefficient zero. This is the key argument in the item itself. Surjectivity only over Q would be insufficient.

Step 5 uses the new Hom node with V=W=S_i, not an unsupported commutative Hom comparison. Its field, finiteness and compatibility hypotheses are all satisfied. The existing scalar-Schur node states precisely bijectivity of Omega to End_B(W_i), for a nonzero finite-dimensional simple module over any associative Omega-algebra. Its Mathlib match was checked at Basic.lean:22--32. The remaining tensor-basis calculation is written explicitly and gives dim_K D_i=1. Since 1_Di is nonzero, it spans, so it is the actual structural map K to D_i that is bijective.

Small cases: for A=K, products K^r and M_d(K) the map on representation classes is surjective and the conclusion holds. For a nontrivial finite separable field L/K, scalar extension sends its simple class to the diagonal vector in Z^[L:K], which is not surjective. For the real quaternion algebra H, its unique simple left module is H; C tensor_R H is the regular M_2(C)-module and has two copies of the standard simple, so the map is multiplication by 2 and fails surjectivity. This confirms why neither noncommutativity nor Schur multiplicity can be ignored. Zero modules satisfy the unique n=0 clause of the matrix lemma; d=0 and the zero division ring are excluded. The Hom lemma also covers V=0 or W=0 with both sides zero. The r=0 case of the item is vacuous. No statement correction or source-error notice is needed.

## Unfinished work

The two new auxiliary statements intentionally remain unsplit for later stage-1 workers. The item has a complete natural-language proof. No requested work is deferred beyond the required independent maintainer review.
