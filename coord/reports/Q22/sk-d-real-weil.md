# sk-d-real-weil — Q22 stage-1 direct delivery

## Files written

- `dag/nodes/sec-purity-real-sheaves/sk-d-real-weil.json`: definition, split; all original mathematical clauses retained, coefficient and topology conventions made explicit; not in Mathlib as a whole.
- `dag/nodes/sec-purity-real-sheaves/lem-real-compact-matrix-coefficient-descent.json`: statement-only auxiliary, not in Mathlib; exact finished source-library declaration found and reported below. This node is not split or reproved.
- `dag/units/sk-d-real-weil.json`: only `realized` and `realized_by`; the unit has no separate numbered steps.
- `citations.json`: for every proof-step citation, the verbatim cited statement. Full statements are copied to make the hypotheses and scope visible.

One new node, zero Mathlib leaves. All work is in the sandbox. No Lean was written or compiled, no git command was run, and no source-library/repository/launcher file was changed.

## Attachments

`PadicAlgCl.exists_finiteDimensional_forall_mem` belongs to `lem-real-compact-matrix-coefficient-descent`, `lean/WeilConjectures/RepresentationTheory/IntegralModel.lean:58` (proof through line 128).

I read the full theorem and proof: a compact topological group, a finite matrix index type including the empty type, a monoid homomorphism into matrices over the algebraic closure, and coordinate continuity give one finite intermediate coefficient field for every matrix entry. This is exactly the new node. The read-only `local/sorry_map_slopmaster2_full.jsonl.gz` entry for this declaration has `s=false`, `ts=false`. The declaration is mentioned in the proof of `det-sf-comp-continuous-algcl-heart-finiteness`, but that node states a proper-direct-image constructibility assertion, not coefficient descent for an arbitrary compact matrix representation. The attachment is reported for the maintainer; the delivery tool preserves its own authority over attachment metadata.

The entire item cannot be attached. `AlgebraicGeometry.WeilGroup`, `.IsLisse`, `ofFundamentalGroup`, and `isConj_frobenius_of_isFrobeniusElement` cover individual group, predicate and conjugacy clauses, but do not give the complete sheaf definition, coefficient criterion and constructible clause in the item's actual etale adic convention. The pro-etale equivalence in `SheafRepresentation.lean` is not silently identified with that etale adic convention. The existing DAG comparison node is reused as stated.

## WANTED

None. Read Deligne, *La conjecture de Weil II*, (1.1.1), pp. 146–147, (1.1.6), p. 150, (1.1.8), (1.1.10)–(1.1.13.1), pp. 151–153; and Stanford Weil II L19, Definition 1.1.7, Proposition 1.1.9, Proposition 1.1.11 and the beginning of the proof of Proposition 1.1.12, pp. 2–5. These documents are present under literature/. No SGA source was used.

## Corrections and clarifications

The imported definition bundled real theorem clauses but had only the Frobenius path argument in its proof, with no judged elementary flag or dependencies. The split now accounts for degree exactness, finite coefficients, lattice existence, the existing sheaf/representation equivalence, and Frobenius degree and conjugacy. The topology must be the topology from G times discrete Z, not the subspace topology from G alone (Deligne p. 152, L19 Definition 1.1.10). This makes explicit the imported sentence “The quotient Z is discrete”. The source library already implements that topology.

The item now says which global lisse adic Weil pairs and stalk functor are meant, and spells out the constructible version of the same etale adic coefficient convention from Weil II (1.1.1). A constructible sheaf still includes its global gluing and global Weil isomorphism; it is not independent data on a list of strata. The finite stratification clause is retained. These are definition clarifications, not a changed theorem, target, or extra hypothesis.

The new coefficient-descent lemma is independent of curves, Weil sheaves, Frobenius, or degree data. It isolates the compact-group/Baire input. It is neither the item nor a new node restating its finite-model criterion: after this lemma the item's proof must still adjoin the degree-one operator and its inverse, prove stability under the entire Weil group, obtain a geometric lattice, and relate the representations to sheaves. Its exact project proof is already finished.

The local conjugacy argument is written using restriction to the finite residue field rather than leaving the arithmetic of Z-hat implicit. If r(g) has the same residue restriction as gamma_k^n, sigma=gamma_k^(-n)r(g) belongs to the residue Galois group. Its image centralizes F_x and removes the nonintegral degree of g. This is Deligne's centralizer argument and is equivalent to the imported Z-hat argument.

The unit record is the older master wording; the node and the current main-20261015 blueprint explicitly formulate lissity by coordinate continuity. I used the current node and source, as instructed, and changed only the unit's realization fields.

## Not duplicates

- `lem-real-compact-matrix-coefficient-descent` vs `lem-pod-profinite-stable-lattice`: the new node produces a finite coefficient field from a continuous matrix representation over the algebraic closure; the existing lattice theorem assumes a finite coefficient field and produces a stable lattice. Both are needed, in that order.
- `lem-real-compact-matrix-coefficient-descent` vs `p-real-integral`: the latter starts with a Weil sheaf/representation with a given coefficient field E and asks for its geometric lattice; it does not state arbitrary compact matrix coefficient descent.
- `lem-real-compact-matrix-coefficient-descent` vs `det-lem-coefficient-finite-descent-lisse` and `lem-sfb-lisse-finite-coefficient-model`: those descend lisse sheaf objects in specified pro-etale coefficient categories. This is a coefficient-free-in-geometry compact group theorem, with matrix continuity as its hypothesis; invoking those would require constructing the sheaf first.
- `lem-real-compact-matrix-coefficient-descent` vs `det-sf-comp-continuous-algcl-heart-finiteness`: the existing statement concerns proper higher images. Mentioning the project theorem in its proof does not make that node state the project theorem.
- `lem-real-compact-matrix-coefficient-descent` vs `sk-d-real-weil`: the item concerns a specific Weil group, sheaves and finite-model/lattice equivalence; the auxiliary concerns arbitrary compact groups and matrix homomorphisms, and does not mention Weil sheaves, lattices or descent operators.

Searched the entire DAG by coefficient-descent/compact subgroup/Baire/matrix-coefficient terminology and the exact source declaration, then `tools/blueprint_refs.py search` for compact subgroup, compact matrix, finite coefficient, coefficient field descent, matrix coefficients, Weil group, Frobenius and finite-dimensional continuous. None states this general coefficient-descent lemma. I inspected the candidates above, rather than treating absence of a tag as absence of a duplicate. No new node carries a Stacks tag shared with another node. The item's `same_as=[]` means no other blueprint node states the whole compound definition: `def-wf-weil-group` and `def-wf-fundamental-representation` only supply parts and are reused explicitly.

## Mathlib searches

Every recorded query was actually run through msearch.py and read. The complete command log is `searches.jsonl`; there was no earlier item split or earlier search log to reuse. Each node has leanfinder, leansearch, loogle and grep, with a second semantic phrasing. The item grep for WeilGroup/WeilSheaf/WeilRepresentation and Loogle for WeilGroup found nothing in Mathlib; the semantic hits were finite Galois-category/Frobenius, isocrystal and condensed-category facts. None states the compound item.

For the auxiliary, the compact-group matrix/descent queries returned compactness of Krull Galois groups, open fixing subgroups, general finite-dimensional linear continuity, arithmetic subgroups of GL, and Galois inverse-limit maps. Loogle `IsCompact, Matrix.GeneralLinearGroup` and the coefficient/compactness grep found no matching theorem. These ingredients are not one-line specializations yielding finite coefficient descent. The theorem was subsequently located in the project library, not Mathlib, and is reported as an attachment. No Mathlib match is claimed and no result or query has been invented.

## Review by Q22

I compared the node with the full current blueprint section, its older unit record, the chapter contract, Deligne's actual definitions and paragraphs, and L19's definition/classification discussion. The sources agree on inverse-image Weil group, product topology with discrete integer quotient, no Frobenius-stable integral lattice requirement, and geometric local Frobenius with degree equal to residue degree. I checked the full statements of all cited nodes, and the closures of those nodes do not point back to this item.

Step 1 uses `lem-wf-arithmetic-lift-fibre-path` for an actual exact sequence, not merely a definition of the arithmetic projection. The hypotheses hold: k_0 is perfect, C_0 is separated finite type, C is connected and a geometric point is chosen. `sk-d-real-setup` supplies these curve assumptions. `def-wf-fundamental-representation` explicitly says the topology is induced from G times discrete Z. Taking the fibre product then proves the exact integer degree sequence directly; I did not copy the older flawed informal phrase that treats Frobenius itself as a pre-existing element of G.

Step 2 takes only profiniteness from `lem-galois-aut-profinite`, whose finite-fibre/small-category hypotheses hold on a small skeleton of finite etale covers. The new coefficient lemma says exactly that all entries of this continuous finite matrix homomorphism lie in one finite field. I checked its source theorem, its proof, its sorry-map entry, and its empty-index case. The remaining step is explicit finite algebra: adjoin entries of F and F inverse, write w=h gamma^n, and check finite-coordinate joint continuity. It does not claim that arbitrary compact subsets of Qlbar lie in finite subextensions; compact *group representations* are essential.

Step 3 applies `lem-pod-profinite-stable-lattice` only after constructing E and joint continuity in step 2. That theorem explicitly supplies the full free stable lattice, its rank and the adic topology. The reverse implication is the written fixed-change-of-basis finite-sum formula. A constant rank-one Weil sheaf with F acting by ell or ell inverse is allowed; the geometric lattice is stable while F need not preserve it. No invariant lattice for W was accidentally imposed.

Step 4 cites the statement of `prop-wf-weil-sheaf-representation-equivalence`, which explicitly gives an exact tensor equivalence and its stalk representation, and the actual etale adic definition `def-wf-fundamental-representation`. It does not use a pro-etale equivalence or a sorried declaration as a finished proof. This is an existing lemma reused; no clause is delegated to a newly created restatement. The constructible part is a definition using a global sheaf and global Weil datum. The finite-ring constructibility definition and finite-stratification definition are direct statement dependencies, and lisse adic coefficients are specified on the strata. I did not claim an unsupported etale/pro-etale coefficient comparison.

Step 5 uses the fibre-evaluation formula of `lem-galois-pi1-functoriality`, the natural path isomorphisms of `lem-wf-fibre-functor-basepoint-transport`, and the explicit constant-cover characterization of r in `lem-wf-arithmetic-lift-fibre-path`. These give a homomorphism on the actual residue Galois group and identify its constant projection. Acting on geometric points of every cover is the definition of that natural automorphism; no decomposition-group injection beyond it is needed. Gamma_x is the inverse q^e power map, so its constant exponent is positive e, not negative e.

Step 6 takes exactly inner conjugation under changing a path from the path node, cyclic finite-field Frobenius from `lem-sfb-finite-field-galois-frobenius`, and abelianness of the residue Galois group from `det-base-field-cd-galois-group`'s isomorphism with the inverse limit of cyclic groups. The finite extension kappa(x)/k_0 has degree e_x>=1. The displayed sigma lies in the subgroup fixing kappa(x); its image a commutes with F_x; w=g a inverse then has integral degree and gives the same conjugate. This is a calculation with two justified finite-field inputs, not a hidden conjugacy theorem. Changing the residue embedding is covered by the algebraic-closure isomorphism over kappa(x) and the same path argument. No equality of conjugacy classes in G was silently substituted for conjugacy in W.

I checked B–E of delivery-errors.md: statement-only new node, all objects introduced, notion dependencies present, TeX encoded once, sources at their actual numbered places, real recorded searches, blueprint ancestry explicit, exact source attachment distinguished from Mathlib; every used theorem is in the cited statement and in citations.json. Existing smaller results are reused. All non-elementary steps are marked false and explicitly cite their mathematical inputs; none exceeds 2000 characters. There are no new theorem statements carrying an inline proof and no relocated whole-item argument.

Small cases checked: rank zero/empty matrix index (vacuous coefficient conditions, E=Ql, zero lattice); trivial geometric action with a nonunit degree-one scalar; e_x=1 (take n=0 and correct every g by a residue Galois element); general e_x (finite cyclic restriction gives n modulo e_x); unchanged path; and changing embeddings. The curve is nonempty and geometrically connected, so degree surjectivity is not used on a disconnected scheme. There is no statement dispute or abandoned clause. I corrected the initially incomplete coefficient/lattice accounting, the unrecorded topology and the global-constructible ambiguity while keeping the source's mathematical content.

## Unfinished work

None in this stage-1 split. The single new auxiliary is reported for attachment to its already finished source-library proof. Its status remains statement-only pending the maintainer's attachment bookkeeping. The existing representation equivalence remains its own DAG item; this delivery does not claim to prove or attach it.
