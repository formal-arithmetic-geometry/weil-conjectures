## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-cyclotomic-field-brauer-splitting.json: item, split; unchanged statement, five-step proof.
- dag/nodes/sec-deligne-laumon-a1/lem-per-maschke-finite-group-algebra.json: statement, Mathlib leaf, MonoidAlgebra.Submodule.instIsSemisimpleModule at Mathlib/RepresentationTheory/Maschke.lean:168.
- dag/nodes/sec-deligne-laumon-a1/lem-per-brauer-monomial-induction.json: statement only, unsplit, no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-semisimple-scalar-extension-kzero-criterion.json: statement only, unsplit, no Mathlib match.
- citations.json: verbatim statement quotes for every citation of each numbered step.
- searches.jsonl: actual msearch records; the new nodes reproduce the corresponding query strings and results. write_split.py is the sandbox-only generator.

## Attachments

None. Searches of lean/WeilConjectures for the item tag, cyclotomic splitting, Brauer induction and Schur index found no exact finished declaration. Existing character and scalar-extension declarations do not assert this result. No Lean was written or compiled.

## Wanted sources

WANTED: J.-P. Serre, Linear Representations of Finite Groups, Part II Chapter 10, Brauer induction and its monomial-character consequence, for lem-per-brauer-monomial-induction. Need the version over any algebraically closed characteristic-zero field, or its transfer from the complex case.

WANTED: J.-P. Serre, Linear Representations of Finite Groups, Part III, fields of definition and Schur indices, for comparison with the agent auxiliary lem-per-semisimple-scalar-extension-kzero-criterion. The original item also requests Serre 1978, 12 section 2.3 and 13 section 14.4. No book was downloaded. A web search corroborated the monomial consequence in Chapter 10; the actual book is not an obtained local source and is not represented as one.

## Corrections and provenance

No statement dispute or change. The original item had no proof. Its reference to Gabber p.138 is a reference to an input, not a proof of Brauer splitting. I read printed pp.138-140 (PDF pp.144-146): p.138 invokes Serre to lift V_0 to a projective Lambda[G]-module before equation (5); p.139 localizes the cyclotomic coefficient ring. The five-step proof is marked agent-written, and the two unsplit non-Mathlib nodes are explicitly auxiliary inputs, not falsely attributed as theorems proved in that passage.

The current latest blueprint was read at literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md. Its Step 3 concerns duality and does not itself state the representation theorem. The ancestor and inherited chain are retained; the from.place refinement names the representation lifting before equation (5). The unit and chapter are unchanged; the item is not the unit key statement.

## Not duplicates

lem-per-maschke-finite-group-algebra vs lem-per-semisimple-algebra-matrix-division: the new Mathlib leaf proves semisimplicity from nonvanishing group order, while the existing node assumes semisimplicity and decomposes an arbitrary finite algebra.

lem-per-brauer-monomial-induction vs lem-per-cyclotomic-field-brauer-splitting: the new node asserts integral generation of virtual representations over an algebraically closed field, with no root hypothesis and no assertion about forms over smaller fields. The item proves descent of the inducing characters and matrices, applies the independent scalar-extension criterion and assembles the algebra isomorphism.

lem-per-semisimple-scalar-extension-kzero-criterion vs lem-per-cyclotomic-field-brauer-splitting: the criterion has no group, exponent or roots of unity and requires surjectivity on representation classes; it does not establish that surjectivity. It detects division factors in a given general algebra decomposition, whereas Steps 2-4 of the item prove its essential hypothesis.

lem-per-semisimple-scalar-extension-kzero-criterion vs lem-per-semisimple-algebra-matrix-division: the existing node supplies a decomposition with arbitrary division factors. The criterion makes an additional scalar-extension hypothesis and proves structural maps to those factors are bijective.

Whole-DAG statement searches for Maschke, Brauer induction, Schur index and representation Grothendieck groups, together with blueprint_refs searches for Brauer, semisimple algebra, induction character, monomial representation, Maschke, division algebra and split Grothendieck, found no existing statement of these new facts. The existing generic Wedderburn-Artin and algebraic-closure Mathlib leaves are reused. No new node cites a Stacks tag also used by an existing node; these two representation-theoretic assertions have no identified exact Stacks tag. They are not disguised new versions of a Stacks theorem.

## Auxiliary proof rationale for the next workers

The unsplit new nodes themselves contain statements only, with no proof_deps or proof sketch.

For Brauer induction use the integral monomial-character consequence, not Artin induction with rational coefficients and not an assertion that each irreducible representation is monomial. Maschke and character independence identify characters with the direct-sum representation group over an algebraically closed characteristic-zero field. A proof from the complex version must justify transfer to an arbitrary algebraically closed characteristic-zero field. This work belongs to the new node, and is not assumed elementary in the item.

Here is a complete rationale for the general scalar-extension criterion, to make its future split concrete. Let S_1,...,S_t represent the simple A-modules. Semisimplicity makes R(A) the free abelian group on the S_i, by uniqueness of multiplicities. Similarly R(A_Omega) has the simple A_Omega-modules T_j as a basis. For finite-dimensional A-modules U,V, choosing finite bases turns A-linear Hom into the kernel of the finite matrix of equations f(av)=af(v) for a basis of A. Extending a field preserves the kernel (row reduction of that matrix works over either field), hence Omega tensor Hom_A(U,V) is Hom_{A_Omega}(U_Omega,V_Omega). In particular, distinct S_i have zero Hom even after extension. Since A_Omega is semisimple, the sets of simple constituents of (S_i)_Omega are therefore pairwise disjoint. Each (S_i)_Omega is nonzero, as a K-basis stays an Omega-basis after extension. Write its multiplicity vector as v_i with nonnegative integer coordinates and nonempty support. Surjectivity of s means the v_i span the whole integer lattice on the T_j. A basis vector in the support of v_i can only be made from an integer multiple of v_i, since all other supports are disjoint. Thus each support is a singleton and its multiplicity is exactly one. Every (S_i)_Omega is simple. Its endomorphisms over the algebraically closed field are scalar: a linear endomorphism has an eigenvalue, and the kernel of f-lambda is a nonzero submodule, hence the whole simple module. The Hom base change above then gives dim_K End_A(S_i)=1. For each displayed factor M_d(D), its column module D^d is simple: matrix units move a nonzero coordinate to any coordinate, and inverses in D produce arbitrary columns. Endomorphisms commuting with all matrix units and left multiplication by D are right multiplication by a common element of D, so its endomorphism ring is D^op. Inflation to the product preserves this simplicity and endomorphism ring. Therefore dim_K D=1 for every supplied factor. The nonzero unit 1_D is a basis, so the central structural map K to D is bijective. This argument also treats the zero algebra (no factors); the item separately rules out zero. No centrality of D over K, nor a prior identification of its centre with K, was assumed.

## Review by Q22

I checked delivery-errors B-E against the files, the current blueprint and Gabber pp.138-140. Every new statement introduces its objects and defines its potentially ambiguous notions inline: group algebra, semisimplicity, virtual/direct-sum representation group, induction, division algebra and scalar extension. The common tensor, matrix and algebraic-closure notions cite their existing definition nodes. Both new non-Mathlib nodes have empty proof and proof_deps; only the item is split. No old imported metadata was removed. No source prohibited by the route lock is used.

Step 1 uses exactly the new Maschke conclusion, the existing finite-dimensional Wedderburn-Artin decomposition and the existing existence of an algebraic closure. I opened all three statements and copied their relevant statements into citations.json. Nonzero group order follows from characteristic zero, A is finite-dimensional from its finite group basis, and [1] excludes the empty product. The Mathlib source at Maschke.lean:140-169 was read directly: the regular-module specialization is available without algebraic closure. WedderburnArtin.lean:201-205 was also read; it gives finite division factors, not split factors.

Step 2 proves the root assertion directly: distinct powers use the exact-order hypothesis, and a degree-N monic polynomial with N distinct listed roots has no additional roots. This uses no unstated splitting-field theorem. For N=1 it says the only root is 1, as required.

Step 3 uses exactly integral generation by induced linear-character classes in the new Brauer node. Every value is an Nth root because h^N=1 also in a subgroup. The coset construction explicitly supplies a K-model and verifies its multiplication and its scalar extension in the quotient convention actually stated by the cited node. Negative coefficients are allowed because the group is defined using integer combinations. This step does not assert that a virtual class is an actual representation or that each irreducible is induced from a linear character. No character-value-only descent shortcut is used: the quaternion representation over Q is a counterexample to that shortcut, while Q(i) contains the exponent-four roots and the present proof supplies the missing descent mechanism.

Step 4 uses only the stated convention of the criterion and the tensor universal property. Both are opened and quoted verbatim. The displayed two inverse maps identify A_Omega with Omega[G] on bases, including their multiplication; module actions correspond to group actions by restricting to invertible basis elements. Thus the surjectivity proved in Step 3 is exactly the hypothesis needed later, rather than an unproved comparison of two meanings of representation classes. This step is elementary assembly of these definitions and explicit inverse maps.

Step 5 uses Maschke again and the full statement of the criterion. I checked that Omega has characteristic zero, A_Omega is semisimple, s is surjective, and the decomposition is already available. Entrywise application of inverse structural maps is a K-algebra isomorphism and keeps all positive matrix sizes. Every cited fact has a verbatim quote. The first dry run required explicit definition-node citations in the new Maschke node despite its inline definitions; I added def-weil-field and def-weil-pbc-simple-module, read their statements, and regenerated the citations without changing the mathematical argument. All proof steps are under 800 characters, so no step exceeds the long-step threshold.

For the new criterion I checked split products K^r, M_d(K), the zero algebra, a nontrivial finite extension L/K and quaternion division factors: the latter two fail surjectivity respectively by tied constituent coordinates and a multiplicity greater than one. The disjoint-support argument in the rationale handles both field-of-values and Schur-index obstructions. For Brauer induction the trivial group is generated by its unique linear character; nonmonomial irreducibles require integer combinations, as the statement allows. In the item G={1} gives r=d_1=1 and N=1 forces G={1}. No hypothesis was added to the item, and no clause was weakened.

## Unfinished work

No part of the item's one-level split is left unwritten. Brauer induction and the general scalar-extension criterion are deliberately statement-only next-stage DAG work. Serre remains WANTED, so the item has honest agent proof provenance. Delivery awaits the mandatory server checks and push.
