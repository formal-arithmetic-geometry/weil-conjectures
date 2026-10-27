## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-tannaka-rational-point-reconstruction.json`: item split into ten proof steps, statement unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-rational-representation-comodule-dictionary.json`: new statement-only lemma, not a Mathlib match.
- `citations.json`: verbatim statements for every node used in every proof step, indexed from 1.

One new node; zero new Mathlib leaves. No attachments. No WANTED documents. No unfinished mathematical obligation beyond the deliberately unsplit supporting dictionary node.

The project search by the exact blueprint id and by Tannaka, coaction, comodule, tensor automorphism and rational representation found no declaration giving the item. The upstream `GeneralLinear/Representation.lean` only constructs the abstract point representation and its simplicity/semisimplicity predicates, not reconstruction. In particular its field-point terminology cannot replace rational equivariance over every algebra for a nonreduced group.

I read Milne, *Algebraic Groups* (2017), Chapter 9(a), Lemma 9.1 and Theorem 9.2, printed pp.163--165; Chapter 4(a), Remark 4.1, equations (24)--(25), printed pp.83--84; Proposition 4.7/Corollary 4.8, printed pp.86--87; and Proposition 4.12, printed pp.87--88. These are in `literature/milne-algebraic-groups_iAG2017.pdf`. The proof follows Theorem 9.2 and spells out its omitted extension, tensor compatibility and uniqueness calculations. Lemma 9.1's conclusion is derived explicitly by applying the counit, so it is not hidden in a new reconstruction node. Likewise Proposition 4.12's equivariance and injectivity are its two coaction axioms and are written directly in step 9.

The item is a special case of Milne's theorem: base field algebraically closed and R=K, with the extra assumption that the given maps are invertible. Milne does not need the latter assumption; preserving it does not change the item. No statement dispute was found. No hypothesis or clause of the original statement was changed.

## Blueprint and reuse

Read the chapter record, the recorded unit `sk-thm-sf-ctf-stability`, and the latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and direct-image proof. This supporting algebraic-group lemma is below the imported alteration prerequisite recorded by the item; no chapter or unit route is replaced. `blueprint_refs.py ancestor` explicitly returns a null nearest blueprint ancestor for this imported chain; that value and its via chain are retained, with the exact Milne supporting place appended for the new node. The latest blueprint proof now phrases its direct-image step via proper base change/open-coefficient preservation; the inherited long historical ancestor explanation is provenance, not an additional lemma used in this proof. No unit realization fields belong to this auxiliary item.

Whole-DAG searches by Tannaka, regular representation, coaction, comodule, matrix coefficients, rational representations and Milne 4.1/4.12/9.1/9.2 found the existing finite-subrepresentation and Hopf nodes. I read their statements and reused them. Whole-blueprint searches (`blueprint_refs.py search`) for tannaka, regular representation, comodule, coaction, rational representation, tensor automorphism and coordinate ring produced no node stating the new dictionary. The few rational-representation hits concern affine geometry, Lie stability and tangent comparisons, not this dictionary. No separate node is introduced for the extension of a family, multiplicativity, evaluation at identity, coaction embedding or uniqueness: those are explicit steps of the item's proof.

## Not duplicates

lem-sfb-rational-representation-comodule-dictionary vs lem-sfb-comodule-finite-subrepresentation: the latter starts with a coaction and finds finite stable subspaces; the new lemma converts functorial group actions to coactions, identifies equivariant maps, and describes trivial/tensor actions.

lem-sfb-rational-representation-comodule-dictionary vs lem-sfb-affine-group-coordinate-hopf: the existing node supplies the Hopf structure on the coordinate ring, not the representation/coaction correspondence on a vector space.

lem-sfb-rational-representation-comodule-dictionary vs lem-sfb-hopf-coaction-linearization: the existing theorem converts semilinear module coactions to module descent isomorphisms over an affine action groupoid. It does not state a correspondence with natural group-valued representations, its universal-point formula, or finite-dimensional representability in GL(V).

lem-sfb-rational-representation-comodule-dictionary vs def-wf-algebraic-representations: the existing definition names finite-dimensional group-scheme representations, but asserts no comodule correspondence, particularly for infinite-dimensional spaces.

lem-sfb-rational-representation-comodule-dictionary vs lem-sfb-tannaka-rational-point-reconstruction: the new node has no lambda family and constructs no point; it is a coordinate description of a single representation and its morphisms. All reconstruction remains in the item's argument.

## Mathlib searches

All new-node searches were executed through the required `msearch.py` wrapper and are recorded verbatim in `searches.jsonl` and the node. I tried two semantic formulations, LeanSearch, Loogle and source grep (both the representation directory and the whole source, plus the coalgebra directory). The first LeanFinder search finished before the launcher pause; its actual top hits were preserved in the log and read after resumption. There was no earlier delivery or dry run to repeat.

I read the main candidates: `Mathlib/RepresentationTheory/Tannaka.lean`, especially `TannakaDuality.FiniteGroup.equiv` at line 230, requires a finite abstract group; `AffineScheme.ΓIsEquiv` at `AlgebraicGeometry/AffineScheme.lean:224` is affine antiequivalence; `AffineSpace.homOverEquiv` at `AlgebraicGeometry/AffineSpace.lean:153` parameterizes morphisms by coordinates. `Coalgebra.Repr` and its coefficient sums in `RingTheory/Coalgebra/Basic.lean` describe a finite tensor presentation of comultiplication of one coalgebra element, not a module coaction. `FDRep` represents abstract monoid actions. None states the new node or the reconstruction item, or specializes to it in one line. Further reconstruction queries returned the same finite-group restriction; recorded on the item without replacing its inherited search history.

## Review by Q47

I checked B--E of `coord/delivery-errors.md` with the item, new node, Milne text and each cited statement open. The new node introduces k, G, A, the three Hopf maps, V_R, rational representations, the coaction equations, morphisms, trivial and tensor operations, and the universe convention. Its notions have statement dependencies or explicit definitions. It is statement-only with empty proof/dependency lists, and preserves the exact nonreduced scheme interpretation. Its source is Milne Remark 4.1 rather than an unverified Stacks number; no SGA source is used. I tested the zero space, trivial group, the regular comodule, G_m weights, G_a, and alpha_p in characteristic p. The all-algebras and universal-point requirements are essential for alpha_p and have been retained. Infinite-dimensional spaces are allowed only where the new correspondence and the proof explicitly allow them; the supplied lambda data remain finite-dimensional.

Step 1 uses the coordinate-Hopf node for both coassociativity and counits, and the new dictionary for the regular/trivial/tensor interpretation. I read the displayed Hopf identities and the dictionary formulas, not merely their titles. This permits a possibly infinite-dimensional coordinate ring and imposes no smoothness or reducedness.

Step 2 uses the existing finite-subrepresentation node's actual finite-subset conclusion. Finite spanning sets of two submodules are one finite subset, so the cited statement really gives a common finite-dimensional rational submodule. Equivariant inclusions are supplied by the dictionary. Naturality into that common module proves independence and linearity. No uncited filtered-colimit theorem is used.

Step 3 again uses exactly that finite-subset conclusion for the images of a spanning family. The dictionary's morphism clause identifies coaction preservation with equivariance. During self-review I expanded the injection of Z tensor A into N tensor A, instead of silently using tensor exactness: the existing vector-space-free node supplies a basis of A, the existing free-module definition supplies unique finite coefficient maps, and the tensor universal property constructs the extraction maps. Comparing those coefficients proves injectivity. The node statements quoted in citations.json provide these ingredients. This is an elementary finite-expansion argument within the naturality proof, not a new node.

Step 4 uses the finite-subrepresentation node to choose W and Z and the tensor definition's bilinearity/pure-tensor generation to prove finite spanning and extend equality from pure tensors. The dictionary gives the tensor action and hence equivariance of the canonical map. I use a map into M tensor N, so no unproved assertion that the tensor inclusion is a submodule is needed.

Step 5 uses the dictionary's trivial-action formula; K to T, a to at, is equivariant by direct substitution. Original unit compatibility then gives the identity on every trivial space. No basis of T or infinite direct-sum preservation is assumed.

Step 6 uses the Hopf node's multiplicativity and unit identities and the dictionary's tensor formula to check explicitly that multiplication and the scalar unit are equivariant. Earlier proved naturality and tensor/unit compatibility yield u(ab)=u(a)u(b) and u(1)=1. No algebra-homomorphism property of u is assumed.

Step 7 uses the Hopf node's displayed coassociativity, the dictionary's tensor/trivial/morphism clauses, and the affine-spectrum node's actual full Hom correspondence. The target of Delta has action only on its SECOND factor; this produces Delta u=(1 tensor u)Delta, the required direction. Epsilon u is a K-algebra map, so the spectrum morphism is over K. Affineness is an existing hypothesis, not an inference from finite type.

Step 8 uses the Hopf node's counit identity and the dictionary's evaluation formula to compute u=(1 tensor h-sharp)Delta. I wrote this computation instead of citing Lemma 9.1 as if a DAG node already existed.

Step 9 uses the dictionary's coassociativity and counit equations to prove, directly, that c_V is equivariant into V_0 tensor A and has left inverse 1 tensor epsilon. These facts make it injective without any tensor-flatness theorem. Previous steps give the two equal composites with c_V, hence the required equality on V. The zero representation is included.

Step 10 uses the finite-subrepresentation node to detect equality on each element of A and the dictionary for equivariance and evaluation. The Hopf counit then gives equality of the two coordinate algebra maps. The affine-spectrum statement actually asserts uniqueness of the morphism for a given algebra map, so it proves equality of points. This works for nonreduced G as well, with no density claim or unproved faithful-representation theorem.

All uses have verbatim statement quotations. `proof_deps` is exactly their union. No new node states a reconstruction clause. Every proof step is under 2000 characters (the longest is 996), so none hides a long-step lemma. All non-elementary steps cite the real inputs. I checked the empty finite subset, zero vector space, arbitrary coordinate-ring dimension, trivial group, and nonreduced alpha_p. The latter rules out replacing algebraic representations by representations of the abstract group G(K). I corrected the initially implicit tensor-inclusion argument in step 3 and expanded the citation quotes to cover every clause used. No source error or statement dispute remains.
