# Worker report: lem-sfb-split-reductive-affine-space-quotient

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-split-reductive-affine-space-quotient.json: item, statement unchanged, seven proof steps, status split. Added the actually used proof dependencies and generic tool-use declarations.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-unipotent-extension.json: new statement-only lemma, status unsplit. Mathlib verdict: no match; algebraic unipotence is not abstract group nilpotence or solvability.
- dag/nodes/sec-six-functors-basics/lem-sfb-split-unipotent-affine-torsor-section.json: new statement-only lemma, status unsplit. Mathlib verdict: no match; the returned affine-space definitions, topological trivial bundles, cotangent H1 and Hilbert 90 statements do not state the fppf torsor result.
- citations.json: verbatim statement quotations for all 15 step/node pairs. searches.jsonl is the search command's original log; all new recorded queries were executed through msearch.py and their results read.

## Attachments

None. Searched lean/WeilConjectures/ by the exact blueprint tag, unipotent, reductive and split-torus terminology. The only unipotent hits were biproduct matrix morphisms; reductive hits concerned Lie algebras, not the algebraic-group statement. No exact project theorem, even a partly completed one, was found for the item. No Lean was written, built, or compiled.

## Sources requested

WANTED: Michel Brion, On Linearization of Line Bundles, J. Math. Sci. Univ. Tokyo 22 (2015), printed pp.117--118, Definition 2.1, Remarks 2.2(iii),(v), and Lemma 2.3, for lem-sfb-split-reductive-affine-space-quotient. The named local PDF is absent. I read the primary publisher PDF online at https://www.ms.u-tokyo.ac.jp/journal/pdf/jms220104.pdf without downloading it into the repository.

The supporting literature is present: literature/milne-algebraic-groups_iAG2017.pdf. Its text extraction is only in this item's sandbox. I read Sections 6.45--6.46 on printed p.135, Corollary 16.24 on p.331, Proposition 16.55 and Corollary 16.56 on p.344, and Example 2.72 on p.61. These give the extension lemma, the additive series, affine-base torsor triviality, and the affine-space induction. No SGA source is used. The generic geometric-integrality and base-change nodes retain their existing Stacks sources rather than introducing new tag-based nodes.

## What needed repair

The imported item had no proof. Its statement is true as written: the product is an isomorphism of schemes over the quotient, and a group-homomorphic section is not asserted. In particular no Levi-decomposition hypothesis or characteristic-zero restriction is introduced. I kept every original field and the original statement and its statement dependencies.

I supplied the missing argument that G/R_u(G) is reductive, rather than reading it into the radical-existence node. The inverse image of a putative smooth connected normal unipotent subgroup is unipotent by the new extension lemma; the quotient-geometry node supplies its smoothness, connectedness, normality and exact sequence. Maximality of the radical then forces that subgroup to be trivial.

The existing split-solvable-torsors-and-variety node asserts Zariski local triviality, not a global section over an arbitrary affine base. Its variety statement also allows a torus factor and does not identify the exponent for a prescribed additive series. I therefore did not cite those conclusions for the stronger claims. The new affine-base section lemma supplies the non-elementary global torsor input; the item's fourth step explicitly performs the finite reverse induction constructing the affine-space coordinates. The fifth step gives the actual section-based maps and checks their first coordinate.

Blueprint searches used tools/blueprint_refs.py ancestor and search, with unipotent, unipotent radical, unipotent extension, unipotent exact, unipotent torsors, unipotent affine, unipotent kernel, split solvable, principal bundle, torsor, and affine space. The unipotent hit about finite classical local systems and the torsor/affine-space hits do not state either new lemma. Ancestor reports blueprint.from.node = None for this existing lineage; I preserved that value and extended its exact supporting place and via chain. I read the latest blueprint chapter and sk-thm-sf-ctf-stability unit and direct-images proof. This support remains in its recorded Picard/linearization branch; it changes neither the unit nor its route. This item is not the unit's key statement, so no unit record is written.

## Not duplicates

lem-sfb-smooth-unipotent-extension vs lem-sfb-unipotent-radical-existence: existence and maximality of a normal unipotent subgroup does not state closure of unipotence under extensions; the latter is the separate inference needed for its quotient to be reductive.
lem-sfb-smooth-unipotent-extension vs lem-sfb-unipotent-normal-quotient-image: that node takes an already unipotent normal subgroup and proves that its image is unipotent; the new lemma deduces unipotence of a middle group from its kernel and quotient.
lem-sfb-smooth-unipotent-extension vs lem-sfb-unipotent-rational-representation-fixed-vector: a fixed vector for a representation of an already unipotent group does not state extension closure; the latter requires invariants under the kernel and descent to the quotient.
lem-sfb-split-unipotent-affine-torsor-section vs lem-sfb-split-solvable-torsors-and-variety: the existing torsor assertion is local for the Zariski topology and includes torus factors, whose torsors over affine schemes can be nontrivial; the new assertion is global over an affine finite-type base and assumes exclusively additive quotients.
lem-sfb-split-unipotent-affine-torsor-section vs lem-sfb-additive-affine-torsor-section: the existing node is the single additive-group case; the new result allows a possibly noncommutative iterated additive group.
lem-sfb-split-unipotent-affine-torsor-section vs lem-sfb-normal-extension-torsor-reduction: that node constructs quotient torsors and lifts a pair of given sections; it does not assert the existence of either section.
lem-sfb-split-unipotent-affine-torsor-section vs lem-sfb-perfect-unipotent-additive-series: existence of a subgroup series over a perfect field is not the section theorem for a torsor over an affine base. The new node assumes its series and works over any field.

Searches covered all dag/nodes, not only the target closure, by these notions and by Milne 6.45, 16.55 and their nearby statements. The source-place hits were opened; they do not provide a stronger statement that specializes to either new node. The new lemmas are genuinely smaller supporting results: neither asserts a reductive quotient, maximal torus, affine-space decomposition of a general group, or the item's field-extension clauses.

## Review by Q90

I read Brion's Definition 2.1, Remark 2.2 and the proof of Lemma 2.3 at the publisher. Brion reduces from G to its reductive quotient by using the unipotent radical as an affine space and trivializing its torsor. Milne's 6.45--6.46 and 16.24, 16.55(b), 16.56 spell out the structural inputs for this route. The new extension statement agrees with 6.45, including positive characteristic and without centrality or connectedness assumptions. The new torsor statement uses the additive-series meaning of split unipotent in 14.61 and the affine algebraic base of 16.55(b); its finite-type hypothesis ensures it asks for no unsupported arbitrary-base generalization. Both new nodes are self-contained statements with empty proof and proof_deps, complete definition dependencies, and actual searches in all the requested services plus Mathlib grep. All hits were irrelevant for the specific reasons recorded above. No unavailable service was treated as a no-match result.

For step 1 I opened radical-existence, the rational-section geometric-connectedness criterion and affine-normal-quotient-geometry. The first supplies exactly U with its maximality, the second applies to the identity section, and the third explicitly supplies the affine represented quotient, smoothness, geometric connectedness and right-torsor comparison. This avoids assuming either a section of q or reductivity at this point.

For step 2 the same quotient-geometry statement explicitly says that inverse images of smooth connected subgroups are smooth connected and that normality and exact quotients are preserved. The new extension lemma is applied only to smooth affine finite-type groups U, P and V over algebraically closed k. Thus the radical node's maximality applies to P; faithful flatness then identifies V with P/U=1. I opened reductive-borel-pair-structure and used only its existence of a split maximal torus for a reductive group over an algebraically closed field; no flag variety or root-system claim is used. This is an actual proof of reductivity, not an application of a new node restating it.

For step 3 I opened perfect-unipotent-additive-series and split-solvable-right-torsors. The former provides all smooth connected terms and additive represented quotients for U, because algebraically closed k is perfect; every tail meets the definition in the latter. No nontrivial separability claim about the later extension field L is needed.

For step 4 I checked quotient-geometry and the new affine torsor section statement against each induction term. The base is G_a, hence affine and finite type; U_{j+1} has precisely the tail split series. The length-zero base of the induction is Spec k. A section together with the cited torsor comparison gives the explicit isomorphism (x,v) -> s_j(x)v and its scheme morphism inverse. Adjoining one polynomial coordinate then gives the inductive exponent. The finite induction and inverse construction are written in the step, not hidden in the new lemma.

For step 5 I checked the new section lemma at S=H: step 1 gave affine finite type and the right U-torsor, and step 3 gave the split series. The quotient node gives the comparison isomorphism, so the second coordinate is regular, not merely a set-theoretic choice on points. The two displayed maps have inverse composites, and the first coordinate is q. A section of schemes suffices; a section of group schemes is neither used nor claimed.

For step 6 I opened smooth-connected-fibre-normal-integrality and proper-base-change. The former explicitly concludes integrality after every field extension from a smooth morphism with geometrically connected nonempty fibres; all are available for H over the one-point base Spec k. A further extension M/L is also an extension of k, proving the stronger geometrically integral assertion for H_L. Only clause (2) of proper-base-change supplies smoothness, not its properness clause. Affineness and finite type are checked directly on A tensor_k L. The two nodes from other units and the rational-point criterion are declared as generic tool uses with their exact purpose, not as changes to the unit route.

For step 7 no theorem is concealed: pulling back both inverse equations proves the scalar-extended map is an isomorphism, pulling back the projection equation proves it is over H_L, and polynomial base extension identifies the affine-space factor. This step is elementary. I kept the arbitrary L/k scope, including transcendental and imperfect L, and explicitly included the trivial group with n=0. Every proof step is below 2000 characters (the largest is 844), and none hides a separate comparison lemma.

I tested the new extension lemma with either kernel or quotient trivial, a finite smooth constant p-group in characteristic p, and noncommutative unitriangular groups; no excluded case or centrality hypothesis appears. I tested the section lemma with U=1 (including an empty affine base), U=G_a and an iterated noncommutative additive group. The affine hypothesis is essential: no claim is made for unipotent torsors on a positive-genus projective curve. For the item I checked G=1, G=G_a^d and a torus, and positive-characteristic groups without a group-theoretic Levi section. The statement consistently concerns schemes. I corrected the potential C4 misuse of merely local torsor triviality and supplied the missing extension-closure node for C1. All step citations have verbatim quotations in citations.json.

## Unfinished work

The two new statements remain unsplit as required for a one-level split. No Lean proof is claimed. The required server dry run and delivery are the final checks; their results are recorded below when available.
