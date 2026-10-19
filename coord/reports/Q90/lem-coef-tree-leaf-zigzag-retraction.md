# Worker report: lem-coef-tree-leaf-zigzag-retraction

## Files written

- `dag/nodes/sec-six-functors/lem-coef-tree-leaf-zigzag-retraction.json`: statement node, split; no new child nodes and no Mathlib leaves.
- `citations.json`: verbatim quotations for the three steps that cite `def-coef-zigzag-homotopy-calculus`.

## Attachments

None. I searched both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the upstream reference checkout for the item id, its title, and the leaf-collapse terminology; no declaration states this item.

## WANTED:

- Dwyer–Kan, *Calculating simplicial localizations*, Section 5.8(iii), printed p.25, for the finite-tree contraction. The repository has no archival copy, so the proof is recorded as agent supplied from the cited place.

## What was checked and changed

The copied item was unsplit. I retained its statement, statement dependency, recorded Mathlib searches, source, and blueprint ancestry. I filled the proof and proof dependencies and marked the node `split`. No definition or child statement was created: the retraction and the two naturality checks are direct proof steps from the free path and zigzag definitions, and a separate child would restate clauses of this item.

I searched the whole DAG for the item, its terminology, the Stacks/source place, and the relevant blueprint wording. The closest existing node is `lem-coef-cofibrant-localization-diagonal-nerve`, whose finite-tree argument is a related ordinary path-category contraction; it does not state fixed-word zigzag diagram categories, so it cannot replace this item. The existing `lem-coef-nerve-natural-homotopy-equivalence` is not needed here because this item supplies the natural transformation that its parent applies.

## Review by Q90

I read the item node, the chapter record `dag/chapters/sec-six-functors.json`, the unit record `dag/units/sk-prop-sf-biduality-general.json`, the source definition node `def-coef-zigzag-homotopy-calculus`, and the parent proof in `lem-coef-free-factor-hammock-comparison`. The item's hypotheses are unchanged: the tree is small and oriented, the endpoints are different from the deleted leaf, the pair defining the zigzags is `(C_T,C_T)`, and identity horizontal arrows remain allowed.

Step 1 constructs the inclusion and collapse functors from the universal property of the free path category. Replacing the sole incident edge by `1_a` is type-correct for either orientation because both endpoints map to `a`; fixing every remaining generator makes `r i` strictly the identity. This step uses no external statement.

Step 2 applies these functors to every vertex, horizontal arrow, and vertical arrow in a fixed-word diagram. The cited definition says that `Z_w` consists of such diagrams with the prescribed orientations, so the componentwise assignments preserve the word shape and commuting squares. The same definition supplies the morphism convention used below. Since `x,y` are not `l`, the endpoint components are identities, and `R_w I_w` is the componentwise identity.

Step 3 handles `l\to a`. The cited statement requires commuting diagrams, vertical arrows in `W`, and identity endpoint components. Here `W=C_T`, so the proposed components are allowed. A path avoiding `l` is fixed; any nonidentity path touching the leaf starts with the unique edge `e` and cannot return to `l`, while an identity at `l` is sent to `1_a`. The naturality squares therefore reduce to associativity and the equation `r(e)=1_a`. The endpoint components are identities.

Step 4 handles `a\to l` by reversing the transformation. Every nonidentity path touching `l` ends with the unique edge `e`; after collapse it becomes `1_a`, so the same associativity check gives naturality. Again the endpoint components are identities. These checks also cover horizontal arrows displayed leftward in the signed word, because the underlying arrow is still a morphism of `C_T` and functoriality handles its displayed direction.

Step 5 records that the word is finite, so repeated vertices give only finitely many components; the empty word gives the identity diagram and vacuous transformation. I tested the one-edge tree in both orientations, words consisting only of identities, words containing a single incident edge, repeated occurrences of `l`, and endpoints equal to `a`. No hypothesis is added or dropped, and no source statement is corrected.

No Lean source declaration, Mathlib declaration, or Stacks node states this fixed-word leaf retraction. No SGA source is used, and no off-unit tool use is needed.

## What could not be finished

Nothing in the split remains unfinished. The cited Dwyer–Kan document is unavailable in the repository, as recorded under `WANTED`; the proof is explicitly marked agent supplied.
