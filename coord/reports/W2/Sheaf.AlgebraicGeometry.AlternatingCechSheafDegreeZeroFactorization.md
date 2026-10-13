## What changed

Proved `AlgebraicGeometry.alternatingCechSheafAugmentation_restrict_degreeZero_factorization`
without changing its signature. Added two modules: `CechCapPresheafLocalIso` proves that
intersection restriction becomes invertible after sheafification and restriction to the open;
`AlternatingCechPresheafDegreeZeroIdentity` constructs the singleton projection and signed
pair insertion explicitly and proves their degree-zero identity. The item's proof-only import
uses these results, then transports through the sheafification counit and `extendXIso`.
The existing node now records this route. No existing definition or statement changed.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.alternatingCechSheafAugmentation_restrict_degreeZero_factorization`
(node `lem-pc-s3-alternating-cech-sheaf-degree-zero-factorization`).
Also proved `AlgebraicGeometry.cechCapPresheafUnit_local_isIso`
(node `lem-pc-s3-cech-cap-presheaf-local-iso`) and
`AlgebraicGeometry.alternatingCechSheafPresheaf_degreeZero_identity`
(node `lem-pc-s3-alternating-cech-presheaf-degree-zero-identity`).
No sorry remains in the delivered modules and no holes were added.

The new definitions are real presheaf functors and natural restriction maps.
The insertion maps in the new identity proof are explicitly constructed; no arbitrary
witness of an unproved existence result supplies data.

## No longer needed

None. The original module imported only the construction, which is still needed.
No original proof-dependency node or module is pruned. Higher-degree singleton contraction,
positive contraction and insertion homotopy are not needed for this degree-zero proof;
they were not dependencies of the item's original node and no pruning of their other users
is claimed. In particular, singleton contraction already imports this item and cannot be
used to prove it without an import cycle.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original one-step prose proof did not supply Lean declarations
for its presheaf or sheafification comparison steps. The two new proved lemmas supply these
steps. The local comparison admits an elementary adjunction proof: on direct images from the
open, intersection restriction is an isomorphism; transfer the bijection on morphisms through
the composite sheafification–restriction adjunction and use the coyoneda criterion.
The unit's route stays unchanged: its realized statement and step lists do not include this
auxiliary node, and all new nodes inherit its chapter and unit.

Edge cases were checked in the constructions: no index exists when r=0; with one index the
pair terms vanish; the equal-index coordinate uses zero insertion; empty opens and arbitrary
module presheaves cause no exception in the adjunction proof. No covering assumption is added.

## New nodes

`lem-pc-s3-cech-cap-presheaf-local-iso` records the proved cap-unit comparison for any
module presheaf. Its source is Stacks 02FU, restriction to a cover member, and its proof
is the explicit adjunction argument described above. LeanFinder, Loogle and source searches
found generic adjunction and Yoneda tools but no specialized comparison. LeanSearch was
unavailable. The functor and natural unit are genuine specializations of Mathlib pushforward.

`lem-pc-s3-alternating-cech-presheaf-degree-zero-identity` records the proved signed
pair-coordinate identity before sheafification or integer extension. It follows Stacks 02FU
and 01FM and is strictly a lower computational step of the target argument. The same search
kinds found no matching explicit increasing-tuple identity; LeanSearch was unavailable.
No change record is needed because existing interfaces are unchanged.

## Second reading by W2

1. The delivered target module was compared with the repository version. The target signature is unchanged byte for byte; only the proof and a proof-only import were added. Verdict: pass.
2. All three sandbox modules compile successfully with `lcompile.py --all`. No `sorry`, forbidden declarations, or hollow definitions occur in the delivered Lean files. Verdict: pass.
3. The split-off statements are true, strictly lower than the target, and required by the proof. Their docstrings describe complete constructions and each has a matching DAG node. Verdict: pass.
4. The proof follows the unit route through the presheaf identity, local cap-unit isomorphism, sheafification, and extension isomorphisms. No unused original dependency or import was found. Verdict: pass.
5. DAG `proof`, `proof_deps`, `proof_origin`, and Lean declarations agree; the unit realized route remains unchanged. Verdict: pass.

Changed after reading: no Lean statements or definitions; this report section only.

A scratch probe within the sandbox Lean root confirmed that all three public theorems
use only `propext`, `Classical.choice`, and `Quot.sound`. Additional independent
LeanFinder, Loogle, and source searches for intersection restriction invertibility,
sheafification restriction, and singleton projection found generic adjunction tools
and no replacement specialized lemma. The signed pair cases were checked directly:
i<j gives s_j-s_i, j<i negates s_i-s_j, and i=j has zero boundary term.
The unit's realized statement and step lists were inspected and are unchanged.
