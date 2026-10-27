## What changed

Reduced `sfOpenClosedTriangle_qbar` to the existing integral/rational theorem at each
finite coefficient field and the new normalized common-stage descent lemma. The proof
chooses the finite presentations only inside the theorem, then proves uniqueness of
the connecting arrow and naturality using triangle-morphism extension.

Reduced `sfOpenClosedTriangle_rational_weil` to the existing automorphism exactness
theorem, the new proved normalization theorem, and the new geometric mate-square lemma.
A complete categorical proof maps each triangle by exact Frobenius, transports shifted
orthogonality through the open Weil isomorphism, and applies triangle-morphism extension.
It proves the third square and uniqueness of both outer Weil isomorphisms.

Added `SfNormalizedRecollementTriangles`: normalization on representative complexes
extends to arbitrary integral objects by essential surjectivity and naturality. The
actual exact completed sheaf sequence supplies their triangles and orthogonality.
Full-subcategory transport and exact raw scalar localization give the rational result.
The two other new modules state precisely the remaining geometric comparison/descent
steps. All new imports in the item are private proof imports. Existing public signatures,
definitions and public imports stay unchanged. A declaration-local linter setting
permits the original implicitly used shift binder without changing the signature.
The rational Weil proof derives separatedness of the geometric fibre by base change.
No source-library files are changed.

## Proved and sorry left

This is a decomposition, not a net reduction in the number of holes: two original
holes are closed and two strictly smaller geometric holes are added. The original
module had three holes and now has one.

Closed original holes:

- `WeilConjectures.sfOpenClosedTriangle_qbar`, node
  `prop-sf-open-closed-triangle-all-stages`.
- `WeilConjectures.sfOpenClosedTriangle_rational_weil`, the same node.

New proved public theorem:

- `WeilConjectures.sfNormalizedRationalRecollement_triangle_orthogonality`, node
  `lem-sf-normalized-rational-recollement-triangles`.

The private `integral_normalized` proof and the private
`sfRecollementWeilEquivariant_of_squares` proof are complete.

Every remaining textual sorry in this delivery:

- Existing `WeilConjectures.sfOpenClosedTriangle_qbar_weil`, node
  `prop-sf-open-closed-triangle-all-stages`; unchanged.
- New `WeilConjectures.sfNormalizedRecollement_commonStage_descent`, node
  `lem-sf-normalized-recollement-common-stage-descent`.
- New `WeilConjectures.sfNormalizedRationalRecollement_weil_squares`, node
  `lem-sf-normalized-rational-recollement-weil-squares`.

The finite and integral/rational original proofs stay complete. Each new hole is the
whole proof of a public theorem in its own module, with a source and full proof in words.
No definition contains sorry and no data definition chooses arbitrary existence data.

## No longer needed

No original direct import is removed and no whole module is withdrawn. The finite
constructibility dependency `lem-trf-open-ctf` / `Sheaf.Paper.OpenExtensionFiniteTor`
is retained: its `extension_constructible` theorem is used in the existing finite proof,
even though this proof needs no finite-Tor conclusion.

`lem-sf-qbar-localization-common-stage` / `Sheaf.Paper.SfQbarLocalizationCommonStage`
is not used for the arbitrary-field qbar triangle clause. Its finite-field datum is
stronger than that clause permits. The new datum-free normalized descent lemma is used
there. The old node stays in the unfinished qbar Weil proof plan and is not withdrawn.

The rational Weil proof imports the automorphism equivalence and the strictly smaller
normalized mate-square module; it does not import a second localization theorem or
assume a connecting-map equivariance assertion. The source-library boundary is preserved.

## Where the brief, the DAG or earlier work was wrong

The stated common-stage dependency assumes a finite-field datum and geometry over its
algebraic closure. `sfOpenClosedTriangle_qbar` instead quantifies over an arbitrary
field k with l invertible. It cannot be applied by specialization without adding a
hypothesis. The new descent lemma isolates the same coefficient argument over the
actual arbitrary base field; no original theorem statement is changed.

The existing mate theorem concerns the canonical operations and normalized module/tower
adjunctions. The rational Weil statement accepts any presentations satisfying the two
normalization predicates. Transporting the mate equations to those presentations is a
separate geometric comparison step, now explicitly stated. Exactness, triangle
existence, vanishing, the third square and uniqueness are not hidden in that step.

Empty complements and zero objects satisfy both new geometric statements. The descent
statement retains all integer shifts and independent input objects. The new mate lemma
requires only the two squares; the real triangle argument supplies its missing conclusions.
The unit route through the exact open/closed sheaf sequence is retained.

## New nodes

`lem-sf-normalized-rational-recollement-triangles` is a proved transport theorem for
already normalized presentations; its module is `SfNormalizedRecollementTriangles`.
It supplies triangles and shifted cross-object vanishing without choosing geometric
operations or assuming their conclusions.

`lem-sf-normalized-recollement-common-stage-descent` is coefficient descent of already
supplied finite presentations, in `SfNormalizedCommonStageDescent`. It does not produce
the finite presentations and it does not assert uniqueness or naturality of the final
arrow; those are combined and proved in the item.

`lem-sf-normalized-rational-recollement-weil-squares` transports the canonical geometric
mate equations to normalized rational presentations, in `SfNormalizedRationalWeilSquares`.
It supplies neither exactness nor a triangle nor vanishing nor a third square nor
uniqueness. These other parts are independently proved and combined in the item.

No existing public interface changes, so no change record or consumer adaptation is needed.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
