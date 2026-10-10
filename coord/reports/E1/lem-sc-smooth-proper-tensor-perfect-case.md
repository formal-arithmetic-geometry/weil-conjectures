Files written:

- `dag/nodes/sec-picard-framework/lem-sc-smooth-proper-tensor-perfect-case.json`: item split into the projection-formula mate construction and the perfect-complex dualizability calculation.
- `dag/nodes/sec-picard-framework/lem-pc-perfect-tensor-hom-duality.json`: new statement-only auxiliary node; Mathlib searches found no match.
- `citations.json`: verbatim citations for every node used by every proof step.

Attachments:

None. No sorry-free declaration in `WeilConjectures/` states the item.

WANTED:

None. The Stacks source is cited by Tag 0A9T in the imported node and the proof follows that tag.

What was wrong or incomplete:

The imported item had no proof. The existing perfect-complex definition gives local bounded finite-projective models but does not state dualizability, so I added `lem-pc-perfect-tensor-hom-duality` rather than hiding that fact in the main proof. I searched the whole DAG and blueprint for this statement and found no duplicate. The Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and is recorded as such.

## Not duplicates

lem-pc-perfect-tensor-hom-duality vs lem-sc-smooth-proper-tensor-perfect-case: the auxiliary node is the general dualizability and tensor-Hom statement for one perfect complex on one scheme, with no morphism, properness, adjoint, or comparison map; the item is the projection comparison for a proper perfect morphism and a right adjoint.

## Review by E1

I read the imported item and its neighboring Tag 0A9U node, including the exact statements of `lem-pc-projection-formula`, `lem-pc-noetherian-derived-direct-image-right-adjoint`, and `def-pc-perfect-complex`. Step 1 uses only the projection-formula statement, and the proper Noetherian hypotheses supply the quasi-compact and quasi-separated conditions required there; the counit is already part of the item's adjunction hypotheses. Step 2 uses the new node's explicit dualizability and tensor-Hom isomorphisms, and the projection-formula statement for the middle isomorphism. I checked that the Hom chain has the correct variance and that its induced map is the mate defining the comparison, so Yoneda applies. The auxiliary statement is strictly smaller than the item and is statement-only as required. I tested the calculation on `K=O_Y` and on a shifted finite free complex, where it reduces to the adjunction and shift identities.

## Second reading by E1

- Item statement: checked against Stacks, Duality, Tag 0A9T (`duality-lemma-compare-with-pullback-perfect`); the proper Noetherian hypotheses specialize the source's quasi-compact and quasi-separated hypotheses, and the comparison map has the source's orientation and mate definition; verdict: agrees.
- Step 1: checked against the statement of `lem-pc-projection-formula` and Tag 0A9T's construction; proper Noetherian schemes are quasi-compact and quasi-separated, and the counit supplies the stated mate; verdict: cited statement says the used projection isomorphism.
- Step 2: checked against Tag 0A9T's perfect-complex proof and the exact statements of `lem-pc-perfect-tensor-hom-duality` and `lem-pc-projection-formula`; each Hom identification has the required variance, and the comparison-induced map is identified by its defining mate; verdict: valid after making the dual-pair and double-dual identifications explicit.
- New node `lem-pc-perfect-tensor-hom-duality`: checked against the perfect-complex dual construction used in Tag 0A9T; its hypotheses introduce the scheme, perfect complex, and quasi-coherent complexes, and its two displayed adjunctions are strictly smaller than the item; verdict: self-contained statement-only auxiliary, no duplicate found by DAG/blueprint search, Mathlib searches recorded.

Changes made: corrected the item's `created.item` to the delivered item (it incorrectly named the diagonal tensor item), and expanded Step 2 to name the two tensor-Hom applications, the dual pair, the double-dual identification, and the mate/naturality argument. I tested the statement on the zero complex, the structure-sheaf complex, a field scheme, and shifts of finite free complexes; these reduce to the zero isomorphism, adjunction, and shift identities. No source error or false edge case was found.
