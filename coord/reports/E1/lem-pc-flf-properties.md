# Stage 1 report

Files written: `dag/nodes/sec-picard-framework/lem-pc-flf-properties.json`; new nodes `lem-pc-finite-flat-pushforward-locally-free` (closed Lean declaration) and `lem-pc-finite-affine-fibre-sections` (unsplit statement-only). `citations.json` records verbatim citations for every step.

Attachments: `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_pushforward` belongs to `lem-pc-finite-flat-pushforward-locally-free`.

WANTED: none.

The item has no sorry-free declaration: the pointer theorem `isFiniteLocallyFreeOfRank_pushforward_unit` in `FinitePushforward.lean` is sorry-bearing. The imported split cited the existing locally-free pushforward node, whose proof depends on this item; I removed that cycle. The replacement uses the independent closed theorem for a finite locally free module, an affine fibre calculation node, and the degree definition.

## Review by E1

I read the source declaration and docstring in `WeilConjectures/AlgebraicGeometry/Modules/FinitePushforward.lean` and the blueprint item. The closed supporting declaration has exactly the finite, flat, locally finitely presented hypotheses and concludes finite locally free pushforward. The affine supporting statement introduces its own rings, schemes, point, residue field, and canonical map, and states the exact tensor identification used in Step 2. I searched the DAG for both statements and found no duplicate; the affine-spectrum node is an existing Mathlib leaf and is cited directly.

Step 1 uses only the closed pushforward statement and the finite-locally-free definition; the structure sheaf is the standard finite locally free module over itself. Step 2 uses the affine fibre statement and the existing affine fibre-product statement, which explicitly gives the tensor-product spectrum. Step 3 uses the degree clause of the definition and is a one-line rank identification. I checked the identity morphism, the empty degree-zero case, and an affine finite algebra over a field. The previous residue-field flat-base-change route was removed because a residue-field extension need not be flat.

## Not duplicates

`lem-pc-finite-flat-pushforward-locally-free` vs `lem-sc-finite-pushforward-locally-free`: the new node is the general finite locally free sheaf pushforward theorem backed by a closed declaration; the existing node is a structure-sheaf rank/local-constancy statement whose proof uses this item.

`lem-pc-finite-affine-fibre-sections` vs `lem-weil-pbc-fibre-product-affine-spectra`: the new node identifies pushforward stalk tensors and fibre global sections; the existing node only identifies a fibre product of affine schemes with a tensor-product spectrum.

`lem-pc-finite-affine-fibre-sections` vs `lem-sc-finite-pushforward-locally-free`: the new node is an affine stalk-to-fibre algebra isomorphism; the existing node states local freeness of the structure-sheaf pushforward and does not state this canonical map.

`lem-pc-finite-affine-fibre-sections` vs `lem-pc-cartier-criterion`: the new node concerns finite morphism fibres and pushforward stalks; the existing node uses Tag 02KB for a Cartier criterion and does not state the fibre-sections isomorphism.

`lem-pc-finite-affine-fibre-sections` vs `lem-weil-pbc-finite-locally-free-degree-etale-descent`: the new node is the affine tensor calculation; the existing node concerns descent of finite locally free degree and does not state the canonical map.

`lem-pc-finite-affine-fibre-sections` vs `lem-weil-pbc-finite-locally-free-degree-locally-constant`: the new node identifies stalk tensors with fibre sections; the existing node only states local constancy of the degree function.

## Second reading by E1

- Item statement: checked against the blueprint node and the degree/fibre conventions; verdict: correct, with explicit scheme and residue-field definition links added.
- Step 1: checked against Stacks Tag 02KB (Lemma `lemma-finite-flat`) and the attached sorry-free Lean declaration; verdict: hypotheses and conclusion match, and the structure sheaf is finite locally free over itself.
- Step 2: checked against Tag 02KB's affine proof and the affine fibre-product node; verdict: the stalk localization and tensor identification give the stated canonical map.
- Step 3: checked against the degree clause and Step 2's fibre isomorphism; verdict: elementary after explicitly citing the affine fibre node.
- `lem-pc-finite-flat-pushforward-locally-free`: checked against `isFiniteLocallyFree_pushforward` in `FinitePushforward.lean` (lines 214--244), including finite, flat, locally finitely presented, and finite locally free module hypotheses; verdict: exact closed declaration, with all definition dependencies listed.
- `lem-pc-finite-affine-fibre-sections`: checked against Tag 02KB's affine calculation and the affine spectrum fibre-product identification; verdict: statement is self-contained and its finite morphism, spectrum, and residue-field dependencies are now cited.

Changes: added missing statement dependencies for both new nodes and the item; added the Step 2 dependency to Step 3; retained the Lean-closed pushforward theorem attachment. Small cases checked: identity morphism, empty degree-zero fibre, and a finite algebra over a field. No source error found.
