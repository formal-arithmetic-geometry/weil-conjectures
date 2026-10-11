1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-perfect-local-pseudocoherent-free-model.json` (statement, split)
- `dag/nodes/sec-abelian-varieties/lem-sc-pseudo-coherent-lift-stably-free-complex.json` (statement, unsplit, Mathlib no match)

2. Attachments: none.

3. WANTED: none.

4. The item has no sorry-free declaration in `WeilConjectures/` and no duplicate DAG node. I read the Tag 0BCC source and its preceding Tag 0BCB lifting lemma. The new node records the exact general lifting input used by the source. The item proof uses the pseudo-coherence hypothesis for the residue tensor, the elementary splitting of complexes over a field, the new lifting statement with I=m, and the elementary rank identification and upper bound. The local-ring hypothesis supplies that 1+m consists of units; the free terms of the residue complex supply the final free conclusion.

## Review by E1

I checked the item statement against `more-algebra.tex`, Lemma 15.75.7 (Tag 0BCC), including the finite dimensions, eventual vanishing, bounded-above model, and ranks d_i. I checked the new node against Lemma 15.75.6 (Tag 0BCB), including the hypotheses on 1+I and the final free-term clause. I searched the DAG for 0BCC, 0BCB, stably-free lifting, and residue-field models; no existing node states the new lemma. The citations quote the exact dependency statements. Small cases are consistent: K=0 gives all d_i=0 and the zero complex; K=R in degree zero gives d_0=1 and the one-term free model. Mathlib searches were run for both the item and the supporting concept (LeanFinder, Loogle, grep, and unavailable LeanSearch) and recorded in the node.

## Second reading by E1

- Item statement: checked against More on Algebra, Lemma 15.75.7, Tag 0BCC; restored the source's uniqueness-up-to-isomorphism clause and retained all hypotheses.
- Step 1: checked against the field-splitting paragraph of Tag 0BCC; the assumed finiteness and cutoff are used directly, and the residue complex has zero differential with terms $\\kappa^{\\oplus d_i}$.
- Step 2: checked against Tag 0BCB; the local-ring unit condition and free residue terms match the cited lifting statement.
- Step 3: checked against the displayed conclusion of Tag 0BCC; reduction identifies the ranks and the cutoff gives bounded-above support.
- Step 4: checked against the uniqueness paragraph of Tag 0BCC; the existing projective-complex Hom statement supplies a chain representative and Nakayama supplies degreewise invertibility after reduction.
- `lem-sc-pseudo-coherent-lift-stably-free-complex`: checked against Tag 0BCB, including the $1+I$ hypothesis and free-term conclusion; self-contained statement and recorded searches retained.
- `lem-sc-perfect-derived-morphism-chain-map`: checked against Derived Categories Tag 06XR; it states exactly the chain-map representation used for uniqueness, with all notions and Mathlib searches recorded.

Changes: removed `lem-sc-pseudo-coherent-residue-finite-cohomology` because it restated an item hypothesis; rewrote the proof to use that hypothesis directly; added the omitted uniqueness clause and its chain-map/Nakayama argument; added the local Tag 06XR chain-map dependency to keep the unit route self-contained; corrected `created.item` and proof dependencies; updated citations to quote every cited statement verbatim.

## Not duplicates

- `lem-sc-perfect-derived-morphism-chain-map` vs `lem-sc-derived-hom-projective-resolution`: the existing node treats a projective resolution of a single module and computes derived Hom; the new node covers arbitrary bounded-above projective complexes and representation of every derived morphism by a chain map.
- `lem-sc-perfect-derived-morphism-chain-map` vs `lem-sc-affine-rhom-qcoherent`: the existing node is an affine quasi-coherent sheaf RHom comparison; the new node is the algebraic derived-category chain-map representation.
- `lem-sc-perfect-derived-morphism-chain-map` vs `lem-sc-affine-projective-complex-derived-hom`: the existing node identifies an ordinary Hom complex with derived Hom in a one-point ringed-site formulation; the new node states the direct morphism-representation theorem used for uniqueness.
- `lem-sc-perfect-derived-morphism-chain-map` vs `lem-sc-ext-locally-free-second-naturality`: the existing node concerns naturality of Ext for locally free sheaves; the new node concerns arbitrary bounded-above projective complexes.
- `lem-sc-perfect-derived-morphism-chain-map` vs `lem-sc-p1-ext-resolution-derived-connecting`: the existing node concerns connecting maps in an Ext resolution; the new node concerns chain representatives of derived morphisms.
- `lem-sc-perfect-derived-morphism-chain-map` vs `def-sc-ext-sheaf`: the existing node defines an Ext sheaf; the new node is a derived-category representation theorem.
- `lem-sc-perfect-derived-morphism-chain-map` vs `lem-sc-p1-rhom-hom-derived-connecting`: the existing node computes a connecting morphism; the new node supplies chain-map representatives for arbitrary derived morphisms.
- `lem-sc-perfect-derived-morphism-chain-map` vs `lem-weil-pbc-ext-via-injective-resolution`: the existing node computes Ext via injective resolutions; the new node uses bounded-above projective complexes and chain maps.
