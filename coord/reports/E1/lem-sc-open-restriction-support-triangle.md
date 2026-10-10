1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-open-restriction-support-triangle.json`: item, split; no Mathlib match.
- `citations.json`: four verbatim step-to-node quotes.

2. Attachments: none.

3. WANTED: `literature/stacks-project/duality.tex`, Tag 0E4G (the local repository has no Stacks TeX checkout; the source was read from the authoritative review checkout).

4. The item had an empty proof. I retained its statement and dependencies and supplied the proof of the Stacks support-triangle argument. No new node was necessary: the existing K-injective restriction node supplies the derived restriction model, the existing exact open-restriction adjunction supplies exactness, and the derived-category definition supplies mapping-cone triangles. The three steps respectively construct the unit cone, prove its restriction is zero and hence its cohomology is supported on the complement, and prove bounded-below preservation.

## Not duplicates

lem-sc-open-restriction-support-triangle vs lem-sc-right-adjoint-open-support-criterion: this item constructs the restriction triangle and its supported cone; the existing node uses that triangle to characterize right-adjoint restriction isomorphisms.
lem-sc-open-restriction-support-triangle vs lem-sc-supported-derived-generated-perfect: this item concerns the cone of an open-restriction unit; the existing node concerns perfect generation of all complexes supported on a complement.

## Review by E1

I read the item source at Stacks Tag 0E4G, Lemma 48.4.3, together with Derived Categories of Schemes Lemma 36.4.1 and Definition 36.6.1. I also read the complete statements of `lem-sc-derived-k-injective-restrict-open`, `lem-sc-derived-open-restriction-adjunction-exact`, and `def-pc-derived-category`. Step 1 uses exactly the K-injective restriction clause and the derived-category cone construction. Step 2 uses exactness of restriction and the open adjunction to identify the restricted unit as an isomorphism; the resulting zero restriction gives support on `Y\\setminus V` by the cohomology long exact sequence. Step 3 checks the bounded-below hypothesis through the same triangle and long exact sequence. I tested the edge cases `V=Y` (zero cone), `V=empty` (zero restriction), and `K=0`; each gives the stated triangle and support conclusion. The Mathlib searches for the item were run with `msearch.py`: LeanFinder returned only generic t-structure triangles, Loogle rejected the natural-language pattern, grep found no scheme support theorem, and LeanSearch was unavailable.

## Second reading by E1

- Item statement: checked against Stacks Tag 0E4G, Lemma 48.4.3, including the qcqs, quasi-compact-open, unbounded, support, and bounded-below hypotheses; verdict: agrees.
- Step 1: checked the statements of `lem-sc-derived-k-injective-restrict-open`, `def-pc-ringed-spaces-derived-direct-image`, `lem-pc-derived-direct-image-preserves-qcoh`, `def-weil-abstract-derived-category`, and the kernel, cokernel, and extension quasi-coherence nodes. The representation clause is explicitly the K-injective direct-image clause, and the cone's cohomology is QC by the cited kernel/cokernel/extension statements; the qcqs hypotheses for `j` were verified from quasi-compact `V` and quasi-separated `Y`.
- Step 2: checked `lem-pc-restrict-derived-direct-image-open` with `f=j`, `U=V`, and `g=id_V`, together with exact restriction. This supplies the derived counit isomorphism and the long exact cohomology sequence gives support on the complement.
- Step 3: checked `lem-weil-pbc-bounded-below-injectives-kinjective`, exact restriction, and the termwise direct-image clause. The previous false claim that open direct image is stalkwise zero at boundary points was removed; bounded-below preservation now follows from the bounded-below injective representative and the cone long exact sequence.
- Existing nodes were searched by tag and keywords; no new child node is needed. The item is distinct from `lem-sc-right-adjoint-open-support-criterion` because that node consumes this triangle, and from `lem-sc-supported-derived-generated-perfect` because that node concerns generation rather than an open-restriction cone.
- Small cases checked: `V=Y`, `V=empty`, `K=0`, and a field scheme; all give the stated triangle and support behavior.
- Changed Step 2 to spell out the open-immersion counit on sections without importing an off-unit tool; changed Step 3 to spell out the bounded-below K-injective/direct-image calculation; converted arrows to TeX and updated `citations.json` and `proof_deps` accordingly.
