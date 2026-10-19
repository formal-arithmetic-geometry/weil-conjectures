Files written:
- `dag/nodes/sec-smooth-base-change/sbc-lem-strict-henselian-constant-cohomology.json` (item, split; two proof steps).
- `dag/nodes/sec-smooth-base-change/lem-sbc-strict-henselian-positive-cohomology.json` (statement, closed Lean declaration; Mathlib searches found no match).
- `dag/nodes/sec-smooth-base-change/lem-sbc-strict-henselian-constant-hzero.json` (statement, closed Lean declaration; Mathlib searches found no match).

Attachments:
- `AlgebraicGeometry.Scheme.subsingleton_H_of_isStrictlyHenselianLocalRing` belongs to `lem-sbc-strict-henselian-positive-cohomology`.
- `AlgebraicGeometry.Scheme.hZeroConstantSheafAddEquiv` belongs to `lem-sbc-strict-henselian-constant-hzero`.

WANTED: none.

The imported item had an unsplit proof paragraph. I checked the source blueprint and the corresponding declarations in `WeilConjectures/AlgebraicGeometry/Sites/StrictlyHenselian.lean`; both clauses are already stated by closed declarations there, but no single declaration states the full finite-constant result. The split therefore introduces one node for positive-degree vanishing and one for degree zero, then combines them in the item. I added the existing constant-sheaf definition to the item's statement dependencies. The positive-degree step verifies that a finite constant sheaf is an abelian étale sheaf and applies the cited subsingleton theorem with $q=n+1$; the degree-zero step applies the cited additive equivalence. Each citation quote is copied verbatim from its node statement, and the hypotheses (strict henselian local ring, Spec construction, abelian/constant sheaf) match the item's hypotheses.

## Review by NC

I read the item's blueprint source at `literature/blueprint/master/blueprint/sec-smooth-base-change/sk-rem-rest/sbc-lem-strict-henselian-constant-cohomology.md` and the complete source module `WeilConjectures/AlgebraicGeometry/Sites/StrictlyHenselian.lean`. The positive-degree node matches the theorem at lines 165–168, including its arbitrary abelian sheaf and $n+1$ hypotheses; the degree-zero node matches the definition at lines 190–195, including the constant sheaf over `Spec R` and additive equivalence. The item uses exactly these statements in separate cases, with the finite constant sheaf supplying the abelian-sheaf hypothesis and the value $A$ supplying the degree-zero input. I searched the full DAG and blueprint for duplicates and found none. I ran LeanFinder, Loogle, Mathlib grep, and LeanSearch for the item and each created statement; LeanSearch was unavailable and recorded as such. No source or statement correction was needed.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against the blueprint node and the imported `StrictlyHenselian.lean` declarations; corrected the ambiguous use of `A` as both a sheaf and its value, and made the strictly henselian, scheme, étale-site, abelian-sheaf, constant-sheaf, and cohomology notions explicit through definition dependencies.
- Step 1: checked against `subsingleton_H_of_isStrictlyHenselianLocalRing` (lines 165–168); its arbitrary abelian-sheaf and all `n ≥ 0` hypotheses supply the claimed positive-degree case after writing `q = n+1`.
- Step 2: checked against `hZeroConstantSheafAddEquiv` (lines 190–195); its input is the abelian group `A` and its output is exactly the degree-zero equivalence for `\\underline A`.
- `lem-sbc-strict-henselian-positive-cohomology`: statement checked against the closed declaration and tested on the zero group and a field; definitions and source metadata are self-contained, and recorded searches were verified in `searches.jsonl`.
- `lem-sbc-strict-henselian-constant-hzero`: statement checked against the closed declaration and tested on the zero group and a field; definitions and source metadata are self-contained, and recorded searches were verified in `searches.jsonl`.

Changes made: clarified the item's coefficient as a finite abelian group with associated constant sheaf, updated both proof steps to use `\\underline A`, and added all definition dependencies required for a standalone statement. No node was removed: both are closed declarations and are strict dependencies of the two proof cases.

## Second reading by NC

- Item statement: checked against the blueprint node and `StrictlyHenselian.lean`; the strictly henselian local ring, finite abelian coefficient, invertibility condition, constant sheaf, and the cases `q=0` and `q>0` are all present.
- Step 1: checked against `lem-sbc-strict-henselian-positive-cohomology`; writing `q=n+1` supplies its quantified degree, and the constant sheaf is an abelian étale sheaf. The subsingleton conclusion gives the zero abelian group.
- Step 2: checked against `lem-sbc-strict-henselian-constant-hzero`; its natural additive equivalence has exactly the required degree-zero value for the same `Spec R` and constant sheaf.
- `lem-sbc-strict-henselian-positive-cohomology`: checked statement, definition dependencies, blueprint place, search log, and closed declaration `AlgebraicGeometry.Scheme.subsingleton_H_of_isStrictlyHenselianLocalRing` (lines 165–168); zero group and field cases are consistent.
- `lem-sbc-strict-henselian-constant-hzero`: checked statement, definition dependencies, blueprint place, search log, and closed declaration `AlgebraicGeometry.Scheme.hZeroConstantSheafAddEquiv` (lines 190–197); zero group and field cases are consistent.
- Changes in this second reading: added this required audit section; no mathematical or citation repair was needed because the prior B10 closure metadata and exact citation quotes were already present.

## Repair for B10

Both created clause nodes are closed declarations in `WeilConjectures/AlgebraicGeometry/Sites/StrictlyHenselian.lean`, so their records now carry the exact declarations in delivery-preserved `lean_candidates` (branch `slopmaster2`, full name, module, file and lines), in addition to the sandbox audit records. Their queue status remains `unsplit` until the maintainer verifies and installs the attachments, as required by the remote field-ownership contract. I added the required `created.group: "NC"` metadata alongside the existing by/item/date fields. The positive-degree node's statement quantifies over an arbitrary abelian étale sheaf and does not mention a constant sheaf, so I removed its unused `def-weil-pbc-constant-sheaf` statement dependency. The degree-zero node keeps that dependency because its statement explicitly uses the constant sheaf. The item remains split and cites both closed nodes.

The delivery script strips `lean_audit` from new remote records and reduces `created` to its `item` field; therefore closure evidence is now carried in `lean_candidates`, which survives that filter. The full by/date/group metadata is present in both sandbox records for the maintainer to stamp on merge. This avoids the returned records losing all machine-readable attachments.
