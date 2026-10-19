## Files written

- `dag/nodes/sec-trace-formula/lem-trf-unramified-maximal-ideal-residue-criterion.json`: split into the Stacks point criterion with two proof steps; statement and hypotheses retained.
- `dag/nodes/sec-trace-formula/lem-trf-stalk-formally-unramified-maximal-residue-criterion.json`: Mathlib leaf for the actual stalk ring map criterion.
- `citations.json`: verbatim statement quotes for each cited node and step.

## Attachments

None. The slopmaster2 and upstream source searches found no sorry-free project declaration carrying the exact item. The existing stalk-neighbourhood and locally-finite-type/formal-unramified nodes are cited as tools, not attachments.

## WANTED

None.

## Corrections and scope

The imported item is mathematically the Stacks Morphisms Tag 02GF equivalence (1) and (6), with “unramified at x” expanded as an unramified open neighbourhood. I retained its actual stalk-map wording and all finite-type, maximal-ideal, and finite-separable hypotheses. I repaired the blueprint place to identify the local maximal-ideal/residue criterion used in the ancestor `lem-trf-local-term-locality` proof. The new stalk node is strictly smaller than the item: it removes the neighbourhood assertion and records only the ring-theoretic local criterion. It is not a duplicate of `lem-sbc-dvr-map-maximal-ideal-formally-unramified`, whose statement is one-way and restricted to DVRs, nor of `lem-trf-unramified-over-field-local-criterion`, which concerns morphisms over a field.

## Not duplicates

`lem-trf-stalk-formally-unramified-maximal-residue-criterion` vs `lem-sbc-dvr-map-maximal-ideal-formally-unramified`: the new node is an iff for arbitrary local stalk rings and includes finite separable residue extensions; the existing node is only the forward maximal-ideal equality for DVRs.

`lem-trf-stalk-formally-unramified-maximal-residue-criterion` vs `lem-trf-unramified-over-field-local-criterion`: the new node is a local ring-map criterion for any base scheme and point, while the existing node characterizes an entire locally finite type scheme over a field.

`lem-trf-stalk-formally-unramified-maximal-residue-criterion` vs `lem-weil-pbc-henselian-local-target-etale-maps`: the existing node is a henselian lifting bijection for a module-finite target and etale source; it does not characterize arbitrary stalk maps by maximal ideals and residue fields.

`lem-trf-stalk-formally-unramified-maximal-residue-criterion` vs `lem-weil-pbc-unramified-algebra-over-field-product`: the existing node is a field-base affine product decomposition of an unramified algebra, while the new node is a local stalk iff criterion over an arbitrary scheme base.

`lem-trf-stalk-formally-unramified-maximal-residue-criterion` vs `lem-weil-pbc-unramified-quasi-finite-at-points`: the existing node gives local quasi-finiteness of an unramified scheme morphism and no converse or maximal-ideal/residue criterion.

`lem-trf-stalk-formally-unramified-maximal-residue-criterion` vs `lem-weil-pbc-unramified-ring-map-over-field-etale`: the existing node concerns finitely generated unramified algebras over a field and concludes etaleness; it does not handle local stalk maps or the iff with maximal ideals.

`lem-trf-stalk-formally-unramified-maximal-residue-criterion` vs `lem-sbc-dvr-tame-tensor-factor-unramified`: the existing node is a specialized DVR tensor/normalization assertion with ramification hypotheses, not a general local criterion.

`lem-trf-stalk-formally-unramified-maximal-residue-criterion` vs `lem-weil-pbc-unramified-fibre-point-isolated`: the existing node says an unramified point is isolated in its fibre; it does not characterize formal unramifiedness of the actual stalk map.

`lem-trf-stalk-formally-unramified-maximal-residue-criterion` vs `lem-sbc-formally-unramified-stalk-neighbourhood`: the existing node is the one-way spreading implication from a formally unramified stalk to an open neighbourhood; the new node is the local ring iff criterion and includes the converse algebraic condition.

`lem-trf-stalk-formally-unramified-maximal-residue-criterion` vs `lem-sbc-root-normalization-generic-stalk-unramified`: the existing node treats a particular finite etale torsor and normalization at a generic trait point and explicitly does not assert an open-neighbourhood or general local criterion.

`lem-trf-stalk-formally-unramified-maximal-residue-criterion` vs `lem-trf-unramified-locus-base-change`: the existing node characterizes the unramified locus through unramified fibres and base change, whereas the new node characterizes formal unramifiedness of one actual stalk map through its maximal ideal and residue extension.

`lem-trf-stalk-formally-unramified-maximal-residue-criterion` vs `lem-trf-unramified-maximal-ideal-residue-criterion`: the new node is the intermediate actual stalk-ring formal-unramified iff criterion; the existing item adds the existence of an unramified open neighbourhood and is the target equivalence.

## Review by N8

I read Stacks `literature/stacks-project/morphisms.tex` at Tag 02GF, lines 7874–7930, and the Mathlib sources `Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean:120–152` and `Mathlib/RingTheory/Unramified/LocalRing.lean:117–144`. The item statement matches Tag 02GF exactly: (i) is an unramified open neighbourhood at x, and (ii) uses the actual map of local rings, equality of the image of the base maximal ideal with the source maximal ideal, and a finite separable residue-field extension. The new node states the intermediate stalk-map criterion and includes the square-zero lifting meaning of formal unramifiedness.

Step 1 uses the existing statement that an unramified morphism is formally unramified, then the Mathlib `FormallyUnramified.stalkMap` result and the new local criterion. Thus the cited statements provide exactly the formal-unramified stalk map and the two conclusions in (ii); no hidden neighbourhood or residue-field identification is used. Step 2 uses the new criterion in the reverse direction, the existing stalk-to-neighbourhood statement for locally finite type morphisms, and the existing criterion that locally finite type plus formally unramified is unramified. The restriction to an open neighbourhood preserves local finite type directly from the definition. I checked the hypotheses at the actual points and used the actual stalk homomorphism throughout.

For the new node, I searched the whole DAG and blueprint before creating it. Mathlib searches were run with `msearch.py` for LeanSearch, Loogle, LeanFinder, and source grep; the recorded matches are `AlgebraicGeometry.FormallyUnramified.stalkMap`, `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`, and the accompanying finite residue-field instance. The Mathlib source gives the exact local-ring iff and the finite module instance under essential finite type. Small cases checked were an identity map of a field, a finite separable field extension, and a ramified map such as k[t] localized at (t) over k[t²] localized at (t²), where maximal-ideal equality fails. No statement was weakened, no SGA source was used, and both proof steps are under 2000 characters.

## Unfinished work

None.

## Validation

The required dry run remains to be executed after this report is written.
