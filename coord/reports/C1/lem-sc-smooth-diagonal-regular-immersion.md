# Stage-1 Split: lem-sc-smooth-diagonal-regular-immersion

The item is split in `dag/nodes/sec-picard-framework/lem-sc-smooth-diagonal-regular-immersion.json`.

New nodes:

- `lem-sc-standard-smooth-local-relative-dimension`: Mathlib leaf, `AlgebraicGeometry.SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension`, `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean:135-139`.
- `lem-sc-standard-smooth-affine-diagonal-generators`: unsplit statement, with the sorry-free project declaration `AlgebraicGeometry.isRegularImmersion_diagonal_specMap` at `WeilConjectures/AlgebraicGeometry/Morphisms/RegularImmersion.lean:336-364` recorded in its Lean audit.

Attachment: `AlgebraicGeometry.isRegularImmersion_diagonal_specMap` belongs to `lem-sc-standard-smooth-affine-diagonal-generators`. The broader `AlgebraicGeometry.isRegularImmersion_diagonal` at line 396 does not attach to the item: it assumes `d>0` and states weakly regular generators, whereas the item includes `d=0` and asks for ordinary regular sequences near the diagonal.

WANTED: `literature/stacks-project/divisors.tex`, Tags 067R and 067U, for `lem-sc-smooth-diagonal-regular-immersion` and `lem-sc-standard-smooth-affine-diagonal-generators`; the local copy is absent on this machine. I read the Stacks tag pages and the project's completed Lean affine proof. The item's `proof_origin` is therefore `agent`.

## Not duplicates

`lem-sc-standard-smooth-affine-diagonal-generators` vs `lem-pur-diagonal-regular-immersion`: the former is an affine standard-smooth local statement over any commutative base ring, while the latter is a global statement in the purity chapter's fixed finite-field setting and additionally identifies a normal bundle.

`lem-sc-standard-smooth-local-relative-dimension` vs `sbc-thm-etale-local-normal-form`: the latter produces an etale chart with some unspecified dimension; the new Mathlib leaf fixes the chart dimension to the given pure relative dimension `d`.

`lem-sc-standard-smooth-local-relative-dimension` vs `def-sbc-smooth-morphisms`: that node defines smoothness and fibre dimension; it does not assert the existence of an affine standard-smooth chart with the specified dimension.

`lem-sc-standard-smooth-local-relative-dimension` vs `lem-weil-pbc-etale-near-point-smooth-zero-fibre-dimension`: that node says smoothness and zero-dimensional fibre imply etaleness near one point; the new leaf covers every dimension and supplies affine standard-smooth charts.

`lem-sc-standard-smooth-local-relative-dimension` vs `lem-pc-dense-separable-points`: that node concludes density of closed separable points on a smooth variety over a field and uses a local chart only in its proof; it neither states nor supplies the general-base, specified-dimension chart.

## Review by C1

I read Stacks Tags 067U and 067R. Tag 067U states regularity of an immersion between smooth schemes; Tag 067R treats a section of a smooth map. Neither states the number of equations, so the item retains the explicit standard-smooth affine calculation. I checked the Mathlib chart declaration at `Smooth.lean:135-139` and the project Lean calculation at `RegularImmersion.lean:336-375`: the first gives affine charts with the same `d`, and the second gives weakly regular generators of length `d` for the diagonal. At a point on the diagonal the ideal is proper, so weak regularity is ordinary regularity by the definition of `IsRegular`. The affine node is confined to points on the image and `d>0`; these are precisely the hypotheses used in step 4. It is statement only, and its Mathlib searches were run through `msearch.py`; LeanSearch returned HTTP 500 and is recorded unavailable. Searches of the whole DAG and blueprint found no node with the affine statement.

Step 1 uses only the closed-image hypothesis and the affine-open basis. In step 2 I checked the exact final sentence of `def-sbc-smooth-morphisms` (smooth relative dimension zero means etale), the definition in `def-weil-etale-morphism` (etale implies unramified), and `def-weil-unramified-morphism` (the diagonal is open). Together with the item's closed-diagonal hypothesis, the image is clopen, and its ideal is zero on an affine open inside it. I removed an earlier section-of-etale-projection route because it required an unnecessary separated-base-change premise. Step 3 takes the specified affine chart from the Mathlib leaf; the fibre-product universal property identifies the chart's diagonal with the global diagonal restricted to the open `V x_T V`. Step 4 uses the affine node's stated regular generators, not details hidden in its proof; openness transfers the same ideal to an open of `X x_S X`.

I checked the small cases `d=0` (empty regular sequence on the diagonal), points off the diagonal (unit ideal), and the identity map (again `d=0`). The affine node requires `d>0`, and the item applies it only in that branch. The item statement has not been weakened. The original source field gave a mutable Stacks lemma number; I replaced it with stable Tags 067U and 067R. The local Stacks source is missing as noted above.
 
## Second reading by C1

- Item statement: checked against Stacks Tags 067U and 067R and the affine standard-smooth calculation; all hypotheses and the length-d conclusion agree.
- Step 1: checked the closed-immersion hypothesis and the open complement; empty preimage and unit ideal are elementary.
- Step 2: checked `def-sbc-smooth-morphisms`, `def-weil-etale-morphism`, and `def-weil-unramified-morphism`; d=0 gives an open and closed diagonal with zero ideal.
- Step 3: checked `lem-sc-standard-smooth-local-relative-dimension`; the Mathlib declaration supplies the affine standard-smooth chart and the fibre-product universal property identifies the restricted diagonal.
- Step 4: checked `lem-sc-standard-smooth-affine-diagonal-generators`; its stated regular generators transfer from the chart to the original diagonal.
- New node `lem-sc-standard-smooth-local-relative-dimension`: B1-B7 and Mathlib lines 135-139 plus all recorded searches checked; verdict mathlib leaf.
- New node `lem-sc-standard-smooth-affine-diagonal-generators`: B1-B7, the closed Lean declaration at lines 336-364, and all recorded searches checked; verdict unsplit closed declaration.
- Small cases checked: d=0 and identity use the empty sequence; off-diagonal points use the unit ideal; d>0 matches the NeZero hypothesis.
- Changes: none to statements or proof; this section records the required second-reading checks.
