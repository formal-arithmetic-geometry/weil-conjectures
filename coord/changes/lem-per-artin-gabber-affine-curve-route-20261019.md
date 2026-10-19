# lem-per-artin-gabber-affine-curve: finite coefficients and the blueprint route (2026-10-19)

## Reason

Route decision of the human, 2026-10-19. The stage-1 split of lem-per-artin-gabber-affine-curve by Q144 (5ea9835359, 2026-10-18,
reviewer NT-cc-Q144-f0aa142b4) restated the lemma over $D^b_c(-,\overline{\mathbf Q}_\ell)$ on an arbitrary field and
routed it through new children lem-per-qbar-arbitrary-field-duality, lem-per-qbar-middle-tstructure,
lem-per-qbar-ordinary-adjunction (with lem-per-arbitrary-field-adjunction-scalars) and lem-per-qbar-affine-support-bound.
These escalate through lem-per-finite-residue-dualizing, lem-per-finite-exceptional-preservation and
lem-per-quasi-excellent-etale-direct-image-finiteness (Gabber's finiteness over quasi-excellent bases) to Gabber's
uniformization, de Jong's alterations and the stable-reduction part of the trace-formula chapter. That generality is not
needed: the upstream Lean statements (WeilConjectures.SixFunctors.Etale.Perverse.Operations,
isPerverseLE_lowerShriek / isPerverseGE_lowerShriek) are at finite coefficients, and the blueprint/BBD proof needs no
biduality, no middle t-structure and no Gabber finiteness. About 1,700 unfinished batch-5 nodes hung only on that split.

## Old

Statement over $\overline{\mathbf Q}_\ell$-coefficients on an arbitrary field; proof: arbitrary-field relative duality and
biduality, the middle t-structure, the ordinary adic adjunction and BBD 1.3.17(iii), the adic affine support bound
(steps 1-6 of 5ea9835359).

## New

Statement: the upstream finite-coefficient form (finite $\Lambda$ with exponent invertible in $k$, any field $k$, $K$ in
$D^b_{ctf}$, all shifts $n$; support and cosupport conditions with closed supports and the dual relative to the structure
map, as in Perverse/Basic.lean). The `lean` record is unchanged (the two upstream declarations).
Proof plan (blueprint and BBD 4.1.1, 4.1.2, 4.2.4):
- support side: proper base change, $\operatorname{cd}\le2\dim$ over a separably closed field and the fibre-dimension
  count, packaged in the new node lem-per-finite-compact-support-fibre-support-bound; devissage by truncations;
- cosupport side: the ordinary exchange $D_YRf_!\cong Rf_*D_X$ from prop-asd-internal-adjunction (no finiteness, no
  biduality), constructibility of the finite-coefficient dual over a field (new node lem-per-finite-coefficient-dual-constructible, via finite-type direct
  images thm-dg-finite-type-constructibility and purity of affine space, not Gabber), and Artin's affine estimate at finite
  coefficients (new node lem-per-finite-affine-direct-image-support-bound, from lem-kun-affine-direct-image-support-bound, Stacks 0F0X).

lem-per-artin-gabber-affine-curve is returned to stage 1 with keep_plan (coord/repair-notes/lem-per-artin-gabber-affine-curve.json in the side project): the worker delivers this plan
for review and keeps its coefficients and route. The three new nodes are stage-1 items (status unsplit).
The dropped route (nodes no longer reached from any target) is listed in the 2026-10-19 section of
coord/route-pivot-dropped.txt (side project); the review service rejects splits that cite them again.

Known consequence: thm-fd-fourier-perverse step 5 applies this lemma in its $\overline{\mathbf Q}_\ell$ reading, while its own
Lean record (isPerverseLE_fourierTransform) is finite-coefficient like this node; its NL step should be read at finite
coefficients, matching its Lean statement.
