# Stage-1 report: lem-a1-affine-hc2

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-affine-hc2.json`: existing item, updated to the current main-20261015 blueprint proof, marked `split`, with the four audited proof steps and recorded Mathlib searches; no new nodes.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

## Attachments

None. The reference source declaration `compactTopFrobenius` is an endomorphism on representation coinvariants, not the requested canonical Frobenius-equivariant isomorphism involving `H_c^2`; it therefore does not attach to this item.

## WANTED

None.

## What was checked and corrected

The imported statement was compared with `literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-p-real-semi/lem-a1-affine-hc2.md`; its mathematical text is unchanged from the imported statement (only the blueprint order changed). The proof was read from `literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-p-real-semi/lem-a1-affine-hc2.proof.md`. The source declaration and its docstring were read at `WeilConjectures/EtaleCohomology/Purity/RealSheaves/Rankin.lean:309-321` in the read-only slopmaster2 source; it defines only `compactTopFrobenius`.

## Review by NS

I checked every proof step against the statement of each cited DAG node and recorded the exact text in `citations.json`.

1. The opening step uses `lem-wf-curve-normal-smooth-compactification` for the smooth projective compactification and `def-pod-conventions` for the dualizing complex and orientation. I verified that the compactification hypothesis (normal, geometrically connected, finite type, pure dimension one) is supplied by the smooth affine curve assumptions and that the orientation is the `d=1` specialization.
2. The compact-support step uses `def-compact-support-direct-image-detailed` for the compactification formula, `def-weil-extension-by-zero` for `j_!`, `fix-lem-exchanges` for composition, and `def-weil-ordinary-compact-cohomology` for the definition of `RΓ_c` and `H_c`. I checked that the identity compactification of the open immersion gives `Rj_!=j_!` and that the coefficient object lies in the constructible finite-Tor domain.
3. The duality step uses `thm-pod-global-verdier-duality`, `fix-cor-verdier-exchange`, `prop-exc-open-adjoint`, and `lem-weil-derived-direct-image-composition`. Their statements respectively give global duality, the Verdier exchange map, the `j_! ⊣ j^*` adjunction, and the canonical composite direct-image comparison. I checked that `K=j_!ℱ` is the constructible object to which duality applies, and that the smooth orientation gives `ω_U ≃ E_U(1)[2]`.
4. The degree `-2` step uses `def-wf-fundamental-representation`, `p-real-sections`, `def-wf-monodromy-data`, and `def-wf-tate-twist`. I verified that `p-real-sections` states exactly the global-sections/invariants identification and that the remaining passage from the dual of invariants to coinvariants, including inversion of the twist, is the elementary finite-dimensional linear-algebra step. Frobenius compatibility follows because all compactification and orientation maps descend from `k_0`, as stated in the blueprint proof.

I searched the whole DAG and current blueprint for duplicate statements and for a separate invariants/coinvariants lemma; no existing node states a strictly smaller missing fact needed by this proof, so no node was created. The item was tested on the zero sheaf (both sides zero), the constant sheaf on an affine line (coinvariants one-dimensional and twist `(-1)`), and a sheaf with no geometric coinvariants (both sides zero). No statement or hypothesis change was needed.

## What could not be finished

Nothing. The required split, citation audit, Mathlib searches, and report are complete; the dry run is the remaining delivery check.
