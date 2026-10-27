## What changed

Replaced the sorry in `WeilConjectures.PurityFiniteSetting.smooth_clopen_component_inverse`
by a complete Lean reduction. The statement and all original public imports are unchanged.
Added the proof-only imports `SmoothClopenResidueLine`, `SfDerivedCompleteLegacyComparison`,
`PurityFiniteSettingComparisonHypotheses`, and `Mathlib.Data.Nat.Prime.Infinite`.

The private integral argument works at every finite coefficient field. It obtains the
residue line, proves the required completeness comparison and Noetherianity, applies
`completeResidueLineInverse`, compares the two specified completed tensors using their
normalized universal property, and lifts both evaluations through the fully faithful
constructible inclusion. Rational localization carries both evaluations to the actual
rational exceptional image using its coherence equation. The common-stage argument
includes the compositum comparison and the identity scalar unitor, then applies the stage
inclusion to both evaluations.

The item compiles in 24.7 seconds and the new residue-line interface in 8.4 seconds using
`lcompile.py`. Neither file changes a shared definition or any existing signature.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurityFiniteSetting.smooth_clopen_component_inverse`
(node `lem-pur-smooth-clopen-component-inverse`). There are zero sorries in the item.

Added one sorry, and no others:
`WeilConjectures.PurityFiniteSetting.smooth_clopen_residue_line`
(node `lem-pur-smooth-clopen-residue-line`, module `Sheaf.Paper.SmoothClopenResidueLine`).
This is a decomposition: one upper hole closed, one smaller residue-identification hole
added, so the net hole reduction is zero. The new conclusion only concerns the first
reduction; it asserts no tensor inverse, no integral finite-Tor bounds, and no rational
or common-stage invertibility. The Lean combination proving all those assertions is
complete. Existing dependency sorries, notably `completeResidueLineInverse`, remain with
their existing owners and nodes.

## No longer needed

No original import was removed and no module was withdrawn. No whole module is claimed
pruned. The item's direct proof no longer needs `thm-asd-smooth-tensor`,
`def-weil-exceptional-inverse-image`, `thm-weil-pbc-site-comparison`, or
`det-sp-unique-right-adjoint`; these remain necessary proof dependencies of the smaller
residue-line node. The finite-only inverse theorem
`Sheaf.Paper.SmoothFiniteDualizingInverse` is not imported: finite invertibility does not
identify the residue of the actual integral exceptional image. No unit-level step is
bypassed; `sk-def-purity-conv` has no prescribed realized statement or proof steps.

## Where the brief, the DAG or earlier work was wrong

The original proof plan does not directly supply a declaration presenting the first
reduction of an arbitrary normalized component integral exceptional value as the shifted
etale line. Its finite exceptional and smooth tensor declarations describe the finite
value; they do not alone identify that value with the scalar reduction of the integral
one. The new node isolates precisely this missing interface, with the same actual
normalized systems and right-adjoint comparison required by the original plan. Several
related adic/finite-reduction APIs also impose absolute separatedness of X and Y, which
the present statement correctly does not assume; no such hypothesis was added here.

The recorded complete-residue theorem uses `IntegralOnSlice.completedTensor` whereas
the clopen tensor uses `integralCompletedTensor`. These are compared in Lean through the
existing normalized descent universal property, rather than treated as definitionally
equal. Likewise common-stage tensor is formed at the compositum even when both inputs
are represented at one stage; its identity-extension comparison is explicitly used.

Edge cases of the new statement were checked against its source argument: d=0 has zero
shift, empty Xi has the zero categories and unique comparisons, and the residue field is
nonzero for a genuine finite extension of Q_l. No orientation or line basis is required.

## New nodes

`lem-pur-smooth-clopen-residue-line` records only Step 1 of the original node: the first
reduction of the actual integral exceptional coefficient-unit value is an intrinsic
shifted etale line. Its source and full natural-language proof are in the module docstring
and node. LeanFinder, Loogle, LeanSearch and Mathlib grep found no replacement; project
searches found the finite inverse and complete-residue APIs used or distinguished above.
No change records are needed because no existing statement, definition or consumer changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.SmoothClopenComponentInverse": "f3f572809ac0e849235bc80b4577f54f4e993937", "Sheaf.Paper.SmoothClopenResidueLine": "6bf31555755d51417b842bc435008d22620b0801"}, "results": {"Sheaf.Paper.VaryingDimensionDualizingInverse": {"hash": "b76346912b6b41dc747a104b368dfa3b09ca165a", "status": "OK"}}, "seconds": 45, "time": "2026-10-28T03:26:26+0800", "transitive": 0, "version": 1}
```

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
