## What changed

The signature and public imports of
`AlgebraicGeometry.Scheme.fullyFaithful_completed_punctured_quotient` are unchanged.
Its proof now transfers depth by flat-local preservation of regular sequences,
identifies the completed puncture, and proves bijectivity on Hom sets. Private
helpers prove injectivity using the faithful geometric fibre functor and
surjectivity using unique nilpotent lifts, scalar formal comparison, the existing
finite-etale sections transfer, and the quasi-affine toSpecGamma pullback.
All added imports in the original module are proof-only.

Two new modules supply the needed connectivity/principal-slice lemma and isolate
the remaining scalar formal comparison. The connectivity module is fully proved
from depth-two Hartogs, the dimension bound, the principal ideal theorem, and the
idempotent connectedness criterion. The updated original DAG proof follows the
Lean proof, rather than treating full faithfulness as a direct application of 0BM6.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.fullyFaithful_completed_punctured_quotient`
(node `lem-sbc-completed-punctured-quotient-fully-faithful`), from the dependencies
listed in its revised node. No sorry remains in the original module or its private
helpers.

New and proved: `AlgebraicGeometry.Scheme.depth_two_punctured_principal_slice_connected`
(node `lem-sbc-depth-two-punctured-principal-slice-connected`).

Added hole: `AlgebraicGeometry.Scheme.complete_punctured_principal_formal_sections`
(node `lem-sbc-complete-punctured-principal-formal-sections`), in its own module.
Its body is exactly `:= by sorry`. This is only the scalar structure-sheaf formal
comparison; it asserts neither full faithfulness nor algebraization of cover maps.
The categorical construction combining it with existing lemmas is complete Lean.
This is a decomposition: one original hole closed, one smaller hole added, net zero.
No axiom-free proof of the full dependency closure is claimed.

All three sandbox modules compiled cleanly with lcompile --all. In particular the
new connectivity module and the entire finite-etale glue are kernel checked.
Edge cases checked: g = 0, nilpotent g, and empty covers need no cancellation or
nonzerodivisor hypothesis; depth at least two guarantees the slice is nonempty.

## No longer needed

No original imports removed; no existing module is claimed globally pruned.
The original proof route's use of derived local-cohomology base change (0ALZ)
and henselian-pair terminology (0ALJ) is unnecessary in the original module.
`def-weil-flat-morphism` and `def-weil-pbc-henselian-terminology` are removed from
its proof_deps: ring-module flatness is used directly, and unique nilpotent lifts
replace the proposed henselian-pair application. Existing statement dependencies
are unchanged. The scalar comparison retains its own completeness/cohomology input.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The old node's final instruction to apply 0BM6 was
not a Lean declaration giving the needed comparison. The missing geometric input
is now isolated as scalar formal comparison (Stacks 0EII), with the rest of that
application written out in Lean. Completion preserves depth directly through
regular sequences, avoiding the planned derived base-change detour. No unit-level
statement or realized step is bypassed. No existing statement or definition was
changed and no forced adaptation was needed.

## New nodes

`lem-sbc-depth-two-punctured-principal-slice-connected`: the puncture of a
Noetherian local ring of depth at least two is connected and meets every principal
closed slice defined by an element of the maximal ideal. The module
`Sheaf.AlgebraicGeometry.Morphisms.DepthTwoPuncturedPrincipalSliceConnected`
contains a complete proof.

`lem-sbc-complete-punctured-principal-formal-sections`: compatible scalar sections
on principal thickenings of a depth-three complete local puncture have a unique
algebraization. The module
`Sheaf.AlgebraicGeometry.Morphisms.CompletePuncturedPrincipalFormalSections`
contains the one remaining sorry, with source and complete mathematical proof.
The two nodes have their own search records and inherit the original unit and
blueprint lineage. No change record is required.

## Second reading by T3

1. Compared the delivered module with the repository version. The target theorem signature is byte-for-byte unchanged; added declarations are private helpers and two separately stated nodes. Verdict: pass.
2. Compiled all three sandbox modules with `lcompile.py --all`; there are no errors, and the only remaining `sorry` is the named scalar comparison theorem. No prohibited declarations or hollow definitions were found. Verdict: pass.
3. Checked the split-off statements against their docstrings, DAG nodes, and source tags. The connectivity statement is proved; the scalar comparison is a strictly smaller formal-sections input and is explicitly documented with its node. Verdict: pass.
4. The proof follows the shortest available route using existing finite-etale lifting/sections results, direct flat-local depth transfer, and the new connectivity lemma. The original target imports remain public only where needed by declarations; proof-only imports are plain imports. Verdict: pass.
5. The target DAG proof and proof dependencies match the implementation, and the unit route is retained. No existing statement or definition was changed; no forced adaptations or pruning beyond the report are needed. Verdict: pass.

Changed during second reading: no Lean proof or statement changes; appended this review record only.
