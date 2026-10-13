## What changed
Added the proof-only import of `Sheaf.Algebra.Homology.ResidueKernelLocalizedCokernelTransport`.
The target theorem is proved by composing Mathlib's `localizedQuotientEquiv` with the
strictly smaller scalar-extension quotient transport theorem.
Added the transport module and its DAG node.

## Proved and sorry left
`ModuleCat.residue_kernel_localized_cokernel` is proved.
`ModuleCat.localized_range_quotient_extendScalars` remains sorry as the strictly smaller
intermediate scalar-extension transport statement, with node
`new-residue-kernel-localized-cokernel-transport`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt correctly identified that scalar-extension transport is nontrivial;
this delivery isolates exactly that transport as a named intermediate theorem and makes
the planned `localizedQuotientEquiv` composition concrete.

## New nodes
`new-residue-kernel-localized-cokernel-transport`: quotient of a localized module by a
localized range is equivalent to the scalar-extension quotient; module and node are in
this delivery.

## Earlier second reading (a previous round; superseded)
The target theorem's unchanged signature is proved by a genuine composition with
`localizedQuotientEquiv`; the only remaining sorry is the strictly smaller transport
node, whose statement matches its Lean declaration and is needed by the composition.

## Second reading by U4

1. I diffed `ResidueKernelLocalizedCokernel.lean` against the repository version. The
   existing theorem signature and all definitions are byte-for-byte unchanged; only a
   proof-only import and proof body were added. Verdict: pass.
2. Both delivered modules compile with the prescribed `lcompile.py --all` command. The
   target has no `sorry`; the named transport theorem is the sole remaining `sorry`, and
   it is public, documented, and represented by its split DAG node. No forbidden
   declarations or hollow definitions were introduced. Verdict: pass.
3. The target proof uses Mathlib's `localizedQuotientEquiv` and the explicitly split
   scalar-extension transport theorem. The split statement is strictly smaller than the
   target and has the same hypotheses needed by the composition. Verdict: pass.
4. The proof follows the stated localization/range-quotient route; no import was removed,
   and the proof-only transport import is private. The unit route remains represented by
   `new-residue-kernel-localized-cokernel`. Verdict: pass.
5. The target node's proof and proof dependencies agree with the Lean proof, and the new
   transport node records the exact declaration, source, and split status. Verdict: pass.

Changed during second reading: reverted an exploratory, incomplete proof attempt in the
transport module; retained the compiling target composition and added this review record.
