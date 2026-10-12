## What changed

Replaced the target theorem's sorry with a complete application of a reusable
fraction-field geometric-regularity transport theorem. Added the helper module
`Sheaf.RingTheory.FractionFieldGeometricRegularityTransport`, whose theorem states
the generic transport step with an arbitrary A-algebra C. The target signature and
public imports are unchanged; the helper is an ordinary proof import.

## Proved and sorry left

Closed `genericFormalFiber_geometricallyRegular_of_fractionField_transport` by
specializing the helper to the specified adic completion. The helper theorem
`fractionField_geometricallyRegular_tensorProduct_transport` remains as one named
sorry, with node `lem-weil-pbc-fraction-field-geometric-regularity-transport`.
This is a strict decomposition: the helper removes the completion and prime-ideal
wrapper and isolates the universal-property and tensor-equivalence argument.

## No longer needed

No existing imports or nodes were removed. The target's original proof had no
usable proof dependencies; the new helper node is the only direct dependency.

## Where the brief, the DAG or earlier work was wrong

The blueprint presented the universal-property and tensor-product transport as one
step but provided no Lean declaration for it. I isolated that step as a generic
A-algebra theorem so the target proof can be checked by specialization. The
universal-property argument remains open in the helper theorem and is documented
there from Stacks Tags 07PS and 07PP.

## New nodes

`lem-weil-pbc-fraction-field-geometric-regularity-transport` records the helper
statement, source, search results, proof plan, and Lean declaration in
`Sheaf.RingTheory.FractionFieldGeometricRegularityTransport`.

## Second reading by S3

1. I compared both delivered modules with the repository versions. The target theorem
   signature is byte-for-byte unchanged; the helper is a new proof-only module and the
   target adds only a private import. Verdict: pass.

2. I compiled both modules with `python3 /home/ubuntu/weil-launcher/lcompile.py --all`.
   They compile without errors or warnings. The target has no `sorry`; the only remaining
   `sorry` is the named helper theorem, which has its own DAG node and source-backed
   docstring. No definitions contain `sorry`, and no forbidden declarations were added.
   Verdict: pass.

3. I checked the split-off helper statement against the fraction-field transport argument.
   It has exactly the original assumptions and conclusion needed by specialization, with
   no extra hypothesis or weakened conclusion. A search of the existing Sheaf modules
   found no declaration with this statement; the nearby field-isomorphism results are
   lower-level ingredients rather than duplicates. Verdict: pass.

4. The target proof is the shortest available specialization of the generic transport
   theorem. The completion is introduced once and passed directly to the helper. The
   helper's universal-property/tensor-equivalence step remains explicitly open, so this
   is a genuine strict decomposition rather than a restatement. No prior imports or DAG
   proof dependencies became unused. Verdict: pass.

5. The target node now records the helper as its sole proof dependency, and the helper
   node records its declaration, source, split status, and proof plan. The unit route is
   preserved: the target still realizes the generic formal-fibre transport step and the
   helper isolates only the fraction-field transport substep. Verdict: pass.

I changed only this report section. No Lean statements or proofs required repair after
compilation and comparison.
