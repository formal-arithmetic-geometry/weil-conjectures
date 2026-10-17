## What changed

Completed the private theorem `CochainComplex.truncation_boundary_kernel` in
`Sheaf.CategoryTheory.GoodTruncationTotalBoundaryImage`. The existing total-image
proof and all declaration signatures are unchanged.

The proof uses the first component of the already proved upstream private lemma
`CochainComplex.truncLE_inclusion_coordinates`: the canonical truncation-to-cycles
isomorphism followed by the cycles inclusion equals the truncation inclusion.
The composite with the outgoing differential therefore vanishes by
`HomologicalComplex.iCycles_d`. Transporting `HomologicalComplex.cyclesIsKernel`
along that isomorphism using `Fork.ext` and `IsLimit.ofIsoLimit` establishes the
required universal property. This works for every integer boundary, including
zero complexes and zero differentials, without new assumptions.

Replaced the proof import of the retired
`Sheaf.Algebra.Homology.UpperTruncationStepSES` wrapper with
`import all WeilConjectures.Algebra.Homology.UpperTruncationStepQuotient`, where
that proved coordinate lemma now resides. No public imports or interfaces change.
The existing DAG boundary-kernel/direct-sum argument is followed, so its node
`lem-sp-good-truncation-total-boundary-image` needs no route change.

Validation: the complete module compiled cleanly through `lcompile.py` in 4.3
seconds. The required delivery dry run also checks its declaration axioms.

## Proved and sorry left

Closed 1 of the original 1 holes:
`CochainComplex.truncation_boundary_kernel`, the local kernel step of
`lem-sp-good-truncation-total-boundary-image`.

There are zero remaining holes in the item, zero holes added, and zero split-offs.
In particular, `HomologicalComplex₂.good_truncation_total_boundary_image` now has
a complete proof together with all of its local helpers. The reused upstream
coordinate lemma is proved; this is a proof, not a decomposition.

## No longer needed

Removed the direct proof import
`Sheaf.Algebra.Homology.UpperTruncationStepSES`. Its re-exported module
`WeilConjectures.Algebra.Homology.UpperTruncationStepSES` and the latter's proof
dependency `WeilConjectures.Algebra.Homology.TwoTermCoimageQuasiIso` are also
unnecessary for this item's proof. Thus the item no longer needs nodes
`lem-weil-pbc-truncation-step-ses` or
`lem-weil-pbc-two-term-coimage-quasiiso`. This reports pruning from this item's
imports; other targets or parents may still use those modules.

The replacement coordinate module remains needed, as do the double-complex total,
truncation-degree, and subobject-limit imports. No unit statement or unit proof
step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The actual remaining hole is a private kernel-universal-property theorem; the
large public total-boundary-image proof was already complete modulo this helper.
The old `import all` named a retired re-export wrapper, while the reusable
coordinate theorem lives privately in the upstream quotient module. Importing
that module directly provides the needed existing proof. No mathematical
statement or definition repair was necessary.

## Second reading by J3

1. **Interface and accidental changes.** I diffed the delivered module against
the repository version. The only changes are the proof-only import and the
private proof of `CochainComplex.truncation_boundary_kernel`; the public target
and every existing declaration signature are unchanged byte-for-byte. No
definition, statement, or change record was introduced.

2. **Proof and axioms.** The module compiles cleanly with `lcompile.py`. It has
no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow
definition. The kernel proof transports `cyclesIsKernel` across
`truncLEXIsoCycles` and uses the proved coordinate identity, so it establishes
the universal property for every integer boundary, including zero cases. The
delivery preflight checks the target's permitted axioms.

3. **Statements and split-offs.** No statement was split off and no new node
was added. The private helper is a strictly local kernel construction needed by
the target proof and does not restate the target. The target theorem's statement
continues to express the finite-diagonal boundary-kernel image calculation in
the existing node.

4. **Pruning and route.** The old wrapper import is replaced by the direct
quotient module that contains the already proved coordinate lemma; this removes
the wrapper and its two-term coimage proof from this item's proof closure. The
remaining imports are used by declarations or proofs in this module. The
finite-diagonal/direct-sum route and the unit's recorded route are unchanged.

5. **DAG agreement.** The target node's statement and proof dependencies remain
valid: its direct-sum and boundary-kernel argument is exactly the proof written
here, with the upstream coordinate identity supplying the local kernel step.
No node metadata or unit record needed alteration.

I changed only the private helper proof, its proof-only import, and this review
report; no mathematical interface was changed.
