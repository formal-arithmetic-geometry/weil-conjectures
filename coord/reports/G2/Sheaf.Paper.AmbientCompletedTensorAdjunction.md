## What changed

Repair of the returned global build: qualified the new private transition helper's
module-sheaf binder as `ConstantCompletion.Mod` and supplied the site/coefficient
arguments at its rewrite in `finiteTensorStep_existsUnique`. This fixes the reported
line 86 namespace mismatch and line 151 stuck `SmallCategory` instance. The exact
returned proof packet was recovered from commit `55f3d6fbd8d`; all proofs below
are retained. No public signature changes are made by this repair.
Nested existence eliminations in the ambient theorem are replaced by local
witness selections to reduce kernel-checking cost. The finite-tower witnesses
come from the fully proved comparison theorem; the reflector is the existing
unit-normalized reflector used by the original proof.

Proved `CategoryTheory.AmbientCompletedTensor.finiteTensorStep_existsUnique` by
transporting the actual reduction transition through the normalized scalar
total-tensor comparison. Bilinearity gives the formula for both scalar factors;
the existing extended-total-tensor generator extensionality proves uniqueness.

Added the fully proved module `Sheaf.Paper.NormalizedFiniteTensorComparison`.
Its additive instance parameter is supplied by the proved additivity of the
actual extension/restriction composition. Keeping the finite comparison in its
own module avoids repeating its costly type checking in the adjunction file.

Also proved the sole hole of the unclaimed existing dependency
`Sheaf.Paper.QuotientTotalTensorTowerComparison`. Its normalized finite comparisons
commute with successors by generator extensionality, and `NatTrans.ofOpSequence`
assembles them. This proof stays in that existing module so that the item does
not contain both substantial proofs in one compilation. Its public interface
is unchanged; the item's original application of it is retained.

The concrete finite-field datum in the final completeness proof is factored into
a private irreducible definition with its proved prime-projection equation.
All existing public statements, public imports, attributes and data-definition
bodies are unchanged. No consumer adaptation is needed. The item is the tower
comparison's only original direct importer and is compiled against its new proof.
The nodes' proof routes and dependency lists follow the Lean proofs.

Repair validation: all three modules typecheck with zero holes. The repaired item
passes standalone in 44.2 seconds after reducing existence-elimination overhead.
Development profiling options were removed before delivery. The reported namespace and stuck-instance errors
are gone.

Validation: remote single-file compilation of the normalized scalar comparison,
the general tower comparison, and its direct importer (the assigned item), followed
by the delivery preflight. The tower comparison compiled in 34.5 seconds and the
item in approximately 40.9 seconds, both below the 60-second limit. Existing
statements and data definitions were also compared verbatim with the source.

## Proved and sorry left

Closed the item's sole original hole:
`CategoryTheory.AmbientCompletedTensor.finiteTensorStep_existsUnique`
(node `lem-sf-ambient-completed-tensor-adjunction`): 1 of 1.

Also closed
`CategoryTheory.AmbientCompletedTensor.quotientTotalTensorTowerComparison`
(node `lem-sf-quotient-total-tensor-tower-comparison`): 1 of 1 in that dependency.

The new theorem
`CategoryTheory.AmbientCompletedTensor.normalizedFiniteTensorComparison`
(node `lem-sf-normalized-finite-tensor-comparison`) is fully proved.

Total original holes in delivered modules: 2. Closed: 2. Added: 0. Remaining: 0.
No split-off holes or decomposition.

## No longer needed

No original imports or modules are removed. The strict tower comparison remains
needed and is now proved rather than left as a further item.

`def-pur-sheaf-tensor-product` and `def-pc-tensor-complex-sheaves` are no longer
direct proof dependencies of the finite-transition construction, and the tower
proof also uses the proved normalized scalar comparison instead of rebuilding
its constituent tensor algebra. Their tensor constructions remain in use through
the existing coefficient-model interface and scalar comparison; they are not
claimed as pruned modules. The tower node's other former direct proof dependencies,
`def-sfb-constant-completion-coefficient-data`,
`def-pur-strict-quotient-completion-data`, and
`def-coef-ringed-tensor-hom-model`, remain statement dependencies and provide the
underlying constructions. The recorded unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier DAG described the unique finite successor and the separate strict
tower comparison as still requiring their balanced constructions. Existing
proved generic scalar comparison and generator-extensionality helpers suffice,
including on arbitrary small ringed sites. They require no Noetherian, flatness,
boundedness or proper-ideal restriction. The zero ideal, unit ideal, zero ring
and empty site are included: no nonzero or nonempty hypothesis is used.

During this session the shared source was quarantined by the 2026-10-27 build
(row timestamp 02:47:45Z): two proof-local `Mod` references resolved to the wrong
namespace after the S4 integral-operations update. The sandbox retains the whole
archived module and qualifies those references as `ConstantCompletion.Mod`.
The intended module-sheaf categories, public statements and definitions are
preserved. No archive is deleted and no withdrawal is made.

## New nodes

`lem-sf-normalized-finite-tensor-comparison` records the proved finite scalar
comparison with the formula for both scalar factors. Its proof uses the existing
generic scalar total-tensor isomorphism and bilinearity. It is a finite-level
step used by both the successor and strict tower arguments. No new hole is added.

Change record: `coord/changes/G2-quotient-total-tensor-tower-proof.md` records the
proof-only change to the unclaimed existing tower-comparison module and its user.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
