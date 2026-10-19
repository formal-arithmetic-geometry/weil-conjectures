## What changed

Proved both theorems in
`Sheaf.AlgebraicGeometry.GeometricallyIrreducibleAlgebraClosure`, with their public
statements and visibility unchanged. Retained and repaired the earlier sandbox
proofs rather than replacing the item or moving its holes elsewhere.

The injective-map theorem uses flatness over a field to tensor the injection,
then comaps the prime nilradical. The colimit theorem passes from algebras to
modules by preservation and reflection of colimits, tensors the module colimit,
and detects nilpotence at a later stage. A private proved helper establishes
primality of the colimit nilradical, including its properness; transition maps
need not be injective. All private definitions construct their data directly.

Replaced the three faithfully-flat/ring-map imports listed below with
`Mathlib.RingTheory.Flat.Basic` and
`Mathlib.LinearAlgebra.Basis.VectorSpace`. Updated the existing node's proof,
proof dependencies, proof origin and obsolete tool-use approvals to match the
implemented argument. No public interface or consumer module changed.

Validation in this resumed session: the required `deliver3.py --no-push` dry run
passed compilation and preflight at commit `09e62e9d7e`, classified CODEX because
the delivery changes a node file. Both public signatures are textually identical
to the current library statements, all lines meet the 100-character limit, and
no hole tokens remain. The source was checked against Stacks Tag 037N(1),(3),
including the nonempty index and zero-ring cases. Earlier scratch audits reported
only `propext`, `Classical.choice` and `Quot.sound`.

## Proved and sorry left

Closed both original holes (2 of 2):

- `AlgebraicGeometry.geometricallyIrreducible_spec_of_injective`.
- `AlgebraicGeometry.geometricallyIrreducible_spec_colimit`.

Both realize `lem-zl-geometric-irreducibility-subalgebra-colimit`.
There are zero remaining holes, zero added holes and zero split-off statements.
Every helper has a complete proof. This is a proof of both clauses, not a
relabeling or decomposition of their holes.

## No longer needed

Removed imports:

- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`.
- `Mathlib.RingTheory.RingHom.FaithfullyFlat`.
- `Mathlib.RingTheory.RingHom.Flat`.

Removed proof dependencies:

- `lem-weil-pbc-field-extension-base-change-faithfully-flat`.
- `def-weil-pbc-faithfully-flat-ring-map`.
- `lem-weil-pbc-filtered-colimit-rings-zero`.

Flatness comes directly from the free-module instance over a field. The module
colimit follows from preservation and reflection by forgetful functors; its
construction does not require an explicit ring-representative equality argument.
The module-representative and zero-detection dependency remains necessary for
the tensor-colimit argument. The two obsolete entries of the top-level
`tool_uses` list were removed in their existing order.

No Sheaf dependency is imported: the retained dependencies are Mathlib leaves
whose declarations are used directly. No module is withdrawn. No unit statement
or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's unvalidated code contained binder syntax errors, inferred
algebra-map arguments that required specification, and a ring-hom coercion that
needed to be explicit. Those repairs were retained. Prior compiler response
failures and a timeout had prevented delivery. In the current resumed session the
module compiled successfully; the required delivery audit is recorded above.
No compilation limit was raised and no launcher tool was changed.

The DAG's faithfully-flat detour and explicit construction of the underlying
module-colimit descent map were unnecessary. The existing node now records the
shorter arguments actually checked by Lean. No statement was disputed or
changed, and no definition used by a target was changed.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
