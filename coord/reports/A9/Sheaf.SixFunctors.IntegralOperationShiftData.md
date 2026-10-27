## What changed

Decomposed `tensorShifts_existsUnique` into the four independent normalized tensor-slot
existence/uniqueness results and wrote its complete Lean assembly proof. The proof constructs
all four families from unique characterizations and uses slot uniqueness, function
extensionality and proof irrelevance to identify any competing record.

Moved the nine unchanged normalization definitions to IntegralTensorShiftProperties and
publicly reexported them from the original module, preserving every original public import.
The four new theorem modules privately enter the original module. This extraction avoids
an import cycle and leaves the definitions visible to all 53 transitive consumers.
Consumer inventory and exact old definitions are recorded in
coord/changes/A9-integral-tensor-shift-properties.md. No consumer source needs adaptation.

## Proved and sorry left

Original holes: 3. One original hole is closed by decomposition:
`WeilConjectures.IntegralSystemRealization.tensorShifts_existsUnique`.
This is a decomposition, not a net reduction of the proof obligations.

Two original holes remain unchanged, both at def-pur-integral-operation-shift-data:

- `WeilConjectures.IntegralSystemRealization.IndependentExpression.shift_naturality`.
- `WeilConjectures.IntegralSystemRealization.limitShift_roos`.

Four holes are added, each in a separate module and with its own node and complete
source-guided proof in words:

- `WeilConjectures.IntegralSystemRealization.systemTensorLeftShift_existsUnique`
  (lem-pur-system-tensor-left-shift-unique).
- `WeilConjectures.IntegralSystemRealization.systemTensorRightShift_existsUnique`
  (lem-pur-system-tensor-right-shift-unique).
- `WeilConjectures.IntegralSystemRealization.integralTensorLeftShift_existsUnique`
  (lem-pur-integral-tensor-left-shift-unique).
- `WeilConjectures.IntegralSystemRealization.integralTensorRightShift_ext`
  (lem-pur-integral-tensor-right-shift-ext).

`WeilConjectures.IntegralSystemRealization.integralTensorRightShift_existsUnique`
is proved from the existing finite-tower and normalized-descent helpers and the new
uniqueness theorem. Its existence argument is fully written in Lean and removes the
unused invertibility hypothesis of the existing public right-shift existence theorem.
Only proof-private `import all` access is used; the dependency module is not edited.

The delivery has six holes in total, net three added. The final packet is compiled and
checked by deliver3.py before its push. None is in a definition.
Each new holed theorem fixes one W, one integer shift and one tensor slot, rather than
restating the record theorem. Checks of the statements include r=0 (identity formulas),
negative shifts (integer parity), zero complexes and the empty scheme (zero maps).
No geometric invertibility hypothesis is needed for these algebraic tensor-shift formulas.

## No longer needed

None of the original public imports, nodes or modules is pruned. The original node had
no proof dependencies to remove. The extracted definition module uses only the expression
domain and completed-tensor API; the four extra original imports are not needed there.
All dependencies required by the unchanged expression and Roos declarations stay in the parent.

## Where the brief, the DAG or earlier work was wrong

The definition node had an empty proof plan despite owning three remaining theorem holes.
Its tensor hole combines four distinct constructions and four uniqueness arguments.
The new nodes make those arguments separate proof items, while the parent now contains
an actual assembling proof. No mathematical statement or unit route is changed.

The existing `integralCompletedTensorShiftRight` has an additional ell-invertibility
instance, but its finite-tower and descent helpers do not use that hypothesis.
The new proved right-slot theorem reuses those helpers for arbitrary W, and delegates
only the separate equality of two normalized comparisons to a new theorem.

## New nodes

`def-pur-integral-tensor-shift-properties` owns the nine relocated definitions with
identical signatures and bodies. It is an interface extraction, not a new mathematical notion.

`lem-pur-system-tensor-left-shift-unique` is the unsigned first-factor totalization and
its uniquely normalized K-flat descent on one strict-system site.

`lem-pur-system-tensor-right-shift-unique` is the signed second-factor totalization and
its uniquely normalized K-flat descent on one strict-system site.

`lem-pur-integral-tensor-left-shift-unique` is the unsigned finite tower, fixed product/cone
comparison and uniquely normalized completed first-factor descent.

`lem-pur-integral-tensor-right-shift-unique` is proved by the existing signed finite-tower
and fixed product/cone descent helpers together with the new equality theorem.

`lem-pur-integral-tensor-right-shift-ext` states only equality of two already supplied
normalized completed right-slot comparisons, using generator and cone uniqueness and
good-model resolution density. It contains no existence assertion.

Change record: coord/changes/A9-integral-tensor-shift-properties.md.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
