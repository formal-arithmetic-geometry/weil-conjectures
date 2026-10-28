## What changed

Corrected the composite-shift interface of
`etaleHomComparison_reversedExact_commShift_core` and
`etaleHomComparison_reversedExact_commShift`: both now receive the hPhi and hPsi
component equations already supplied by shiftData. The existing exactness theorem
passes those equations; its signature and every target signature are unchanged.
All changes are under Sheaf. No source-library declaration or definition changes.

The core is proved (reviewer's fix): unfold `NatTrans.CommShiftCore` to components,
rewrite the two composite-shift components by hPhi and hPsi, and apply the new
fixed-degree component lemma `etaleHomComparison_reversedExact_commShift_component`.
The categorical diagram chase (tensor–Hom transposition, naturality of tensor
cancellation, the transpose equation, scalar tensor shift cancellation, hA) is the
proof in words of that component lemma; it is not yet written in Lean. No private
lemma is delivered.

The remaining model calculation is stated separately in
`Sheaf.SixFunctors.EtaleScalarTensorShiftCancellation`. It involves tensor products,
scalar shifts and scalar balancing only; it has no internal Hom, no v, and no Hom
shift-normalization assumption. It is a strict part of the original argument,
not a renamed version of the original obligation.

Change record: `coord/changes/etale-hom-composite-shift-normalization-C8.md`.

## Proved and sorry left

Proved: `AlgebraicGeometry.Etale.etaleHomComparison_reversedExact_commShift_core`
(corrected statement), from the component lemma, hPhi and hPsi; axioms
propext, Classical.choice, Quot.sound and sorryAx (through the component lemma).
The kernel check of this proof takes about 35 s (definitional unfolding of the
opposite shift and of `EtaleHomRight` in the final `exact`); the file compiles in
about 37-48 s.

Two holes are left, each in its own module with its node:
- `AlgebraicGeometry.Etale.etaleHomComparison_reversedExact_commShift_component`
  (module `Sheaf.SixFunctors.EtaleHomTransposeExactCommShiftComponent`, node
  `lem-coef-etale-hom-transpose-exact-comm-shift-component`): the degree-n shift
  square of v at K for the normalized composite shifts. It carries the diagram
  chase; it is the core without the `CommShiftCore` wrapper and the composite
  shift structures, not a strictly smaller mathematical statement.
- `AlgebraicGeometry.Etale.etaleHomTensorComparison_shiftCancellation`
  (module `Sheaf.SixFunctors.EtaleScalarTensorShiftCancellation`, node
  `lem-coef-etale-scalar-tensor-shift-cancellation`), used by the component's proof.

The old arbitrary-structure signature was false; this is an explicit interface
correction, not a claimed proof of that signature.

## No longer needed

Removed the unused public import of
`Sheaf.SixFunctors.EtaleHomTransposeExactShiftData` from the core and the all-degree
module. No module or DAG node is withdrawn. The shift-data construction remains required
by the final exactness theorem. The original tensor-model comparison dependency
is retained for the normalized binary comparison and its naturality. The unit
statement and route are unchanged.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old signatures, repaired here): normalization of sA and sB
does not normalize arbitrary chiPhi and chiPsi. The missing equations were already
present in shiftData and in the intended final exactness predicate, but were
omitted when the shift-compatibility obligation was split. The sign-character
twist described in the change record shows why those equations are necessary.
Both affected nodes carry explicit statement-change records and account for all
DAG citers. The final exactness theorem already had the needed data, so its
mathematical statement is unchanged.

## New nodes

`lem-coef-etale-hom-transpose-exact-comm-shift-component` is the fixed-degree component split off from the core. It retains the exact component equation; its statement dependency is the tensor-model comparison node (owner of the definitions it uses) and its proof dependencies are that node and the scalar/tensor cancellation node.


`lem-coef-etale-scalar-tensor-shift-cancellation` isolates only the compatibility
of canonical scalar tensor balancing with cancellation of shifts -n,n. Its proof
uses flat-term K-flat representatives, termwise scalar extension, and localization.
The cases n=0 and a zero tensor factor reduce to the identity and zero equations;
identity coefficient change gives the same cancellation on both sides. No
flatness of B over A is assumed. Three actual Mathlib searches and the full
blueprint search found no matching statement.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.EtaleHomTransposeExact": "17daff96f533eb8518450ec8a0fc7863cadb9db4", "Sheaf.SixFunctors.EtaleHomTransposeExactCommShift": "4a7c2fce1f4692ac0d28f48b0f6bfd97a973991e", "Sheaf.SixFunctors.EtaleHomTransposeExactCommShiftComponent": "5457800c1cf65c801d2d63c4a60ee645ec61dfdd", "Sheaf.SixFunctors.EtaleHomTransposeExactCommShiftCore": "87cfeddddc202557af48d1a4249acbeaf2397b74", "Sheaf.SixFunctors.EtaleScalarTensorShiftCancellation": "677f9694af012ba2fab85647e52355871488dad4"}, "results": {}, "time": "2026-10-28T12:17:32+0800", "transitive": 0, "version": 1}
```

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
