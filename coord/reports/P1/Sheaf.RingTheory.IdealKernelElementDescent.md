## What changed

Repair of reviewer X-6b9b3's return, points B2, C1 and 6.

Retained the launcher-authorized common-universe signature and complete tensor
proof of `RingTheory.exists_stage_ideal_kernel_element_vanishes` in
`Sheaf.RingTheory.IdealKernelElementDescent`.

Included the forced adaptation of `Sheaf.RingTheory.FiniteIdealKernelDescent`.
Its public theorem signature and visibility are unchanged. Its per-element
`hpoint` proof now assembles the existing finite-relation/tensor argument at the
original carrier universes instead of applying the now ill-typed common-universe
theorem. The later common-stage proof is unchanged. The proof-only import now
names `Sheaf.RingTheory.ColimitFlatRelationDescent` directly. The caller is marked
`STATEMENT-DISPUTED` because its independent-universe dependency remains disputed.

Included both existing DAG nodes. The item's `lean.statement` is copied verbatim
from the delivered declaration, with common universe `u`. Its existing finite-
relation proof route and dependencies already agree with its proof. The adapted
caller's first proof step and `proof_deps` now name finite-relation descent.
Neither node realizes a separate step in `dag/units/sk-thm-p1.json`.

Replaced the change record's prose Users section with the required table,
including the unclaimed adapted caller, and removed the incorrect assertion
that no caller edit is needed. The record is
`coord/changes/ideal-kernel-element-descent-universe.md`.

## Proved and sorry left

`RingTheory.exists_stage_ideal_kernel_element_vanishes` retains its complete
Lean proof. `RingTheory.exists_stage_finite_ideal_kernel_vanishes` also has a
complete Lean proof against the existing relation-factorization declaration.
Neither delivered module contains a `sorry`. No holes are added or split off.
This repair closes no new holes relative to the returned delivery or the local
repository baseline, where the item's theorem was already syntactically proved.

Both proofs still depend on the existing holed declaration
`RingTheory.exists_stage_flat_relation_factorization`
(node `lem-weil-pbc-colimit-flat-relation-descent`). This dependency is not
modified or newly stated here. In its independent-universe form it is already
`STATEMENT-DISPUTED`; the caller retains that mathematical limitation, which
cannot be resolved while preserving its required public signature. This is
compiler/interface repair, not a claim that the disputed theory is axiom-free.

## No longer needed

The item removes the unused proof-only import
`Mathlib.LinearAlgebra.TensorProduct.Finiteness`.
The caller replaces the proof-only import
`Sheaf.RingTheory.IdealKernelElementDescent` with
`Sheaf.RingTheory.ColimitFlatRelationDescent`: it no longer uses node
`lem-weil-pbc-ideal-kernel-element-descent` as a proof dependency.
No other old dependency is removed and no module file is deleted.

## Where the brief, the DAG or earlier work was wrong

B2: The previous delivery incorrectly claimed that the caller needed no edit.
It fails at its old line 112 because the delivered single-element theorem uses
universe `u` throughout, whereas the caller keeps `v`, `w`, and `z` independent.

C1: The previous change record had prose rather than the required Users table.

Point 6: The old delivered set omitted the updated item node. This sandbox
includes it and synchronizes its Lean statement exactly with the declaration.

The earlier second reading incorrectly approved the missing adaptation and
node synchronization. That review is superseded and removed; the next reader
must review this repaired set.

STATEMENT-DISPUTED: The caller's independent-universe signature still inherits
the unresolved elementwise-colimit issue of its existing finite-relation
dependency. The return explicitly requires keeping that signature unchanged.
The repair records this issue openly; it does not introduce a replacement
axiom, false intermediate statement, or changed target. Further correction of
the caller and relation interface remains necessary outside this repair.

## Forced adaptations

`Sheaf.RingTheory.FiniteIdealKernelDescent` is unclaimed in the current local
claims. Its original module compiles against the original shared dependency,
but failed against the delivered common-universe module at old line 112:

```text
error: Application type mismatch: The argument
  hs (↑k) k.property
has type
  Eq.{z + 1} ((TensorProduct.lift (LinearMap.lsmul ↑(A.obj i) ↑(N.obj i)
    ∘ₗ Submodule.subtype I)) ↑k) 0
but is expected to have type
  Eq.{u + 1}
    ((TensorProduct.lift (LinearMap.lsmul ↑(Functor.obj ?m.754 i)
      ↑(Functor.obj ?m.756 i) ∘ₗ Submodule.subtype ?m.774)) ?m.775) 0
```

Necessary changed lines in the delivered caller:

- Line 15: replace the proof-only import with finite-relation descent, whose
  independent-universe declaration is needed by the replacement proof.
- Lines 52–53: update the proof description to match the necessary replacement.
- Lines 65–67: mark the inherited independent-universe statement dispute explicitly.
- Lines 115–147: replace the failing two-line application inside `hpoint` with
  finite tensor expansion, relation factorization, construction by the existing
  private tensor-map helper and `hR`, and balancing/finite-sum cancellation.

The public theorem signature and visibility, private helper, and all proof
lines after `hpoint` are unchanged. This is the existing per-element argument
inlined solely where its common-universe public interface no longer fits.
Compilation and the delivery tool's counterfactual checks verify necessity.

## Second reading by P1

1. Compared both delivered modules against the repository versions. The element
   theorem's changed universe interface is the authorized change, and the finite
   caller changes only its forced proof, import, documentation, and explicit
   dispute marker; all public declarations otherwise match.
2. Compiled both modules with `lcompile.py --all`; neither file contains
   `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The
   proofs use only the existing disputed relation-factorization theorem and
   introduce no new hole or hollow definition.
3. The item proof expands a tensor, derives exactly the required finite
   relation, applies relation factorization, and proves cancellation by tensor
   balancing. The adapted caller repeats this argument at independent carrier
   universes because the common-universe interface cannot typecheck there.
   No split-off statement was added, and searches found no existing theorem
   duplicating either declaration.
4. The removed finiteness import is unused. The caller's direct relation import
   is proof-only and its dependency list now matches the actual route; the unit
   route and realized nodes remain unchanged.
5. The DAG Lean statements are synchronized verbatim with the declarations,
   and proof steps and dependencies name the relation-factorization route.

Changed in this reading: added this review record and retained the necessary
caller adaptation, synchronized item node, corrected proof-only imports, and
the required Users table in the change record. No mathematical statement was
weakened or strengthened beyond the authorized common-universe interface.

## Forced adaptations

### Sheaf.RingTheory.FiniteIdealKernelDescent
Original against changed dependencies failed:
```
/tmp/forced-adaptation-f4g3x999/lean/Sheaf/RingTheory/FiniteIdealKernelDescent.lean:112:36: error: Application type mismatch: The argument
  hs (↑k) k.property
has type
  Eq.{z + 1} ((TensorProduct.lift (LinearMap.lsmul ↑(A.obj i) ↑(N.obj i) ∘ₗ Submodule.subtype I)) ↑k) 0
but is expected to have type
  Eq.{u + 1}
    ((TensorProduct.lift (LinearMap.lsmul ↑(Functor.obj ?m.754 i) ↑(Functor.obj ?m.756 i) ∘ₗ Submodule.subtype ?m.774))
      ?m.775)
    0
in the application
  exists_stage_ideal_kernel_element_vanishes ?m.754 ?m.755 ?m.756 ?m.762 ?m.764 ?m.766 ?m.767 ?m.769 ?m.772 ?m.773 i
    ?m.774 ?m.775 (hs (↑k) k.property)

(with the modules compiled into /tmp/forced-adaptation-f4g3x999/.lbuild) [5.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
