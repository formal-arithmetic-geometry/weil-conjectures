## What changed

Replaced the hole in `native_exceptional_ordinary_counit_graded` by an explicit proof,
without changing its statement. The proof constructs the ordinary adjunction from
`ConstructibleExceptionalCoefficients.exists_coefficient_construction`, the locally
finite compact-support realization, the stage adjunction, and the native geometric
Brown comparison. Private categorical lemmas prove the shifted counit bijection and
transport it through full-subcategory shift comparisons.

The proof then uses two separate geometric components: native realization of an
invariant transpose and a cone criterion for ordinary invertibility. It proves the
intervening kernel-reflection calculation from the given carrier equation, native
comparison naturality, scalar adjunction, and full faithfulness of realization.
`NativeExceptionalOrdinaryMateLift` adds three literal aliases for the ordinary
constructible restriction and a named lift theorem. `NativeOrdinaryConeDetection`
states the independent cone criterion. Both new statements have sources, full
proofs in words, edge-case checks and DAG nodes. All added imports in the item are
proof-only. No other existing module or public interface was changed.

Verification: both new modules compiled (12.0 s and 7.2 s), and the complete
item proof compiled in 54.5 s. Removed its sole unused-tactic warning before
the delivery tool's final compile and preflight.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.NativeExceptionalForgetful.native_exceptional_ordinary_counit_graded`.
The item module has zero remaining holes. Its three private lemmas
`ordinary_adjunction`, `shifted_counit_bijective`, and `ordinary_graded_bijective`
are proved, as is the native counit kernel-reflection calculation.

Added exactly two holes, each in its own module:

- `WeilConjectures.NativeExceptionalForgetful.native_exceptional_ordinary_mate_lift`
  (`lem-sf-native-exceptional-ordinary-mate-lift`). This constructs a native object
  and native lift of an invariant ordinary transpose. It assumes neither the
  comparison `a`, the image identification `e`, nor the carrier equation `ht`, and
  asserts no invertibility or graded bijection.
- `WeilConjectures.NativeExceptionalForgetful.native_ordinary_cone_detection`
  (`lem-sf-native-ordinary-cone-detection`). This is a criterion for a native
  morphism, with no exceptional functor, adjunction, carrier, or graded Hom data.
  Its argument is rotation of the cone triangle followed by finite-dimensional
  stalks of cohomology.

This is a decomposition: one original hole closed and two smaller holes added,
net minus one in this delivery, not a completed proof of the geometric obligation.
There are no holes in definitions, instances, private declarations, or proof glue.

## No longer needed

No existing import was removed and no module is withdrawn or claimed pruned.
The scalar Frobenius counit and constructible realization remain needed by the
native-lift and cone steps; they are not pruned. The parent node's direct proof
route is updated to the dependencies actually used by the new proof.

## Where the brief, the DAG or earlier work was wrong

The former one-step plan suppresses a distinction: the supplied comparison `a` is
natural on native Weil morphisms, while the conclusion tests every ordinary
morphism in every degree. Naturality on arbitrary ordinary maps cannot simply be
assumed. The new proof uses naturality only on native maps in the kernel test,
and obtains ordinary invertibility through a native cone and constructible
finiteness. It never assumes that native derived forgetting is faithful, nor
that global ordinary Hom groups are finite dimensional.

The original statement and the unit route are retained. Zero objects, empty
schemes, and identity morphisms are covered by both component arguments.

## New nodes

`lem-sf-native-exceptional-ordinary-mate-lift` records right Frobenius realization,
ordinary right-adjoint uniqueness, and the degree-zero cyclic-Hom lift. Its module
is `Sheaf.WeilSheaf.NativeExceptionalOrdinaryMateLift`.

`lem-sf-native-ordinary-cone-detection` records the cone and finite-stalk argument.
Its module is `Sheaf.WeilSheaf.NativeOrdinaryConeDetection`.

No definition or statement of an existing module was changed, so no change record
or forced consumer adaptation is required.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitGraded": "d0ab950ff0ec31c68b5574fcf2aba41eeda69323", "Sheaf.WeilSheaf.NativeExceptionalOrdinaryMateLift": "b6efadf34c8aa184539e049b4bbd3c39b48052f4", "Sheaf.WeilSheaf.NativeOrdinaryConeDetection": "fc2a683a3451c2f26a31d10d954cc33634792349"}, "results": {"Sheaf.WeilSheaf.NativeExceptionalOrdinaryCounitWitness": {"hash": "0e4c52d3e1311304c4ad0b61faf22e3ef3dbbb90", "status": "OK"}}, "seconds": 31, "time": "2026-10-28T10:40:08+0800", "transitive": 0, "version": 1}
```

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
