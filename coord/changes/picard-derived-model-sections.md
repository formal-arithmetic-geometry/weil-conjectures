# AlgebraicGeometry.Scheme.picardDerivedModelSections

## Reason

The scalar cycle argument and the arbitrary-base-change direct-image argument need a common
concrete interface. Derived Hom from the pulled-back structure sheaf supplies it without
choosing data from an arbitrary unproved existence theorem.

## Old

These declarations and their modules did not exist. Every existing signature, definition,
visibility and public import is unchanged.

## New

New public declarations in `Sheaf.AlgebraicGeometry.PicardDerivedModelSections`:
`picardDerivedModelSections` is the derived Hom type
`Hom(Lt*(O_W[0]), Lt*E)`;
`picardDerivedModelRestriction` sends ξ to `c.inv ≫ Li*(ξ) ≫ c.hom`, with c the pinned
canonical derived composition comparison followed by transport along the supplied equality;
`picardResidueLift` is Mathlib's open immersion lift of the residue point;
`picardResidueLift_comp` proves its composite is the original residue map.

New public theorems `picard_scalar_derived_cycles` and `picard_direct_image_test_sections`
state the independent model and geometric comparison parts in their respective new modules.
Their full unchanged signatures are recorded in their new DAG nodes and Lean modules.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | S2 | Proof composes the new comparisons; signature unchanged. |
| Sheaf.AlgebraicGeometry.PicardScalarDerivedCycles | S2, new | Uses the explicit derived Hom and restriction interface in its statement. |
| Sheaf.AlgebraicGeometry.PicardDirectImageTestSections | S2, new | Uses the explicit derived Hom and restriction interface in its statement. |

There are no existing users of the new declarations. No forced adaptations are included.

## Status

landed 20261013T072405-L-1124760 2026-10-13 (merge of deliver/S2/Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization)
