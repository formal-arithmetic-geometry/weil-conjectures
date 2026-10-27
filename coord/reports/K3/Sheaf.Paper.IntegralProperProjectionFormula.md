## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.integralProperProjectionFormula`
in `Sheaf.Paper.IntegralProperProjectionFormula`, preserving its complete signature,
public imports, ordinary uncompleted tensor, and specified canonical projection map.
The bounded assertion reuses `projection_bounded` from the existing implementation
`Sheaf.PoincareDuality.ProperProjectionFormulaBounded`. The integral constructibility
comparison identifies its generators with the stated constant-model generators.

Private proved helpers compare the two coproduct-universe conventions, transport
cofan preservation to preservation of discrete colimits, and extend tensor closure
by two applications of localizing minimality. A uniform geometric fibre-dimension
bound permits applying `integralProperDirectSums`. The existing
`isIso_projectionMap_of_localizingBoundedConstructible` then extends the bounded
canonical formula in both variables, using `integralTensorInverseImage` for the
bounded pullback and tensor hypotheses. Its canonical map is definitionally the
map in this item. The node's proof and dependency list record this route.

The support comparison also covers zero objects and empty coproducts: omitted zero
summands admit unique maps, and the retained nonzero summands have distinct
coordinate idempotents in the endomorphism set of the coproduct vertex.
No adopted source module, existing data construction, or other item is changed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.integralProperProjectionFormula`
(node `det-thm-sf-pf-adic-projection`). Its three conjuncts are proved.
Holes added: zero. Split-off statements: zero. Remaining holes in the delivered
module: zero. Existing holes in imported named dependencies remain their own items;
this delivery makes no claim to have proved them.

The bounded-formula/tensor argument and the direct-sum/closure comparison were
checked separately during development. Private conversion lemmas keep the canonical
projection-map wrappers folded at call sites; explicit tensor conversions avoid
expensive reduction during elaboration. No compiler limit is increased. The delivery
tool runs the final combined module, declaration, dependency, and independent-reader
checks.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Paper.RingedProjectionFirstShift`
- `Sheaf.Algebra.Homology.KFlat`
- `Mathlib.CategoryTheory.Triangulated.Adjunction`
- `Mathlib.CategoryTheory.Shift.Adjunction`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Sheaf.Paper.IntegralProperBaseChange`
- `Sheaf.Paper.LocalizingClosureCtfEqualsBc`
- `Sheaf.Paper.ModuleRingedToposDerivedComparison`
- `Sheaf.Paper.UnboundedLocalizingPullback`
- `Sheaf.SixFunctors.ProperImageLocalizingProper`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

`IntegralTensorInverseImage` and `LocalizingClosureExistence` remain used.
The proof adds the existing constructibility comparison, bounded projection formula,
fibre-dimension bound, field base-change dimension result, integral proper direct sums,
and formal localizing determination implementations.

The old direct dependencies no longer needed by this proof are
`lem-weil-pbc-qcqs-over-affine`, `det-def-localizing-closure-ctf-equals-bc`,
`def-pc-tensor-complex-sheaves`, `def-pc-kflat-complex`, `def-weil-abstract-derived-category`,
`det-proper-base-change-unbounded-pullback`, `det-proper-image-localizing-proper`,
`lem-pd-module-ringed-topos-derived-comparison`,
`lem-weil-pbc-adjunction-shift-compatibility-unique`, `lem-sf-triangulated-right-adjoint`,
`lem-weil-pbc-ringed-projection-mate-exact`, and `lem-sfb-ringed-projection-first-shift`.
The bounded formula is obtained through the existing condensed bounded implementation
rather than by directly applying `det-thm-sfb-proper-base-change-integral` here.
The unchanged statement still mentions the exact projection mate node.
The adopted implementation supplies the exactness and shifts already proved there.

Removed the corresponding obsolete top-level approvals, and the unused
`lem-weil-pbc-sheaf-tensor-closed` approval, preserving the order of retained approvals.
These are direct-route pruning statements, not withdrawals: transitive imports and
other consumers can still require these modules. No module is withdrawn, no adopted
declaration is removed, and no whole-library module-pruning count is claimed.

## Where the brief, the DAG or earlier work was wrong

The library already implements the formal two-variable extension for this actual
module-object projection map. Repeating its ringed-topos transport in this item would
duplicate that argument. The integral coefficient-specific direct-sum hypotheses can
be supplied directly by `integralProperDirectSums`, with the existing finite-type
fibre-dimension bound, instead of using the larger proper-image interface.

The two localizing closure definitions have different index-universe conventions.
They cannot simply be rewritten as definitionally equal: the proof includes the
nonzero-support argument and the converse index-lifting argument. The constant-model
and adopted bounded predicates also require their existing comparison theorem.
The previously quarantined item is preserved with its Lean attachment; no archive is
withdrawn or replaced by an empty module. No new nodes or change records are needed.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
