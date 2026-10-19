## What changed

Proved `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_fieldExtension` with its
original signature and public imports unchanged. Constructed the compatible fields
M = perfectClosure L (AlgebraicClosure L) and P = perfectClosure K M using Mathlib.
Perfectness of P gives separability of M/P, including transcendental extensions.
The exact-functor homology isomorphism and `upperStarCompSheafFiberIso` transport the
stalkwise torsion condition to P. Pullback cancellation supplies qcqs of g_P.
The separable result and the purely inseparable comparison then prove the specified
canonical exchange invertible.

Added two fully proved modules. `Sheaf.AlgebraicGeometry.SeparableFieldExtensionExchange`
constructs the smooth-subalgebra inverse system over S and its limit using Over.pullback
and preservation of connected limits by Over.forget. It applies the existing smooth
inverse-limit base-change theorem without assuming that S is quasi-compact.
`Sheaf.AlgebraicGeometry.FieldExtensionPerfectComparison` constructs the comparison maps
by pullback.lift, proves their naturality and Cartesian property, identifies exchange
with the derived mate, and uses horizontal pasting and reflection of isomorphisms to
compare the two compatible field extensions.

Updated both original DAG attachments and added one node for each new theorem.
No existing definition, statement, visibility or public import changed. No consumer
adaptations or change records are required.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_fieldExtension`
(nodes `lem-kun-0f1c-exchange` and `lem-kun-0f1c`).

Also proved, with zero holes:

- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_separableFieldExtension`
  (node `lem-kun-separable-exchange`).
- `AlgebraicGeometry.Etale.isIso_fieldExtension_iff_of_purelyInseparable`
  (node `lem-kun-purely-inseparable-exchange-comparison`).

All private helpers are proved. No sorry remains in any delivered module.
Actual delivery counts: original module 1 -> 0; new modules 0. Closed 1, added 0,
net 1. The proofs use the existing named smooth-subalgebra, smooth-limit exchange and
mate declarations; their upstream proof obligations remain with their own modules.

## No longer needed

Removed these private proof imports from the original module:

- `Sheaf.AlgebraicGeometry.GeometricStalkAsPullback`
- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`
- `Sheaf.AlgebraicGeometry.GeometricStalkCohomology`
- `Sheaf.FieldTheory.SeparableSmoothColimit`
- `Sheaf.AlgebraicGeometry.SmoothBaseChangeLimit`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `Mathlib.FieldTheory.PurelyInseparable.Basic`
- `Sheaf.FieldTheory.SeparableExtension`
- `Sheaf.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange`
- `Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`
- `Sheaf.CategoryTheory.MateIsoAlongEquivalences`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`
- `Sheaf.Paper.KunBaseChange`

The direct declarations `lem-kun-stalk-as-pullback`,
`lem-weil-pbc-derived-inverse-image-composition`, and `lem-kun-stalks-of-cohomology`
are unnecessary: exact homology followed by `upperStarCompSheafFiberIso` gives the
required stalk isomorphism. Their modules are absent from the proof imports.
The smooth-subalgebra and smooth-limit declarations remain used in the new separable
module. The universal-homeomorphism, mate and pasting ingredients remain used in the
proved comparison, through the source library rather than retired wrapper modules.
`Sheaf.Paper.KunBaseChange` is replaced by the source library's explicit horizontal
pasting formula. No original module is withdrawn, and no whole-library reachability
pruning is asserted.

The original nodes remove these obsolete direct tool approvals where present:
`lem-weil-pbc-derived-inverse-image-composition`, `lem-pc-proper-base-change`,
`lem-pc-homeo-pure-insep`, `thm-weil-pbc-universal-homeomorphism-invariance`,
`lem-weil-mate-iso-along-equivalences`, `prop-weil-pbc-derived-inverse-image-adjunction`,
`prop-weil-pbc-inverse-image-exact`, `lem-weil-pbc-exchange-identity-pasting`,
`lem-weil-pbc-derived-exchange-termwise`, `lem-weil-pbc-dplus-injective-representative`,
and `lem-weil-pbc-inverse-image-stalk-germ`.
The corresponding generic support, when needed, stays below the new nodes.

## Where the brief, the DAG or earlier work was wrong

This continuation retained the earlier attempt's three completed Lean proofs and
checked them against the current sources. The required initial dry run passed
compilation and preflight. Its comparison-module axiom probe received no answer
from the busy server; delivery retries the checks. No proof was replaced merely
to rebase it, and the original module's signature and public imports are preserved.

No mathematical statement error was found. The blueprint route is preserved:
separable smooth-limit exchange and reduction through compatible perfect closures.
The new comparison has no qcqs or coefficient hypothesis. Its identity-tower,
characteristic-zero, empty-scheme and zero-complex cases require no special handling.
The separable construction handles arbitrary S and possibly transcendental L/K.
The original stalk-germ dependency was replaced by `lemma-openclosed-stalk-upperstar`,
whose actual declaration is the natural stalk isomorphism used by the Lean proof.

## New nodes

`lem-kun-separable-exchange`: the fully proved separable special case in
`lean/Sheaf/AlgebraicGeometry/SeparableFieldExtensionExchange.lean`, reusing the
smooth-subalgebra colimit and smooth inverse-limit exchange declarations.

`lem-kun-purely-inseparable-exchange-comparison`: the fully proved, coefficient-free
comparison of invertibility in compatible purely inseparable towers in
`lean/Sheaf/AlgebraicGeometry/FieldExtensionPerfectComparison.lean`. The proof gives
actual pullback maps, the mate calculation, horizontal pasting and cancellation.
No unresolved split-offs, change records, forced adaptations or module deletions.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
