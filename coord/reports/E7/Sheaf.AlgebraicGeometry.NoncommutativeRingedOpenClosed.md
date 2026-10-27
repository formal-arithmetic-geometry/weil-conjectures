## What changed

Proved `AlgebraicGeometry.ProEtale.noncommutative_ringSheaf_open_closed` with its full
statement unchanged: arbitrary schemes, arbitrary noncommutative monoid objects,
all canonical maps, and all coefficient-transport assertions. Both public definitions
and all public imports are unchanged. Added only proved private helpers.

The geometric argument reuses the proved abelian closed-support and closed-counit
interfaces. It lifts zero detection and isomorphism reflection through forgetting,
checks the actual localization short complex after the two exact restrictions, and
then deduces exactness of closed direct image by killing its cokernels. This is the
argument already present in `ProEtaleRingSheafClosedLocalization`, generalized here
without its unused ambient qcqs assumptions. The original module is unchanged.

A generic private transport lemma preserves the entire assertion bundle through
additive equivalences on the two coefficient categories. An explicit isomorphism
of composable-arrow diagrams preserves the localization sequence with its actual
maps. Four private lemmas calculate the identity carriers of the scalar-equivalence
unit, counit and inverses. The formulas for composition of adjunctions then prove
all six transported normalization equations.

Read Stacks proetale.tex Tags 09AA, 09BM, 09BN and 09AH, the latest blueprint unit
`sk-lem-formal-closed-support`, all declarations in the assigned module, and the
existing exactness/adjunction/module-object interfaces. Ran LeanFinder, Loogle and
grep through msearch, and searched the source library and Mathlib locally. The
unit's underived localization step is preserved. Checked the empty-open and empty-closed
cases, the zero coefficient ring and matrix rings: the proof uses only additive
module-object structure and exact complementary restrictions, so none of these
cases requires an extra hypothesis or commutativity.

Validation: the complete delivered module compiled cleanly through lcompile.py
in 31.0 seconds, without warnings. A textual interface comparison confirmed the
original theorem signature and both definitions are unchanged. The DAG's proof
uses equal its proof_deps, and no theorem hole remains in the source.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.ProEtale.noncommutative_ringSheaf_open_closed`
(node `lem-sfb-noncommutative-ringed-open-closed`).

Holes added: zero. Holes left in the delivered module: zero. No split-off statement.
The scalar equivalence and assertion-bundle definitions retain their original bodies.

## No longer needed

The route does not need the integer-coefficient comparison with sectionwise ringed
modules from `lem-weil-pbc-proetale-ringed-open-closed`; its import
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed` is removed. It uses the direct
abelian closed-support and closed-counit declarations instead.

The separate module kernel and cokernel action lemmas
`lem-sfb-modobj-kernels` and `lem-sfb-modobj-cokernels` are unnecessary here because
the adopted module-object library already provides exact conservative forgetting.
Their imports `Sheaf.CategoryTheory.ModuleObjects.KernelStructure` and
`Sheaf.CategoryTheory.ModuleObjectCokernelAction` are removed.

The general lifting theorem `det-prop-sfb-module-pullback-exact-lifted` is unnecessary
because mapMod and mapModLeft already have the required exactness instances.
Removed its unused import `Sheaf.CategoryTheory.ModuleObjects.LiftExact`.
The abstract-isomorphism-to-unit/counit lemma
`lem-sfb-adjunction-abstract-iso-unit-counit` is unnecessary because the actual
counit and unit normalization is available directly, including the existing open
counit instance. No module is withdrawn. Removed the obsolete top-level tool-use
approvals for the commutative ringed theorem and the general exact-lifting theorem.

Additional redundant proof imports removed:
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`,
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`,
and `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Projection`.
Their relevant canonical constructions and instances remain available through the
unchanged public imports; no claim is made that those definitions become unused.

Removed redundant direct proof edges to `def-sfb-finite-extension-by-zero`,
`def-sfb-finite-lower-star-lax-monoidal`, `def-sfb-finite-upper-star`,
`def-sfb-finite-upper-star-monoidal`, and `def-weil-proetale-inverse-image`:
the canonical operations and the exactness/adjunction declarations already carry
these constructions. They remain needed transitively; this delivery does not
withdraw their modules or their existing statement dependencies.

## Where the brief, the DAG or earlier work was wrong

The planned passage through integer module sheaves is unnecessary: the library has
proved abelian closed-support/counit statements on arbitrary schemes. The existing
qcqs ring-sheaf localization proof uses neither ambient qcqs assumption; its proof
can be used without changing its public declaration. The assertion-bundle and
coefficient-equivalence definitions are sound, and the full stated result remains
unchanged. Existing docstrings are retained; the updated DAG records the shorter
implemented route.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
