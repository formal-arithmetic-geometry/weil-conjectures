## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.exists_integralBrownAdjoint`
in `Sheaf.SixFunctors.IntegralBrownAdjoint`, with its signature and all existing definitions
unchanged. Establish qcqs for X and Y from the structure morphisms, obtain the integral
localizing-closure equalities from `localizingClosure_ctf_equals_bc`, and specialize
`exists_localizingExceptionalAdjoint` at the same coefficient and boundary compactification.
Package its exact adjoint data as a proposition parametrized by the two object properties,
then transport that proposition along the two equalities. This retains the actual shift
structure and triangulatedness proof supplied by the general theorem.

The proved private helper `ambientCounitComparison` handles the final comparison clause for
arbitrary equal full subcategories. After equality induction it whiskers Mathlib's
`Adjunction.rightAdjointUniq` with the ambient inclusion. Its counit equation is the image
of `rightAdjointUniq_hom_app_counit`; uniqueness follows from injectivity of the inverse
adjunction Hom equivalence, component by component, and natural-transformation/iso extensionality.
It imposes no triangulated-category hypotheses and does not choose any new data from existence.

The five recorded proof steps and the unit's specialization route are followed. No dependency
statement, target, public signature, definition, or other module is changed.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.exists_integralBrownAdjoint`
(node `det-prop-int-brown-adjoint`). Proved private helper `ambientCounitComparison` as well.
There are zero remaining holes in the item and zero added holes or split-offs. This is a proof
from the existing declared dependencies, including the still-open general existence and
integral closure-equality theorems; it does not claim to close those dependency holes.

## No longer needed

Removed redundant private imports `Mathlib.AlgebraicGeometry.AffineScheme`,
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Mathlib.AlgebraicGeometry.Morphisms.Separated`, and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: the public dependency modules already
export their required declarations and instances. Also removed redundant private imports
`Sheaf.Paper.LocalizingAdmissibleCoefficients`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`, which the current
repository has added since the earlier sandbox attempt: they are already publicly exported
by the retained statement dependencies. These removals prune redundant import edges, not
dependency modules. Retained the explicit `Sheaf.Compactification.BoundaryRefinement` import
to preserve the unit route, although it is also publicly exported by a statement dependency.
No DAG nodes or modules bypassed, and no unit-level route changed.
The integral construction module supplies the exact ambient functor and Loc(Dbc) definition;
its separate preservation theorem is not reapplied because the general existence theorem
already supplies preservation of that same composite on Loc(Dctf).

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. Direct rewriting of the unfolded assertion is obstructed
by dependent triangulated and shift instances. A local proposition parametrized by object
properties makes the equality transport explicit and avoids modifying any definitions.

No new nodes, changes to statements or definitions, or forced consumer adaptations.

Retained work rechecked against the current sources on 2026-10-19. The required
`deliver3.py --no-push` compiled the delivery and passed preflight with review class AUTO.
A concurrent standalone `lcompile.py` request received no server response within 186 seconds
(exit 124, not compiled); the successful delivery preflight supplies the compilation check.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
