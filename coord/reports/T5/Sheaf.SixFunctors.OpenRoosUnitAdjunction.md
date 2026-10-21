## What changed

Replaced the proof hole in `WeilConjectures.OpenRoos.openRoosUnitAdjunction` by a complete
Lean assembly from three separate comparison results. The original theorem statement,
public imports and all seven existing definitions are unchanged. Added proved private
helpers for the adic coefficient datum, coefficient exactness, normalized finite-map
invertibility, completed-map invertibility, finite quotient-transition compatibility, the actual-unit completeness criterion, and the ordinary and derived
open adjunction units. The complete-subcategory adjunction is constructed by restricting
the specified adjunction; its unit and counit identities and full faithfulness are proved.
The restriction comparison is proved unique using the reflector Hom bijection.

Added three modules with one public proof obligation each: `IntegralRoosReflector`,
`OpenRoosCoefficientOperations`, and `OpenRoosFunctorTransport`. Their statements isolate
steps 3, 4, and 5–7 of the existing plan, without the geometric/coefficient facts,
completeness-preservation arguments, uniqueness, or adjunction conclusions proved here.
The finite-map and completed-map invertibility and quotient-transition calculations are
proved in the parent, rather than included in the coefficient obligation. Site and coefficient universes remain independent.

Private proof imports added to the parent are the three new modules,
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`,
`Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`, and
`Mathlib.GroupTheory.OrderOfElement`. The existing K-flat resolution import is used
explicitly. A command-only change record documents the private helper scopes and extra universes;
no existing statement or definition is repaired, and there are no forced
consumer adaptations. The new results' statements were checked for the identity and empty
open, unbounded complexes, arbitrary representatives, and independent coefficient size.
All four files compiled together after import cleanup (5.1 s, 6.2 s, 21.8 s and 39.5 s).
The additional completed-map calculation then compiled independently (9.2 s). Final
integrated compilation, axiom checks and preflight are performed by the delivery command.

## Proved and sorry left

Closed the original hole in `WeilConjectures.OpenRoos.openRoosUnitAdjunction` (1 of 1);
its proof and every private helper contain no `sorry`.

Added exactly three holes:

- `WeilConjectures.integralRoosReflector`, node `lem-sf-integral-roos-reflector`:
  the actual quotient reflector, including independence of arbitrary representatives.
- `WeilConjectures.openRoosCoefficientOperations`, node
  `lem-sf-open-roos-coefficient-operations`: construction of normalized coefficient and
  strict-system operations.
- `WeilConjectures.openRoosFunctorTransport`, node `lem-sf-open-roos-functor-transport`:
  the two strict completion comparisons, their actual-unit equations, and the normalized
  pulled Roos comparison.

This is a decomposition, not a net proof of the target closure: one original hole is
closed and three separate holes are added. It does not claim a decrease of the sorry
ledger. Each remaining theorem is a genuine subargument of the original plan and has a
source, full proof in words, Lean signature and matching DAG node. In particular none
repeats the original statement or assumes its conclusion. Previously existing holes in
imported library results are not changed.

## No longer needed

Removed these explicit private proof imports from the item:

- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.Paper.WeilCompletedTensorReflector`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Sheaf.Paper.CompletedKoszulQuotientComparison`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.ExactProductFunctorStrictLimit`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts`
- `Sheaf.SixFunctors.OpenSemilinearTensorModel`
- `Sheaf.SixFunctors.OpenTensorNormalization`

These generic results remain dependencies of the three subarguments or remain reachable
through unchanged public imports. The slice-equivalence definitions are still used by
the direct finite-map calculation. No module or DAG node is withdrawn, and no whole
module is claimed pruned from the targets' closure. The last normalization theorem is
unnecessary for the new adjunction proof: the parent proves the required unit property
from the direct-sum localized extension itself, at independent universes. Its module is
still a public dependency of the unchanged Operations interface. The original unit route
is retained; only the proof obligations below this item have been separated.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically appropriate, but several of its reflector
interfaces are specialized to the site-sized coefficient universe. They cannot simply be
applied when E has an independent universe. The reflector subargument therefore states
the necessary small-model transport explicitly. The existing five-way equivalence already
proves the Roos predicate iff the actual unit is invertible after choosing a good
representative; the parent now uses that result directly. Its arbitrary-representative
intrinsic condition still needs the reflector comparison.

The plan also needs simultaneous normalized coefficient transport and both strict Roos
coordinates, rather than an unspecified abstract equivalence. Those requirements remain
explicit in the two open comparison obligations. No statement is marked disputed and no
statement is weakened. The three new obligations use no completeness assumptions.

## New nodes

`lem-sf-integral-roos-reflector`, in `Sheaf.SixFunctors.IntegralRoosReflector`, records the
normalized quotient reflector subargument of original step 4. Its output includes the
Hom bijection needed for the parent's uniqueness proof, but no open-functor assertion.

`lem-sf-open-roos-coefficient-operations`, in
`Sheaf.SixFunctors.OpenRoosCoefficientOperations`, records original step 3 and the
coefficient/system transport needed in step 7. Finite and completed coefficient invertibility and quotient-transition compatibility are
proved separately in the parent from the retained normalization, system-naturality and
projection fields. The completed-map proof uses preservation of the defining coefficient
limit by evaluation and uniqueness of limit cones.

`lem-sf-open-roos-functor-transport`, in `Sheaf.SixFunctors.OpenRoosFunctorTransport`, records
strict tensor-tower/limit transport from steps 5–7. It supplies neither completeness
preservation nor uniqueness nor any assertion about the restricted adjunction.

The existing item's node now describes the actual Lean assembly. The command-only change record is
`coord/changes/open-roos-proof-local-commands.md`: it documents the added universes and
scoped helper commands required by preflight. All existing public declaration signatures
and definition bodies are unchanged.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
