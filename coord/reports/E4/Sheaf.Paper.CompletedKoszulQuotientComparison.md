## What changed

Proved `AlgebraicGeometry.Scheme.completedKoszulQuotientComparison` without changing
its statement, universes, coefficient objects, completion objects, or either specified
unit. The proof compares both completion presentations with one constant coefficient
completion, lifts the composite through the coefficient equivalence, and checks the
unit equation by naturality.

Added six proved comparison modules. `CompletedConstantCoefficientEquivalence`
constructs the scalar-preserving coefficient equivalence and the strict finite
quotient comparison, including quotient units and all transitions.
`CompletedKoszulConstantTransport` identifies the published Koszul fiber with
constant quotient completion by the existing ringed Koszul reflector and the
unit-preserving completed fiber/strict-limit comparison.
`ExactEquivalenceDerivedSquares` proves the compatible left- and right-derived
comparison squares from Mathlib's Kan-extension universal properties.
`CompletedQuotientUnitNormalization` calculates the actual unit and invertible
reduction counit on a native K-flat complex directly in the cochain-localized
presentation used by the comparison squares.
`ConstantCompletionUnitNormalization` extends the constant unit formula
from K-flat complexes to all complexes by naturality and a K-flat resolution.
`CompletedConstantPresentationTransport` combines these calculations, cancels the
invertible native K-flat reduction counit, and transports the resulting unit-preserving
comparison along a realization isomorphism.

The common-presentation record keeps both unit-compatible comparison families
together. The two explicit unit definitions keep their data irreducible behind
proved normalization and projection APIs. The derived comparison structure keeps its equivalences and
localization factors as fields. This prevents repeated unfolding of the large
completed-sheaf equivalence during kernel checking. The standard derived-category
structures are deliberately inlined with `letI`, since abstract local structures
make comparison with the published fixed structures expensive. Canonical bridges
between homotopy and cochain localization are explicit public constructions. The
normalization API performs the bridge calculation before the sheaf assembly step;
the generic unit API then compares its raw component equations without expanding
large complex isomorphisms in the concrete sheaf context. The generic unit API accepts
comparison component maps directly and forms their canonical isomorphisms inside
the generic proof, keeping the concrete sheaf equations in their stated form.
A proved generic completion-transport API combines the universal derived squares
and the normalized unit equations while leaving every ordinary and derived functor
abstract. The sheaf assembly supplies its K-flat resolving class and the already
proved normalization formulas. This avoids unfolding the tensor and limit functors
inside the comparison calculation.
The assembly uses the canonical native localization and the exact coefficient model
of the published constant completion. Its public comparison fields name that native
localization explicitly. This avoids converting between alternative presentations
of the same derived category during kernel checking.

All new data definitions are explicit constructions from the published functors,
adjunctions, canonical limits, and ringed-site equivalences. No existing definition,
source-library declaration, target statement, or other group's module was changed.
The item statement was compared verbatim with the shared source. The overlaid Lean
import graph has no cycle, and the DAG changes introduce no cycle.
The public unit and localization-bridge definitions were inspected to ensure
their bodies reference no private helper declarations.

Validation: all seven delivered modules compile cleanly through `lcompile.py`.
The assembly passed the official delivery axiom probe in 45.8 seconds; the
original theorem compiled in 3.9 seconds. The final delivery dry run additionally
compiles the complete packet and probes every delivered declaration.
The five public unit/bridge constructions have no direct private-helper dependency.
The original theorem signature is unchanged verbatim.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Scheme.completedKoszulQuotientComparison`
(node `lem-weil-pbc-completed-koszul-quotient-comparison`).

Added zero holes. No `sorry` remains in any delivered module. In particular, all six
new public helper theorems and all their private helpers are proved in this delivery:

- `AlgebraicGeometry.Scheme.completed_constant_coefficient_equivalence`;
- `AlgebraicGeometry.Scheme.completed_koszul_constant_transport`;
- `CategoryTheory.exactEquivalenceDerivedSquares`;
- `AlgebraicGeometry.Scheme.completedQuotientUnitNormalization`;
- `CategoryTheory.ConstantCompletion.constantCompletionUnit_normalization_all`;
- `AlgebraicGeometry.Scheme.completed_constant_presentation_transport`.

The proof uses the existing stated universal derived-functor, quotient-normalization,
constant completion, ringed Koszul reflector, and completed fiber/strict-limit
interfaces. Their existing proof obligations remain with their modules. This delivery
does not claim that their transitive axioms have been eliminated.

## No longer needed

Removed the item's direct proof imports of
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`,
`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
`Sheaf.Paper.AdicCoefficientDatum`,
`Sheaf.Paper.CompletedConstantSheafReduction`,
`Sheaf.Paper.ConstantCompletionEquivalence`, and
`Sheaf.Paper.IntrinsicCompletionCompleted`. Its sole proof import is now
`Sheaf.Paper.CompletedConstantPresentationTransport`; the three original public
statement imports are preserved.

The original node no longer directly invokes the pro-zero-cone/strict-Roos argument,
countable-product exactness, or a separately constructed Koszul augmentation. Its
proof dependency is the joint transport node. The existing completed fiber and
constant/ringed reflector interfaces supply those deeper facts as needed. These
removed direct dependencies remain transitively used: no existing source module or
DAG node is withdrawn, and no whole module is claimed globally pruned. Inspection
of the item's old and new import closures found no whole module removed.

Unused exploratory imports were also removed from the new helper files. The
coefficient equivalence publicly imports the actual Cech-site definitions rather
than the later Koszul-limit comparison; the Koszul transport imports that comparison
only for its proof. Neither helper invokes the unused flat-quotient theorem; the
coefficient file imports its module privately for the functor-identification helper used in the tensor
adjunction comparison.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically compatible with the resulting proof, but the
existing universal and reflector declarations already encapsulate its Koszul and
strict-limit calculations. Repeating those calculations here is unnecessary.

The completed coefficient presentation uses `completedCechSite = AsSmall.{0} T.ProEt`.
The private small-site arithmetic in `CompletedConstantAlgebraFlatQuotients` uses a
different universe presentation. Its conclusions cannot simply be substituted into
the Cech interface by a definitional equality. The new coefficient helper explicitly
constructs the equivalence on the actual Cech site and checks its scalar map,
finite projections, quotient units, and transitions. The existing source interfaces
remain unchanged.

The Koszul transport explicitly retains `Ideal.span (Set.range a) = d.ideal`.
The quotient unit calculation only requires native K-flatness before transport;
there is no unsupported assertion that a coefficient equivalence preserves that
chosen K-flat structure. No completeness hypothesis on the input has been added.
The empty list, zero ideal, zero ring, and empty scheme are covered by the same
finite-free, limit, reflection, and naturality arguments, without nonemptiness or
nontriviality assumptions.

## New nodes

`lem-weil-pbc-completed-constant-coefficient-equivalence` records the scalar- and
quotient-unit-preserving equivalence on the actual small site.

`lem-weil-pbc-completed-koszul-constant-transport` records transport of the specified
Koszul fiber and its unit along a scalar-preserving coefficient isomorphism.

`lem-derived-exact-equivalence-squares` records the two compatible universal derived
comparison squares and their localization factorization equations.

`lem-weil-pbc-completed-quotient-unit-normalization` records the actual
constant/limit-adjunction and quotient-augmentation calculation on K-flat complexes.

`lem-constant-completion-unit-normalization` records the constant quotient unit
calculation for arbitrary complexes, proved by resolution and naturality.

`lem-weil-pbc-completed-constant-presentation-transport` records the joint transport
used by the original item. Each of these nodes has a complete Lean proof, source,
proof steps, and Mathlib search records. No unfinished result is split off.

`def-weil-pbc-completed-quotient-ordinary-unit` records the explicit ordinary
constant/limit-adjunction unit followed by the strict quotient augmentation.

`def-weil-pbc-completed-quotient-completion-unit` records the explicit published
derived adjunction unit followed by derived inverse limit of the quotient augmentation.

`def-derived-exact-equivalence-square-data` records the bundled comparison fields
and their factorization equations. Its existence is proved by
`lem-derived-exact-equivalence-squares`.

`def-weil-pbc-completed-constant-presentation-data` records the common coefficient
equivalence and the two unit-compatible completion comparison families. Its
inhabitation is fully proved by the joint transport theorem.

`def-derived-cochain-comparison-factors` records the canonical factorization between
complex localization and homotopy localization for an additive functor.

`def-derived-cochain-counit` records transport of a homotopy-derived counit to
complex localization.

`def-derived-cochain-right-unit` records transport of a homotopy-derived unit to
complex localization. Both use the explicit factorization isomorphism; their
component and universality equations are proved in the same module.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
