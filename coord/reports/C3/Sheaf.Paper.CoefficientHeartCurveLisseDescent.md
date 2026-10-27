## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientHeart_curve_lisse_descent` in
`Sheaf.Paper.CoefficientHeartCurveLisseDescent`, preserving its complete signature and
both real-data comparison definitions. Fully proved private helpers select a small
subcover, normalize the supplied cartesian refinements to chosen pullbacks, pull back
covers, and lift a specified isomorphism through a fully faithful functor. The forward
implication transports the original finite-free models; the reverse implication uses
the same compatible trivializations as the explicit clause.

The cover helpers hide chosen scheme-limit constructions from dependent coefficient
module types. Local irreducibility attributes on the actual module pullback and the two
comparison definitions keep subsequent elaboration abstract; these attributes do not
escape the module. No definitions or public interfaces were changed. Updated the proof
node to record the actual proof and remove three obsolete tool approvals.

Validation: single-file compile passed cleanly in 8.1 seconds before the final removal
of the redundant MapMod import; the delivery compile checks that final version and all
its declarations with the standard axiom probe. The proof allows arbitrary input-cover
universe, varying ranks including zero, empty schemes and covers, and arbitrary
surjective closed immersions without a nilpotence bound. No new mathematical assumption
is used. No other module is adapted.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.coefficientHeart_curve_lisse_descent`
(node `lem-sfb-coefficient-heart-curve-lisse-descent`).

No sorry remains in the item. Added 0 holes and split off 0 statements. All four private
helpers are proved; the two existing canonical isomorphism definitions are unchanged.
The theorem uses the previously declared cover-refinement and condensed-module-equivalence
results as intended by stage 3; its transitive axioms are checked by delivery preflight.

## No longer needed

Removed the following private imports:

- `Sheaf.CategoryTheory.MonoidalFiniteFreeTransport`: the existing canonical finite-free
  comparison already constructs the needed isomorphism by `mapBiproduct` and regular
  module transport. Node `lem-sfb-monoidal-finite-free-transport` is unused here.
- `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization`: the statement and proof
  already use actual coefficient pullbacks; no section or slice restriction calculation
  occurs. Node `lem-sfb-coefficient-sections-localization` is unused here.
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`: the standard
  base-change instances directly make each closed-fibre projection closed and surjective.
  Node `lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism` is unused here.
- `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`: its needed API is already
  available through the public imports; no separate import is necessary.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc` and
  `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`: existing public pro-etale imports
  already provide the covering base-change instances.

Removed only the corresponding three obsolete entries from the node's `tool_uses` and
from its proof dependencies. Their modules may still be needed by other library users;
no module or source declaration is withdrawn. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was required. The previous sandbox attempt left the
small-subcover universe implicit and tried to use `choose` on a `Nonempty` isomorphism;
these did not compile. Explicit universe selection and `Classical.choice` resolve them.
An explicit `Precoverage.Small` instance obtained by unfolding the pro-etale precoverage
is needed for instance search. Elaborating chosen cover constructions inside dependent
module types caused expensive unfolding; proved existential cover interfaces and local
irreducibility resolve it without changing a definition or increasing a timeout.

The proof plan's localization and general monoidal-transport detours are unnecessary for
the already fixed Lean statement. The base-changed closed-immersion and surjectivity
instances also avoid the universal-homeomorphism detour. No unit statement or step is
bypassed and no new nodes are needed. The static preflight requires a change record
for the local attribute command; see
`coord/changes/C3-coefficient-heart-curve-lisse-local-transparency.md`. The record lists
the unchanged direct consumer and explains the local scope of the attributes.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
