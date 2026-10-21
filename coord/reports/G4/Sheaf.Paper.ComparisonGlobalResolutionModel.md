## What changed

Proved `AlgebraicGeometry.ProEtale.comparisonGlobalResolutionModel` in its existing
module, with all public declarations, definitions, and signatures preserved.
Four private proved helpers establish localization of quasi-isomorphisms,
naturality of the specified cycle classes, the defining derived base-change
unit equation with the derived identity removed, and existence of the two
nonnegative termwise injective K-injective resolutions.

The computing isomorphisms are explicitly the actual right-derived units followed
by inverses of the derived augmentations. The comparison equality follows directly
from `rightDerivedFunctorPlusBaseChange_fac`, naturality at the supplied `t`, and
naturality at the supplied `i`. Homology naturality gives the cocycle equation;
the evaluated termwise adjunction formula is definitional. The node proof,
proof dependencies, proof origin and obsolete tool approvals follow this route.
No public interface, target statement, or source-library file changes.

The required LeanFinder search returned generic right-derived resolution formulas;
Loogle returned `Adjunction.derived_unit`. Neither states this full resolution model.
Local source searches located the stronger fit for this encoding:
`rightDerivedFunctorPlusBaseChange_fac`, the defining equation of the existing
global map, together with the identity-derived localization factor equation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.comparisonGlobalResolutionModel`
(node `lem-pur-comparison-global-resolution-model`).

The item has zero remaining `sorry` declarations. Zero holes added and zero
results split off. All four private helpers have complete proofs. This proof
uses the existing declared resolution theorem and the existing canonical global
comparison construction; it does not assert that every transitive dependency of
the library is already free of `sorry`.

## No longer needed

Removed these proof imports:

- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`:
  the existing Grothendieck instances for fixed `ModuleCat`-valued sheaves supply
  enough injectives directly, without changing coefficient encoding.
- `Sheaf.Paper.PurityComparisonUnitInjectiveModel`:
  the defining equation of the recorded global comparison supplies its normalized
  resolution calculation directly; transport through `FiniteCoefficientModules`
  is unnecessary.
- `WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension`:
  the terminal-object normalization is already part of
  `finiteComparisonGlobalSectionsUnit`; a second derived-sections comparison is
  unnecessary.
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`:
  the proof only computes on `I` and `J`, whose termwise injectivity is supplied;
  it does not need an injective direct-image resolution.

Consequently the proof no longer needs
`lem-weil-pbc-ring-sheaves-grothendieck`,
`lem-pur-comparison-unit-injective-model`,
`lem-sp-right-adjoint-preserves-injectives`, or a separate application of
`lem-weil-pbc-derived-sections-pushforward`. The last node remains a statement
dependency: its existing meaning and attachment are preserved. The fixed-ring
Grothendieck instances are recorded by the existing
`lem-sfb-proetale-sheaves-grothendieck` node, used at the relevant coefficient
specialization. Obsolete entries for ring-sheaves Grothendieck and derived-sections
pushforward are removed from this node's `tool_uses`; no tool approval is added.
Other consumers and existing public imports may retain these modules in the global
closure; no library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan is longer than necessary for the
actual normalized global comparison definition, which is already the canonical
right-derived base change of the terminal evaluation of the adjunction unit.
Its existing unit compatibility avoids the coefficient-encoding transport and
the intermediate derived direct-image calculation. This changes only the route
below the unit level, preserving the blueprint unit and all target statements.

Edge cases: the resolution and naturality arguments apply to zero sheaves, the
zero ring and the empty scheme; the cycle argument holds for every integer degree
and thus includes the required degree zero. The proof treats every supplied pair
of augmentations and never requires inverse image to preserve injectives.

Validation: the final single-file `lcompile.py` run compiled successfully with
no errors or warnings. The file remains within the 60-second limit. A source audit
confirmed zero `sorry` tokens, unchanged main theorem signature and existing
non-theorem declarations, maximum line width 98, and exactly the permitted node
field changes (`proof`, `proof_deps`, `proof_origin`, and removal of obsolete
`tool_uses`). The delivery tool supplies the final compile/probe and preflight.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
