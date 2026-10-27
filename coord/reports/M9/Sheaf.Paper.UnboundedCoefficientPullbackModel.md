## What changed

Proved `AlgebraicGeometry.ProEtale.unboundedCoefficientPullbackModel`, preserving its
complete signature and the two public computation definitions verbatim. The balancing
chain supplies the normalized A-linear comparison and B-linearity. A concrete B-linear
lift gives `s`; its inverse applied degreewise gives `T`. Two adjunction bijections
identify this inverse with the ordinary scalar/pullback mate. The general derived
mate representative formula, followed by naturality along the supplied `i.inv`, proves
the computation equation for arbitrary K.

The ringed-topos pullback theorem supplies both K-flatness and termwise flatness.
Exactness preserves quasi-isomorphisms; the K-flat scalar counits make both computation
maps invertible. All added helper declarations are private and proved. A proof-only `import all` of
`Sheaf.Paper.PulledReductionNormalizationComparison` reuses its already-proved
`ordinaryMate`, `ordinaryMate_one`, `scalar_unit_formula`, `derivedMate_rep`, and
`pullback_good` helpers. The scalar counit helper is reused from the existing
coefficient datum module. The normalization module carries its existing completed
coefficient dependencies; this delivery does not claim to prove or prune those.
No new public interface, definition repair, or consumer adaptation
is needed. The node proof and proof dependencies now describe this route. The unit's
realized statements and steps are preserved.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.unboundedCoefficientPullbackModel`
(node `lem-exc-unbounded-coefficient-pullback-model`).

Holes closed: 1. Holes added: 0. Split off: 0. No `sorry` remains in this module or
in any new helper. This proves the item from the existing library declarations;
existing unresolved dependencies such as the scalar balancing chain are not claimed
as proved by this delivery.

## No longer needed

Removed the proof-only imports
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`, and
`Mathlib.CategoryTheory.Localization.Predicate`, and
`Sheaf.Paper.KFlatRingedToposPullback` (the latter is accessed through the reused
normalization helper).

Removed the node's direct proof dependencies and obsolete tool approvals
`lem-pc-kflat-resolution`, `lem-weil-pbc-site-derived-tensor-descent`, and
`lem-weil-pbc-localization-universal-property`. A representative is supplied in the
statement; its existence need not be proved again. The canonical derived comparison
already exists, so its representative equation follows from normalized adjunctions
and the derived mate comparison without constructing another localization.
These nodes/modules are not withdrawn: other declarations may still use them,
and resolution/localization results remain transitive construction dependencies.
No library module is deleted or globally pruned.

## Where the brief, the DAG or earlier work was wrong

The planned localization descent is unnecessary for this precise Lean statement,
which asks for the computation formula for an already-defined canonical comparison
and a supplied representative. The balancing chain supplies B-linearity, rather than
a packaged B-linear isomorphism; the proof constructs that lift and verifies its
identity with the canonical ordinary mate explicitly. No statement is disputed or
weakened, and neither public computation definition changes.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
