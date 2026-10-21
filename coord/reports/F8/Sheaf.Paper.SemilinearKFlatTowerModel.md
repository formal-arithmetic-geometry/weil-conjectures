## What changed

Filled `AlgebraicGeometry.ProEtale.sp_semilinear_kflat_tower_model` using the
existing simultaneous strict-system resolution and the recorded coefficient-tower
equivalence. Added private, proved helpers for the explicit completed-ring
restriction functor, its exactness, the projection cone equation, and the two
naturality cancellations. The existing theorem signature is unchanged. Factored the pure-tensor clause
through the identical generic sectionwise formula, because the original
specialized definition alone costs 45–49 seconds of kernel checking. The other
public definitions remain unchanged. Updated the node proof and dependencies
to follow this argument.

The representative is constructed on the whole varying-coefficient system before
being evaluated. Its scalar reduction equations follow from `ordinaryReduction_eq`,
`reduction_rep`, the normalized scalar adjunction, and its pure-tensor formula.
The completed lift restricts the actual transitions sectionwise. Both evaluation
and derived-limit projection equations follow from naturality.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtale.sp_semilinear_kflat_tower_model`
(node `lem-sp-semilinear-kflat-tower-model`). One original hole closed; zero holes
added or split off. No `sorry` remains in the delivered Lean source. The assembled zero-hole proof compiled on the server in 48.4 seconds; the
production file removes the diagnostic profiler. The separate definitional-
equivalence probe compiled in 3.1 seconds. Delivery preflight follows.

## No longer needed

Removed the direct proof imports `Sheaf.CategoryTheory.DiagramSiteTopology`,
`Sheaf.CategoryTheory.RingedToposMorphism`, and
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
Their direct node dependencies `lem-weil-pbc-diagram-site-topology`,
`def-weil-pbc-ringed-topos-morphism`, and `lem-pc-kflat-resolution` are replaced
here by the established `lem-pur-system-evaluation-kflat`. Those results remain
needed transitively by that general theorem; no module is withdrawn.

The projection equation uses the naturality of each projection supplied in the
predicate, so this proof does not apply
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`. Its public import and statement
dependency are retained because the public predicate uses its derived-limit API.
The old direct proof-only `sk-def-sp-coefficient-towers` use is retained for the
completed coefficient limit and cone normalization. The K-flat pullback module
remains imported privately for its proved invariance-under-isomorphism helpers.
No whole module is claimed pruned from the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The first four planned steps are already available as
`SheafOfModules.strictRingSystem_kFlatResolution`. Reusing it preserves the unit's
whole-system-resolution route. The remaining canonical comparison identities are
proved from the supplied normalizations; no new mathematical assumption is needed.

A dependent existential elimination caused a kernel timeout even in a minimal
scratch proof. Explicit witnesses from the proved representative theorem avoid
that conversion cost. The second expensive conversion is eliminated by the
data-only generic `SheafOfModules.systemTensorSectionFormula`. It is applied
to the same `Qn`, `beta`, and `q`; expanding it gives the original formula,
including the exact scalar action. See the definition repair record
`coord/changes/F8-semilinear-tensor-formula.md`. The downstream-user tool
reports zero downstream modules; no forced consumer adaptations are needed.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
