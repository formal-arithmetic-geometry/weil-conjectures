## What changed

Completed five existing proofs in `Sheaf.SixFunctors.OpenTensorNormalization`.
The generated vertical topology equals the topology defined by covering vertical slices.
Its sheaf condition is componentwise, so ordinary continuity gives both system continuity
results. Cocontinuity also transfers componentwise. The product of the site adjunction
with the identity adjunction on natural numbers makes open restriction a left adjoint;
it therefore preserves colimits. Forgetting to abelian sheaves proves finite-limit
preservation sectionwise, and finite-product preservation proves additivity.
The chosen pullback isomorphism gives the Cartesian universal property by Mathlib's
`IsPullback.of_iso_pullback`. The final theorem combines the existing two normalization
theorems. All original signatures, public imports and definitions are preserved.
Private helpers contain complete proofs and no holes.

Rechecked the retained sandbox against current sources. The server single-file compiler
accepted it with no errors or warnings (53.8 seconds). Renewed LeanFinder, Loogle and
grep searches confirm the direct Mathlib pullback and exactness APIs used here;
the geometric scheme-module restriction hits do not supply the arbitrary ring-sheaf
or system normalization statements. The infrastructure note is appended to the DAG
proof, preserving the numbering of its retained construction plan.

## Proved and sorry left

Closed five of the original seven holes:

- `SheafOfModules.OpenTensorNormalization.baseChange_continuous`.
- `SheafOfModules.OpenTensorNormalization.openInclusion_continuous`.
- `SheafOfModules.OpenTensorNormalization.restriction_exact`.
- `SheafOfModules.OpenTensorNormalization.square_isPullback`.
- `SheafOfModules.openTensorNormalization` (uses the two existing construction theorems).

Two original named holes remain, both attached to `lem-sf-open-tensor-normalization`:

- `SheafOfModules.OpenTensorNormalization.exists_normalized`: still needs the compatible
  open extensions, derived pullbacks, tensor presentations and specified beta/gamma mates.
- `SheafOfModules.OpenTensorNormalization.finite_compatibility`: still needs the four
  constant-scalar realizations, their pinned comparisons and the two arrow equalities.

No holes added or split off. The final assembly depends on the two remaining holes;
this is partial progress, not an axiom-free proof of the whole normalization theorem.

## No longer needed

The completed continuity and exactness arguments use Mathlib directly rather than
localized-module exactness or the small-universe diagram-site realization theorem.
The large remaining construction plans retain their existing DAG dependencies;
no entire node or unit is claimed unnecessary solely because its construction is open.
Removed proof imports (after checking the module still compiles):

- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`.
- `Sheaf.CategoryTheory.DiagramSiteRealization`.
- `Mathlib.Algebra.Category.Grp.FilteredColimits`.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`.
- `Mathlib.CategoryTheory.Sites.Limits`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Mathlib.Algebra.Homology.BifunctorShift`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`.
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`.
- `Sheaf.Paper.KFlatRingedToposPullback`.
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`.
- `Sheaf.Paper.RingedTopoiDerivedPullback`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.CategoryTheory.RingedSheafSliceAdjunction`.

Also remove the obsolete `tool_uses` entries `lem-coef-semilinear-derived-sections`
and `lem-pur-coefficient-system-derived-comparison`: the retained current proof plan
works on the vertical diagram site directly and already does not list these among
its proof dependencies. Neither enhanced sections nor a special quotient-tower
comparison is used here.

The public imports remain necessary for existing interfaces. No unit-level route changes.

## Where the brief, the DAG or earlier work was wrong

The recorded diagram-site realization theorem is small-universe only, whereas this
module has site object universe `u+1` and morphism universe `u`. Private helpers prove
the needed sheaf criterion directly at those universes. The generated vertical
coverage is identified with the vertical-slice topology without changing its definition.
Mathlib's general module-pullback right-adjoint instance likewise requires small site
categories; the proof instead reflects finite limits through the existing forgetful
functor to abelian sheaves. No statement is weakened and no consumer needs adaptation.

Change record: `coord/changes/V6-open-tensor-proof-helpers.md`.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
