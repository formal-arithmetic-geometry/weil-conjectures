## What changed

Closed `AlgebraicGeometry.mixedAffineSections_kFlat_comparison_isIso` without changing its
signature or docstring. Its proof now constructs the ordinary unit-normalized affine
comparison, applies a mixed-universe localization factorization, and cancels isomorphisms.
The termwise comparison is explicitly the hom of `NatIso.mapHomologicalComplex c`; the
localization functor preserves its invertibility. `IsIso.of_isIso_fac_right hab` performs
the final cancellation, rather than applying a renamed copy of the original statement.

Added `Sheaf.AlgebraicGeometry.MixedAffineSectionsUnderivedChartModel`, whose public
comparison theorem is fully proved. The proof constructs the affine chart adjunction:
ordinary global sections equal pushforward to Spec followed by spectrum sections, including
the global scalar action. Restriction through the spectrum chart is an equivalence, so the
chart adjunction unit is invertible. Composing chart and tensor-pullback adjunctions and
using left-adjoint uniqueness produces the ordinary comparison with its exact unit equation.
The private definitions are explicit constructions from proved facts; no object is chosen
from an unproved mere existence theorem.

Added `Sheaf.AlgebraicGeometry.MixedAffineSectionsChartModelFactorization`, containing one
remaining theorem hole. It localizes an ordinary unit equation for a natural transformation
`c` and supplies the source and target model isomorphisms and the factorization equation.
Crucially, its premise does not assume `IsIso c`, and its conclusion does not assert that the
derived mate is invertible. The ordinary comparison and the localization step are distinct
parts of the original plan, with real Lean combining them in the item's module.

All three sandbox modules compile cleanly together through `lcompile.py --all`. All Lean
lines are at most 100 characters. No other existing module, statement, definition, visibility,
or target was adapted. The parent node's proof, proof dependencies and proof origin match
the delivered route.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.mixedAffineSections_kFlat_comparison_isIso`
(node `lem-sc-mixed-affine-sections-kflat-comparison-isIso`). There is no `sorry` left in
the item's module.

New theorem fully proved:
`AlgebraicGeometry.exists_mixedAffineSections_underived_chart_model`
(node `lem-sc-mixed-affine-sections-underived-chart-model`). Its private supporting
lemmas `chart_pushforward_smul` and `chart_tilde_unit_isIso` are also fully proved.

Exactly one new hole remains:
`AlgebraicGeometry.exists_mixedAffineSections_chart_model_factorization`
(node `lem-sc-mixed-affine-sections-chart-model-factorization`), in its own module, with
proof exactly `:= by sorry`. Its docstring and node contain the full localization argument.

This delivery is a decomposition: one original hole closed and one lower hole added, for a
net hole change of zero. It additionally supplies the complete ordinary affine unit
calculation. It does not claim that the original declaration is free of transitive sorries.

Edge cases were checked in the mathematical statements: zero modules, zero complexes and
empty affine schemes (zero global ring) still satisfy the adjunction and isomorphism
equations. No nonzero-ring, boundedness, perfectness, or flatness hypothesis was introduced.
The underived proof works for arbitrary affine morphisms. In the factorization, a natural
transformation satisfying the unit equation is used without an invertibility premise;
zero transformations satisfy the equation only in the corresponding degenerate cases.
Sheaf and module derived universes remain independent throughout.

## No longer needed

Removed the item's direct proof imports
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence` and
`Sheaf.AlgebraicGeometry.AffineKFlatPullbackChartComparison`.

The full equivalence node `lem-pc-affine-qcoh-derived-equivalence` is no longer needed for
this proof route: the smaller, already proved
`AlgebraicGeometry.affineTildeDerivedSectionsUnit_isIso`
(node `new-affine-tilde-derived-sections-unit-isIso`) supplies the required ordinary-to-derived
sections comparison. The factorization module imports this smaller interface, together with
`TensorPullbackTilde` and `AffineKFlatPullbackChartComparison`.

The chart comparison remains needed in the localization factorization, so its original
import was moved to the lower module rather than pruned. The other original dependencies
`lem-pc-global-hom-adjunction`, `lem-sc-mixed-global-extension-adjunction`, and
`lem-sc-mixed-global-sections-direct-image-iso` remain required by that factorization and
by the unchanged statement interfaces.

No whole module is claimed to leave the targets' import closure: the old affine equivalence
remains reachable through existing public dependencies of `GlobalHomAdjunctionIso`.
The pruning here is removal of a direct proof import and of the planned full-equivalence
proof dependency, not a claimed reduction in the global closure module count.
No unit statement or realized unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the item's statement was found. The two old proof-dependency
interfaces do not by themselves state the needed normalized mate equation:
`affine_kFlat_pullback_chart_comparison` gives a `Nonempty` object isomorphism, while the
full affine derived equivalence supplies a derived sections equivalence. Neither records
the factorization of the fixed mixed-universe adjunct through the localized ordinary map.
The remaining localization theorem isolates precisely that missing glue.

The equal-universe `AffineExtensionSectionsModelMate` route was read, including
`AffineExtensionSectionsUnderivedModel` and `AffineExtensionSectionsModelFactorization`.
It uses spectrum bases, affine base-ring scalar transport, and one localization universe,
so it cannot directly instantiate the present Gamma-ring chart and independent-universe
statement. Its ordinary adjunction calculation inspired the complete chart version here;
its still-open localization factorization was not copied into the original theorem.

Searches: LeanFinder returned ordinary pullback/adjunction tools but no exact mixed derived
comparison. Loogle did not resolve the unqualified `Adjunction.leftAdjointUniq`; direct
Mathlib source inspection found the qualified declaration and its unit equation. Source
grep found the restriction and uniqueness tools and the equal-universe project modules.
LeanSearch was attempted and returned an Internal Server Error, recorded as unavailable.
Whole-blueprint search for "affine extension sections" found no matching imported node.

The primary source statements were read online:
[Tag 01I9](https://stacks.math.columbia.edu/tag/01I9) gives the ordinary affine pullback
calculation; [Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0) gives the affine derived
sections unit computation; [Tag 08DW(2)](https://stacks.math.columbia.edu/tag/08DW) compares
derived pullback and derived scalar extension; [Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
gives composition of derived direct images; and
[Tag 0AA7](https://stacks.math.columbia.edu/tag/0AA7) uses the scalar-extension adjunction
transpose. The explicit normalization argument is marked as agent-written in the nodes.
WANTED locally: `literature/stacks-project/perfect.tex`, `schemes.tex`, and `cohomology.tex`
at these source tags; those source text files are absent in this read-only checkout.

## New nodes

`lem-sc-mixed-affine-sections-underived-chart-model` records the ordinary comparison on
actual canonical Gamma-ring charts, with its fixed tensor-pullback unit equation. Its
module and complete proof are supplied. This statement is entirely underived and has no
K-flat or derived-localization premise.

`lem-sc-mixed-affine-sections-chart-model-factorization` records localization of an arbitrary
ordinary natural transformation satisfying that unit equation. It supplies the two model
isomorphisms and the factorization equality without asserting invertibility of the
transformation or its mate. This is the one new item for a subsequent worker.

Both inherit the parent's chapter, unit, and blueprint ancestor. Their source, searches,
proof steps, proof-dependency unions, and exact Lean signatures are recorded. No change
record is needed because no existing interface changed.

## Second reading by J3

1. I compared the delivered primary module with the repository version. The theorem signature and
all existing declarations are byte-for-byte unchanged; only proof-only imports and the proof body
changed. Verdict: pass.

2. I compiled all three delivered modules with `lcompile.py`, individually and in dependency order.
The only remaining `sorry` is the named factorization theorem, and there are no axioms, unsafe,
opaque, extern, or implemented_by declarations. Verdict: pass, with the documented split-off hole.

3. The underived chart-model theorem is a genuine stronger intermediate calculation with a complete
proof. The factorization theorem is strictly lower than the target, retains the ordinary unit
hypothesis, and does not assume invertibility of the comparison. Its docstring and DAG node state
the intended localization argument. Verdict: pass.

4. The proof follows the shortest available route through the completed chart model and the explicit
localization factorization. The removed direct imports are not used by the proof, while the unit route
and required chart dependencies remain. Verdict: pass.

5. The DAG proof, dependencies, origins, and Lean declarations agree with the delivered code; the
unit's realized route is preserved. Verdict: pass.

I changed only this report by adding this second-reading record. No Lean source or DAG metadata was
changed during the second reading.

The final scratch `#print axioms` probe confirms that the underived comparison uses only
`propext`, `Classical.choice`, and `Quot.sound`; the primary comparison and the split
factorization additionally use `sorryAx`, as expected. An independent search for
`derivedη_fac_app` and `unit_leftAdjointUniq_hom_app` found the generic Mathlib unit
identities, not a replacement for the mixed-universe statement. I read the equal-universe
model factorization interface and checked the unit record: this delivery changes neither
its statement nor its realized fields. The dry run passed as CODEX (new modules and nodes).
