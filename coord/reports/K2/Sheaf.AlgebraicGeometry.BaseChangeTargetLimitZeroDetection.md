## What changed

Wrote a reduction of `AlgebraicGeometry.Etale.baseChange_target_limit_zero_detection`
to the existing `higherDirectImage_limit` theorem, a geometric preparation lemma,
and a natural comparison of target stalks with fixed-coefficient higher-image stalks.
Replaced two redundant proof-only imports with the two new helper modules.
The original theorem signature is unchanged.
The geometric preparation lemma has a complete proof and compiles locally.
All three modules now compile locally without warnings. The refreshed baseline
supplied the previously missing `BaseChangeStalkTransition.olean`. The saved
combination proof needed two repairs: explicitly expose composition application
before rewriting the projection vanishing hypothesis, and identify the local
pullback functor and coefficient sheaf before rewriting finite-stage vanishing.
Replaced proposition-valued `letI` declarations by `let` to satisfy the style linter.

## Proved and sorry left

Proved and locally compiled:
`AlgebraicGeometry.Etale.baseChange_target_limit_geometry`
(node `lem-sbc-target-limit-geometry`). It uses only Mathlib.

The main theorem `AlgebraicGeometry.Etale.baseChange_target_limit_zero_detection`
(node `lem-sbc-target-limit-zero-detection`) is proved by a complete, locally compiled combination proof from the geometric
lemma, the natural comparison, and the existing continuity theorem.
One original hole is closed and one new hole is added: this is a decomposition,
not a net reduction in the number of holes.

The one new remaining sorry is
`AlgebraicGeometry.Etale.baseChange_target_stalk_higher_image_comparison`
(node `lem-sbc-target-stalk-higher-image-comparison`). It asserts natural
isomorphisms for arbitrary schemes over T, independently of any inverse system,
compactness, limit cone, representative, or vanishing hypothesis. It is strictly
the coefficient and transition identification step, not zero detection renamed.
Its docstring gives the construction and the derived-adjunction coherence argument.
The imported `higherDirectImage_limit` may still rest on its own open dependencies;
these are existing stage-3 items and are not changed here.

## No longer needed

Removed the redundant direct proof-only imports
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition`
and `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: the unchanged public
import `BaseChangeStalkTransition` already provides them transitively. Their
modules remain reachable; no module is pruned. `BaseChangeStalkTransition` is
required by the unchanged public signature. No original planned mathematical
dependency is pruned from the transitive proof route.
The original direct proof dependency `def-weil-pbc-inverse-image` moves into the
comparison node; it remains transitively needed. There is no separate negative-degree
lemma: the existing integer-degree continuity theorem and natural comparisons
already cover negative degrees. No source-image descent or survival theorem is used.

## Where the brief, the DAG or earlier work was wrong

Earlier attempts were blocked by the missing object file for the assigned module's
public import `Sheaf.AlgebraicGeometry.BaseChangeStalkTransition`. The baseline
refreshed during this retry; the import and all delivered modules now compile.
The earlier saved proof had two simplification failures hidden by that missing
import; both are repaired without changing any statement.

The original plan's geometry can be proved directly from Mathlib: pasted pullback
squares, base-change stability, `isAffineHom_π_app`, and preservation/reflection of
connected limits. The comparison of the canonical square with the iterated
pullback square is not definitionally automatic, and is separated explicitly.

Sources read: [Tag 0F07](https://stacks.math.columbia.edu/tag/0F07), the restriction
square and limit condition, and [Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1).
The source library's `Coefficients.baseChangeTargetFunctorIso` was also read.
The unit `sk-lem-failure-field` has no nodes designated in its `realized` lists;
its continuity route is retained. Edge cases checked in the new statements:
identity and composite maps over T, negative degrees, an empty stage scheme,
and a constant singleton diagram. Geometry needs a nonempty cofiltered category,
which is exactly the hypothesis used to choose a stage.

## New nodes

`lem-sbc-target-limit-geometry`, module
`Sheaf.AlgebraicGeometry.BaseChangeTargetLimitGeometry`: the geometric hypotheses
for the base-changed continuity theorem, proved directly in Lean from Mathlib.
No sorry remains in this module.

`lem-sbc-target-stalk-higher-image-comparison`, module
`Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison`: natural
isomorphisms between the canonical target stalk system and the higher-image system
of the fixed sheaf on T×_S X. Its sole theorem is left `:= by sorry`, and carries
the source and proof in words. This module now compiles locally. No interface change record is needed: existing
signatures and public imports are preserved.


## Second reading by K2

1. Compared every delivered module with the repository. The two helper modules
   are new. The existing zero-detection theorem's variables, hypotheses, conclusion,
   and docstring are unchanged; its signature is byte-for-byte preserved. No
   existing definitions or public imports change, and no change record is needed.
2. Compiled all three modules in import order with `lcompile.py --all`, with no
   errors or warnings. Searched all delivered Lean files for prohibited constructs:
   none occur. The sole remaining `sorry` is the named comparison theorem reported
   above, with its docstring proof and matching node. Scratch `#print axioms`
   checks give only `propext`, `Classical.choice`, and `Quot.sound` for geometry;
   the comparison and combination theorem additionally use `sorryAx`, consistently
   with the open dependencies. There are no definitions in the delivery.
3. Read the definitions of both stalk transitions and `higherDirectImageOverMap`,
   and the existing `baseChangeTargetFunctorIso`. The comparison is coefficient
   transport across the canonical iterated-pullback isomorphism and compatibility
   of the derived unit-composition-counit maps. It has no inverse-system or
   vanishing assumptions and cannot restate zero detection. Identity maps give
   identity transitions; composite maps use inverse-image associativity. Empty
   schemes and negative degrees give zero objects on both sides, with no exception.
   Repeated LeanFinder, Loogle, and Mathlib grep searches using scheme-isomorphism
   transport and derived-functor terminology, and searched the upstream/project
   Lean files. Found generic transport tools and the known objectwise coefficient
   isomorphism, but no existing natural stalk-system comparison. The complete
   coherence proof is substantial and is left as the explicitly reported hole.
4. The combination proof uses geometric preparation, natural comparison, and the
   zero-detection clause of the existing continuity theorem; injectivity of an
   isomorphism transfers zero back. Geometry is already proved directly with
   Mathlib. No shorter existing natural comparison was found. Checked the unit
   `sk-lem-failure-field`: its `realized` lists are empty, and the continuity step
   of its written route is retained. Both old proof dependencies remain
   transitively used; neither is pruned. Corrected the report to list the two
   redundant original direct imports removed, without claiming module pruning.
5. Read all three delivered JSON nodes and compared the existing node against
   the repository. Its only changed fields are `proof`, `proof_deps`, and
   `proof_origin`. The steps and dependency unions describe the Lean argument.
   Both new nodes have source, full proof steps, searches, creation/blueprint
   records, chapter/unit, and matching Lean declarations. The one closed original
   hole and one added comparison hole are correctly reported as decomposition,
   with zero net hole reduction; geometry adds no hole.

Changes made during second reading: narrowed the geometry module's public import
from `AffineTransitionLimit` to `Morphisms.Affine`, keeping `AffineTransitionLimit`
as a proof-only import; restored exact spacing before the original theorem's
proof; corrected the removed-import report; appended this independent review.
All three modules compile again after these changes.
