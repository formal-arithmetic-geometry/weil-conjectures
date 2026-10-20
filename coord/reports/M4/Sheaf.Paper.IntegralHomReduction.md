## What changed

Retained the earlier sandbox's complete assembly proof of
`WeilConjectures.integralHomReduction`. Definitions and presentation records were
extracted to `Sheaf.Paper.IntegralHomReductionModels` to allow the three
helper modules to import them without a cycle. The original module publicly
re-exports this interface. Existing declaration signatures are unchanged. The body of `homModelMap` uses
the existing named localization factorization to avoid repeated elaboration;
a compiled equality proof by `rfl` verifies that it is the original morphism.
All other extracted declaration bodies are unchanged.
The repair also updates the private proof import in `IntegralHomModelsExist`
from the removed `Sheaf.Algebra.Homology.RhomGlobalSections` module to its current
independent-universe `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses` module,
which is the current Lean attachment of `lem-pur-rhom-global-sections`. The stale
compiled module loaded the removed `Sheaf.Algebra.Homology.DerivedInternalHom`
and collided with the canonical declaration. No declaration signature changes.
The interface also imports the current
`WeilConjectures.Algebra.Homology.HomComplexProjections` in place of its removed
`Sheaf` path. The exported projection theorem is unchanged.
The parent constructs the existential witnesses, proves the evaluation equation
by the adjunction inverse law, and proves arbitrary-transpose compatibility by
adjunction naturality and the tensor comparison's naturality.

## Proved and sorry left

Original holes closed: `WeilConjectures.integralHomReduction` (1 of 1).
New holes added: 3. Actual delivery hole count: 3, all named below.
This is a decomposition, not a net hole reduction.

- `WeilConjectures.IntegralHom.models_exist`, node
  `lem-sf-integral-hom-models-exist`: needs evaluation normalization for every K-injective representative and
  simultaneous normalized coefficient tensor comparisons. The existing closed
  structure supplies the tensor, its K-flat comparison and the abstract adjunction.
- `WeilConjectures.IntegralHom.comparison_isIso`, node
  `lem-sf-integral-hom-comparison-is-iso`: needs identification of the transpose
  with the signed finite-free Hom-complex comparison and conservative restriction.
- `WeilConjectures.IntegralHom.reductionTower_components`, node
  `lem-sf-integral-hom-tower-components`: needs the finite comparison isomorphisms
  on fixed K-flat representatives, with consecutive-transition and augmentation
  equations. It asserts neither completeness nor a product statement.

Additional fully proved declarations:
`WeilConjectures.IntegralHom.augmentedTower_comparison` constructs the Hom
representative and its K-flat resolution and assembles the component isomorphisms
with `NatTrans.ofOpSequence`;
`WeilConjectures.IntegralHom.hom_roosTransport` transports the actual distinguished
Roos triangle through Hom and the augmented tower isomorphism. Its two private
proved helpers identify the canonical Pi product with the homotopy-limit Fan in
both directions, including the endomorphism 1-s and the first arrow. The Hom
functor's right adjunction comes directly from the tensor presentation already
supplied by the parent. Roos transport no longer makes a second choice through
`models_exist`; it needs no separate closed symmetric monoidal structure.

No definition contains a hole. All seven delivery modules compiled against the
current published build, including the resumed seven-module check on 2026-10-20.
The unchanged interface also compiled independently in 34.7 seconds. The latest full packet check (`scratchpad/packet-final.log`) passed all seven
modules. The preceding check compiled model existence in 3.4 seconds, tower
components in 4.6 seconds, augmented-tower assembly in 6.1 seconds, Roos transport
in 7.5 seconds, and the parent in 5.7 seconds. All 25 extracted signatures are retained; 24 bodies
are unchanged and the remaining body is definitionally equal to its original.
A scratch copy of the original `homModelMap` and an equality proof by `rfl`
compiled (6.2 seconds).

The current consumer-check batch compiled AdicClosedConstructible,
BasicOperationsCoefficientReduction, IntegralConstructibleInternalHom and
PointDerivedHomEvaluation unchanged. The last retains its existing long-line
warning. IntegralVerdier failed at its imports with a duplicate
`SheafOfModules.tensorClosed`, loaded from both
Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed and
WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed. Compiling the
unchanged original IntegralVerdier directly against the published build produced
exactly the same import failure (2.6 seconds). This failure is independent of this
packet; no consumer source was adapted to mask it. A second current batch compiled FiniteTorStability (34.8 seconds),
ArbitraryFieldVerdier (55.0 seconds), and the source-library
ProEtale.ModuleObject.Derived.BoundedConstructible (47.7 seconds), all unchanged.
PointCompletedEvaluation, the other external textual user of homModelMap, also
compiled unchanged (30.5 seconds). Thus seven of eight current direct consumers
and both external textual users were checked successfully; the eighth reproduces
the published-build import failure described above.

The isolated obligations include n=0 (positive
exponent one), zero objects, arbitrary unbounded K, and no completeness premise
on K. A scratch proof confirms that the independent-universe closed structure supplies
the tensor, K-flat comparison, and abstract tensor-left/Hom adjunction. Its fixed
K-injective-replacement evaluation still needs transport to every representative
and to this record's signed order; the scalar comparison also needs its precise
normalization. The existing single-universe TensorData theorem does not discharge
these remaining equations. Added the normalized closed-structure and scalar-Hom
adjunction proof imports to `IntegralHomModelsExist`, matching its recorded
proof dependencies. An independent scratch calculation also verifies the generic
signed uncurrying differential and coproduct extension in all integer degrees
(`scratchpad/signed-chain-differential-fixed3.log`). The evaluation-normalization
prototype is unfinished and is kept only in scratchpad; it is not included in the
delivery or counted as a proved presentation.

## No longer needed

The removed public import path `Sheaf.Algebra.Homology.HomComplexProjections`
is replaced by `WeilConjectures.Algebra.Homology.HomComplexProjections`, retaining
the same projection theorem and mathematical dependency.

The obsolete proof import `Sheaf.Algebra.Homology.RhomGlobalSections` is replaced
by `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`. The same global-sections
lemma and DAG dependency are retained; this is a module-name update, not pruning.

`Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal` was removed from
`IntegralHomRoosTransport`: the supplied source tensor presentation supplies the
right adjunction used there. Its theorem is still relevant below `models_exist`,
so this is a removal of an unnecessary direct dependency, not a globally pruned node.
The direct import of `Sheaf.Paper.IntegralHomModelsExist` was also removed from
Roos transport by passing the parent's already chosen presentation. The tower
component argument still needs model existence; its node is not globally pruned.

The argument no longer uses `lem-weil-pbc-ringed-projection-mate-exact`
(`Sheaf.Paper.ProjectionMateExact`): scalar tensor normalization uses the scalar
adjunction directly. It also no longer uses
`lem-weil-proetale-countable-products-exact`
(`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`): the input completeness
witness supplies the source product, and transport supplies the target product.
General derived-limit existence (`lem-weil-derived-limit-existence`) is also
unnecessary: the proof starts from the actual product and distinguished triangle
in the given completeness witness and transports them. These three obsolete
entries were removed from the parent's `tool_uses`. Other parents may still need
these modules; no module is withdrawn.

The parent's following direct proof imports were removed. Apart from those three
dependencies, their mathematical work remains below the three named obligations.
No unit statement or route is bypassed. No existing module is withdrawn.

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Algebra.Homology.RhomGlobalSections`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SplitPerfectTensorKInjective`
- `Sheaf.Algebra.Homology.HomComplex`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence`
- `Mathlib.CategoryTheory.Yoneda`
- `Mathlib.CategoryTheory.Adjunction.Limits`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`

## Where the brief, the DAG or earlier work was wrong

The retained new nodes had abbreviated statements, incomplete dependency records,
no recorded Mathlib searches, and an obsolete blueprint source path. Their Lean
signatures, full proof explanations, recorded searches, and current source path
are now recorded. Removed a nonexistent Mathlib-node identifier from the parent
DAG's elementary adjunction step. The retained report still described Roos transport as a hole, although its proof
and the augmented-tower assembly had subsequently been completed. This report now
names the actual three holes. The current blueprint snapshot numbers the lemma
2478 (the original module and older node used 2134); the source lemma and proof
path identify the same argument. The interface extraction is recorded in
`coord/changes/IntegralHomReductionInterfaceExtraction.md`.

The retained report incorrectly described all extracted bodies as verbatim.
The resumed check found the refactored `homModelMap` and verified its equality to
the original. The record now documents that refactoring, the added narrow public
import, the local elaboration controls, the original 1,105 downstream importers, and
additional users found by the current preflight and source scan.
Unused structure-generator options were removed to retain the original public
structure API.

The required resumed dry run (`scratchpad/dry-run-recovered.log`) reported a fresh
reference clock, despite the retained work from earlier attempts, and rejected
three split holes at 0 of 120 minutes. The dispatch budget start is
1792432284.019502; earlier attempt logs include `dry-run-final.log` and
`dry-run-resume-latest.log`. The launcher metadata was not edited. Proof review,
compilation, definitional-equality checking and consumer checks continued.
Earlier compile transport failures have cleared. A previous preflight exceeded
its 900-second wrapper timeout; this continuation checks fresh delivery results
before repeating any operation. No push had occurred at that point.

The resumed server preflights identified additional textual users as the published
graph advanced. The change record now includes those users and their current
holders; no consumer implementation was changed. A trial privatization of the
interface imports failed with public-signature visibility errors, so their
original public visibility was restored and the interface recompiled successfully.

The corrected dry run passed at bb9001d53c. A subsequent delivery process
ended without output; a read-only remote check confirmed that no delivery
branch existed. The retry timed out compiling the interface before pushing.
Additional local irreducibility for the Hom and scalar-extension functors
prevented repeated unfolding in the presentation fields; the unchanged-signature
interface then compiled in 29.9 seconds. The final packet is revalidated before
the delivery retry.

Delivery tooling stopped after the final transparency repair: the required dry run
in `scratchpad/dry-run-transparency.log` was killed with exit code 137 before
printing a preflight result. A persistent retry also disappeared without producing
its recorded exit status or preflight output; process checks found neither wrapper
nor delivery process alive. No retry was started while an earlier process remained
active. The final seven-module compile passed in
`scratchpad/packet-final-transparency.log`. The last checked remote delivery branch
was absent, and no subsequent push command was issued. The packet is retained.

The 2026-10-20 continuation dry run reached the server preflight successfully
and identified 23 newly landed textual users missing from the change record.
All 23 have now been added with their current holders; their sources and
signatures are unchanged. The interface and all seven packet modules passed the
remote compiler after this audit. Renewed LeanFinder, Loogle and source searches
found general adjunction infrastructure and finite-coefficient derived tensor/Hom,
but no direct replacement for the independent-universe normalized comparison.
The retained signed-evaluation prototype was retried with explicit transparency
controls; it remains scratch work and is not part of this delivery. The repaired
2026-10-20 dry run passed all server checks at commit `fc97e73bfc` and classified
the packet CODEX for the required independent review; nothing was pushed by
that dry run.

The resumed dispatch checked the interrupted delivery logs before repeating any
mutation. The required fresh dry run (`dry-run-dispatch-current.log`) passed at
`2930d3aec7` with review class CODEX. All seven retained modules also passed the
current compile (`compile-dispatch-current.log`). The preflight reported that its
axiom probes for IntegralHomReduction, IntegralHomReductionModels and
IntegralHomRoosTransport timed out and will be rerun by the merge; this is not
reported as a completed axiom audit. The retained evaluation-normalization scratch
calculation was retried against current sources and remains outside the delivery.
The actual retained delivery still has the three named separate obligations above.

The 2026-10-21 repair addresses the return at head `995e342ab1`: the change
record now lists all six omitted quarantined consumers under `## Users`, with
current claim status and the unchanged-interface effect. Their archived Lean
sources, DAG attachments and dependencies are retained. No consumer is withdrawn
or adapted. The retained parent proof and three named remaining holes are unchanged.
The final seven-module remote compile, after both import-path repairs, passed on
2026-10-21; the log is `scratchpad/compile-return-source-repair.log`.
This repair adds no further holes. The earlier delivery invocation stopped at
its source gate on the obsolete HomComplexProjections import and pushed nothing;
that missing source import is now repaired.

## New nodes

`lem-sf-integral-hom-models-exist` isolates presentation construction, independently
of comparison invertibility and completeness.

`lem-sf-integral-hom-comparison-is-iso` isolates invertibility of the specified
comparison, independently of any completeness assertion.

`def-sf-integral-hom-reduction-models` attaches all 25 extracted interface
declarations, with unchanged signatures and public visibility. The only body
refactoring is the definitionally equal named factorization in `homModelMap`.

`lem-sf-integral-hom-tower-components` is the remaining finite-level compatibility
step for fixed representatives, including the quotient units and transitions.

`lem-sf-integral-hom-augmented-tower-comparison` is proved: a complex representative
and a K-flat resolution give a natural isomorphism assembled from the components.

`lem-sf-integral-hom-roos-transport` is proved: the normalized exact Hom functor
preserves the homotopy-limit cone, and product uniqueness identifies its resulting
triangle with the canonical Roos triangle. It adds no completeness assumption on K.

Change record: `coord/changes/IntegralHomReductionInterfaceExtraction.md`.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
