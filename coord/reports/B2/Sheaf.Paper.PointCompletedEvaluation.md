## What changed

Repair of returned head `c03b7d88872`: its review answered FIX (it reverted the unforced
`sections` re-association in `PointDerivedHomModels`), but landing rejected a reviewer
correction filename. This re-delivery brought the re-association back; the reviewer of
`c68ffaf96f1` reverted it again, so `PointDerivedHomModels` is not changed. The change record is present at
`coord/changes/B2-point-completed-evaluation-canonical-map-api.md`.
The stage-3 lander requires its reviewer correction to be named
`B2-point-completed-evaluation-canonical-map-api.change.md`, as specified by
`tools/batch_land.py:fixes`; the bare `.md` correction name is rejected.
The record now includes that exact correction alias and a refreshed, complete Users
table, including H3's current
ownership of `CompletedHomScalarTranspose`. No consumer source is changed. The retained
Lean proof and node changes are rebuilt on current `sheaf-dag` by the delivery tool.
For this repair, `LCOMPILE_NO_LOCAL=1 lcompile.py --all` returned exit code zero
for all four delivered Lean modules on the project server.

Filled `WeilConjectures.PointCompletedEvaluation.point_completed_evaluation` by assembling
its stated coefficient-adjunction, projective-model, and completion-normalization results.
The normalized finite-projective adjunction units give the actual chain isomorphism
`P ≅ Γ(model P)`. Uniqueness identifies the completion theorem's balancing isomorphism
with the item's fixed `towerBalancing`. The pairing identity, inverse tensor comparison,
exact-sections naturality, and localization tensorator naturality give the final equation.
The main theorem statement is unchanged. Its `Result` predicate groups its six
unit, Hom and ordinary normalization proofs into `PointPerfectOrdinaryEvaluation.Normalized`.
This is precisely the conjunction of the original formulas, with the same data.
Expanding it and distributing conjunction recovers the original existential statement.
The extension functor and its unique-existence theorem are unchanged. A proved
`extension_spec` API states the same object, additive and map laws for the named
functor, which is locally irreducible afterward. Completed evaluation
uses the existing pairing with the fixed balancing isomorphism; functor composition
recovers its original formula. Repeated definitions alias the definitionally identical
normalization and projective-model constructions. The generator uses the existing
generator with the equality proof supplied by `extension_spec`; proof irrelevance
identifies it with the original choice-specification proof. The balancing hole uses the existing,
definitionally identical `Balanced` predicate. The unused `roosBalancing` wrapper is
removed. Direct choice from unique existence gives the same tower isomorphism by
uniqueness. Large map definitions have proved private APIs. The repeated complex-model abbreviations alias the same existing constructions. Public imports
expose constructions used by public definitions; other added imports are private.

Added `Sheaf.Paper.PointPerfectOrdinaryEvaluation` for the ordinary chain calculation
between the actual projective Hom model and `R[0]`. Its coefficient isomorphism comes from
the bijective scalar map. Its Hom comparison postcomposes the ordinary Hom adjunction with
the inverse coefficient isomorphism. Its evaluation maps come from the existing signed
sheaf and module evaluation constructions. The square is proved on pure tensors in each
total summand. This calculation involves no completion or derived tensor comparison.

Normalized five alias bodies (`B`, `Modules`, `coefficient`, `sheafValue`, `model`) in the
unclaimed `Sheaf.Paper.PointProjectiveDualTensorModels`. They now name the existing
completed sheaf, module category and ring unit directly, preserving the same objects
by definitional equality. That module's theorem statement and entire proof are
unchanged. Its only direct consumers are this packet's parent and ordinary module.
The termwise model applies `L.mapHomologicalComplex` directly with the same additive
proof as the old wrapper. The original unit now has an explicit, definitionally identical
point-sections codomain. Its body is unchanged. Proved `unit_apply` and `unit_isIso`
interfaces let the parent use its normalization and invertibility without unfolding
that unit. The producer node records these APIs and the point-sections dependency. The change record includes the old and new bodies and consumer inventory.

The producer's proved `scalar_eq`
identifies its generic final-object scalar map with the actual integral section map.
The parent uses that equality to transport bijectivity explicitly. The producer's
`unitIso` names the same canonical `asIso` value; its proved `unitIso_apply` supplies
the original generator normalization. This keeps the actual chain isomorphism abstract
in the parent's completed diagram. The inverse is uniquely determined by its unit.

The parent DAG proof and proof dependencies now describe this route. Locally irreducible
category constructions prevent expensive unfolding during the categorical calculations.
The private `result_of_models` lemma supplies the predicate constructor.
Four proved private categorical lemmas handle completion-unit cancellation, tensor transport,
functorial congruence, and the inverse-comparison argument with abstract objects; the application supplies
all representatives explicitly. Proved private interface lemmas cancel the tensor
comparison and recover the completion unit. The proof first identifies the adjunction object specification with the canonical
one by proof irrelevance, so every model uses that same specification. It then identifies the unique balanced
map directly and transports the pairing equality once.
The `towerBalancing`, `completedEvaluation`, and `tau` definitions are irreducible
with proved interfaces, preventing repeated expansion of strict towers. The termwise
unit is locally irreducible in the parent, with its new normalization and isomorphism APIs.

Validation: the three changed Lean modules (projective models, ordinary evaluation,
completed evaluation) compile against the published, unchanged `PointDerivedHomModels`.
The completed-Hom consumer `CompletedHomScalarTranspose` compiles unchanged against both
this packet and the published parent (reviewer, lcompile.py). No consumer adaptation or
consumer source is delivered. The main theorem signature and the original projective-model
theorem statement and proof are unchanged.

## Proved and sorry left

Closed: `WeilConjectures.PointCompletedEvaluation.point_completed_evaluation`
(node `lem-pod-point-completed-evaluation`).

Remaining original hole:
`WeilConjectures.PointCompletedEvaluation.towerBalancing_existsUnique`
(node `lem-pod-point-completed-evaluation`). Its predicate uses the existing `Balanced`
definition and is definitionally identical to its original statement; its proof docstring is unchanged.

The additional projective-model module has zero holes,
before and after.
The delivery adds no holes.
`WeilConjectures.PointPerfectOrdinaryEvaluation.point_perfect_ordinary_evaluation`
and its private helpers are proved. Thus one of the item's two original holes is closed, with zero split-off holes.
The existing dependencies may still contain their own named holes; this proof uses their
stated interfaces as instructed.

## No longer needed

The parent does not use `PointDerivedHom.point_derived_hom_evaluation` or its
K-injective replacement machinery in either its definitions or proof. The direct public
import of `PointDerivedHomEvaluation` is removed. Its model definitions remain publicly
available through `PointProjectiveDualTensorModels`. This removes the modules
`PointDerivedHomEvaluation`, `PointExtensionKFlat`, and `PointTensorHomEvaluation` from
this parent's import closure. Other modules still use them; no withdrawal is claimed. The ordinary calculation uses `PointHomComplexAdjunction`, `PointSheafHomMaps`,
and `ModuleHomSignedEvaluation` on the actual perfect models.

`def-weil-derived-pullback-tensor-hom` is no longer a direct parent proof step: the
completion theorem gives the pairing equation for the explicit completed evaluation.
Its unused direct public import is also removed, while it remains transitively imported
through the required point-tensor interfaces. Neither removed theorem is an actual
statement dependency of this parent's formulas, so their statement-dependency entries
are removed as well. No module is deleted or globally declared unnecessary.
The unit route is preserved.

The unused public wrapper `PointCompletedEvaluation.roosBalancing` is removed.
The existing completion-pairing construction already uses that same Roos map.
No downstream module mentions the wrapper. Its parent-node declaration attachment
is removed; no node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned invocation of ordinary derived Hom evaluation
has a K-injective target, while this item's normalized formulas concern the specific
coefficient complex and the specific finite-projective dual model. The new ordinary
lemma supplies precisely that chain-level interface without changing either statement.

Edge cases of the new lemma were checked in the argument: the zero complex, a single
free module in any integer degree, vanishing total degrees, and both signs in negative
degrees. Outside total degree zero the evaluation target is zero. The scalar bijection
is used explicitly, so no constant-section inverse is chosen without an isomorphism.
No data definition contains a hole or chooses an undetermined existence witness.

## New nodes

`lem-pod-point-perfect-ordinary-evaluation`, implemented in
`Sheaf.Paper.PointPerfectOrdinaryEvaluation`, is the ordinary signed evaluation square
of parent proof step 3. It assumes the given Hom-model and unit normalizations and
constructs the coefficient isomorphism, Hom comparison, and evaluation maps. It asserts
neither perfect-model existence nor constructibility, completeness, tower balancing,
completion units, tensorator normalization, or the parent's derived square. Its docstring
contains the construction and complete proof. The node records the source, dependencies,
and three kinds of Mathlib search. The canonical-map interface refactor is recorded in
`coord/changes/B2-point-completed-evaluation-canonical-map-api.md`. The only downstream
module, `CompletedHomScalarTranspose`, requires no adaptation. No mathematical condition or specified morphism changes.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
