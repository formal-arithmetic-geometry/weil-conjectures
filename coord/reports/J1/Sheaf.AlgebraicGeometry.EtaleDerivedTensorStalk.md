## What changed

Proved `AlgebraicGeometry.Etale.exists_derivedTensor_stalk_iso` from the already proved
source-library tensor comparison. The geometric stalk preserves flat objects by the
geometric-fiber criterion and the canonical comparison with the lifted point. The public,
fully proved `exactFunctor_tensor_comparison` transports the derived comparison through
`leftDerivedFunctorIsoMapDerivedCategory`, and proves both naturality and the complete
normalization equation using the source counit square.

The expanded concrete signature repeatedly exceeded the normal 60-second limit, although
its abstract proof compiled. It is now packaged as the irreducible proposition
`ExactFunctorTensorComparison`, defined by precisely the original clauses. Its proved
`exactFunctorTensorComparison_iff` exposes all clauses, and its proved `exists_iso` accessor
exposes the objectwise isomorphisms. The theorem's geometric-point parameters and
mathematical meaning are unchanged; `derivedTensor` is definitionally `curriedTensor`.
This definition contains neither chosen data nor a hole. No file or proof was split to
avoid the limit. The item compiled cleanly during development; the final consumer checks took 22.9 seconds
for `GeometricStalkTensorConstantSingle` and 40.7 seconds for
`OpenTorBoundStalkFilteredExtension`. All use the normal 60-second limit.

Adapted the three direct consumers in their comparison construction only. Their existing
signatures, visibility and imports are unchanged. The adaptations use the proved generic
comparison and an explicit equality of tensor functors, mapped to an isomorphism by the
stalk functor. Proving the functor equality before projecting to objects avoids expensive
reduction of the derived tensor at concrete objects. The pointwise generic accessor takes
its derived objects first so their chosen category instances determine its specialization.
The interface repair and all twelve downstream modules are recorded in
`coord/changes/J1-derived-tensor-stalk-comparison-api.md`.
No source-library file, target statement, existing definition, or auxiliary instance changed.
The minimal public import of `Abelian.Flat.PreservesFlat` exposes the class used in the new
public generic theorem. The flat-preservation instance exposes the proved stalk criterion.

The two added private imports are
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat`.
The two comparison definitions are locally irreducible during the abstract proof; no
exported attribute is changed. The node now describes the implemented proof and interface.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.exists_derivedTensor_stalk_iso`
(node `lem-sfb-etale-derived-tensor-stalk`).
Added zero holes. Every delivered Lean module has zero `sorry` occurrences.
The transport theorem, both objectwise accessors and the clause-exposing iff are fully proved.
The new geometric-stalk flat-preservation instance is fully proved as well.
The three adapted consumers retain their complete proofs and have no remaining holes.
This is a proof, not a decomposition: no new unproved statement or proof obligation was added.

## No longer needed

Removed these eight private imports:

- `WeilConjectures.AlgebraicGeometry.GeometricStalkColimits`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `Sheaf.Paper.EtaleFlatKFlatResolution`
- `Mathlib.Algebra.Homology.Additive`
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`
- `Sheaf.Algebra.Homology.KFlat`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The tensor and module-category structures are already available through the public imports.
The ordinary stalk monoidality and point adjunction are proved source-library constructions;
the separate `EtaleStalkTensorScalar` statements are not used. The generic derived comparison
uses the source library's functorial flat resolutions, so this proof does not separately
invoke `EtaleFlatKFlatResolution`, either sheaf K-flat predicate, or a proof of preservation of
all K-flat complexes. The generic K-flat independence API remains available transitively.

Removed from this node's direct proof dependencies:
`def-kun-constant-sheaf`, `lem-weil-pbc-sheafification-geometric-stalk`,
`lem-weil-pbc-site-r-module-presheaf-sheafification-exact`,
`lem-pod-etale-stalk-tensor-scalar`, `def-pc-kflat-complex`, and
`lem-kun-flat-resolution-existence`, and `lem-kun-stalks-commute-colimits`.
Their separate assertions are not needed by this
specialization of the proved source comparison. Colimit preservation follows directly from
the point adjunction for arbitrary module coefficients, without the separate ℤ-specific
colimit theorem. Constants and flat resolutions used
internally by the source-library theorems remain part of those theorems' own dependencies.
No existing module or declaration is withdrawn; other consumers may still need them.
The unit's statement and proof route are preserved.


The four obsolete top-level `tool_uses` approvals for sheafification invariance,
sheafification exactness, the separate scalar tensor comparison and separate K-flat
resolution existence were removed from the node. Its derived-tensor independence approval
is retained. Historical split-report text remains unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan reconstructs machinery already proved in the source library's
`Functor.leftDerivedTensorComparison`. Preservation of flat objects suffices for its API:
its functorial flat resolutions have K-flat images. We therefore need neither a separate
proof that every K-flat sheaf complex has K-flat stalks nor the separate resolution theorem.
The lifted-point flatness criterion transfers to the unlifted stalk by `uliftSheafFiberIso`.

Earlier attempts were blocked by a temporarily unavailable published build. This session's
first delivery retries likewise received no compile-server answer, then the server resumed.
Subsequent 60-second timeouts were treated as definition-performance problems and repaired
by the named-proposition API, without changing the limit or the underlying constructions.
All retained comparison clauses, including the exact localization square, are proved.

## Forced adaptations

All three original consumers were compiled against the repaired item before adaptation.
Each failed with `Tactic rcases failed: ... is not an inductive datatype`, because the
comparison proposition is deliberately irreducible. Only the construction of the tensor
comparison is adapted; all signatures, visibility, imports and subsequent arguments remain.
The local equality `derivedTensor ... = curriedTensor ...` is proved by reflexivity at the
functor level. `congrArg` gives the object equality, and `mapIso (eqToIso ...)` supplies the
bridge to the existing proof's tensor object. Direct conversion at the object level exceeded
the per-file limit, so these bridge lines are necessary for the forced adaptation to compile.

- `Sheaf.Paper.OpenTorBoundStalkFilteredExtension` (unclaimed), original line 171:
  `obtain ⟨e, -⟩ := exists_derivedTensor_stalk_iso A t` failed on
  `ExactFunctorTensorComparison (Scheme.pointSmallEtale t).sheafFiber`.
  The changed block obtains the generic component at `Q` and the single sheaf, then composes
  it with the explicit tensor bridge. The following homology and single-functor comparisons
  are the original proof.
- `Sheaf.SixFunctors.GeometricStalkTensorConstantSingle` (unclaimed), original line 59:
  `obtain ⟨e, _, _⟩ := exists_derivedTensor_stalk_iso R x` failed on
  `ExactFunctorTensorComparison (pointSmallEtale x).sheafFiber`.
  The changed block obtains the comparison's objectwise family and bridges its source at
  `L` and the constant single object. The constant-stalk identification remains unchanged.
- `Sheaf.AlgebraicGeometry.EtaleStalkTorTest` (held by Q18), original line 106:
  `obtain ⟨e, _, _⟩ := exists_derivedTensor_stalk_iso A (S.algClosurePoint x)` failed on
  `ExactFunctorTensorComparison (pointSmallEtale (S.algClosurePoint x)).sheafFiber`.
  Only that tensor-comparison construction is replaced: the generic component and functor
  equality bridge precede the original single-functor comparison and homology argument.

## New nodes

`lem-sfb-exact-flat-tensor-derived-counit-comparison` records the fully proved generic exact-functor comparison and its
component accessor, in the existing item module. It isolates the source counit transport
used before geometric specialization; it introduces no hole and no new Lean module.
Its statement is tested on zero objects, the identity functor and arbitrary homotopy
pairs: the normalization uses noninvertible lax tensorators and does not assume those
pairs K-flat. The braidings need not be preserved by the functor.
The existing node imports this proved result in its dependency plan. The interface change
record is `coord/changes/J1-derived-tensor-stalk-comparison-api.md`.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
