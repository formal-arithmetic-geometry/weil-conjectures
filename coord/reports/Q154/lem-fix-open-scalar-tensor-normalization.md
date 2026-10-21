## Worker report

The module `Sheaf.SixFunctors.OpenScalarTensorNormalization` states
`AlgebraicGeometry.ProEtale.OpenScalarTensor.open_scalar_tensor_normalization`.
Its single postponed proof has the complete eight-step adjunction proof in its docstring.
Every helper definition has actual data. The repair adds the existing-definition record
`def-sp-open-scalar-operations`; no dependency module or mathematical statement correction is needed.

The theorem supplies presentations of the already recorded universal derived operations:
`Models`, `Choices`, and `Normalization`. These are existential conclusions, not assumptions
on the rings, schemes, immersion, or complexes. `Models` uses the existing `ScalarHomModels`:
its scalar functors have the actual sheafified scalar-tensor object/map formulas, universal
left-derived property, and normalized ordinary and derived transposes. Its closed tensors
are the recorded signed K-flat total tensors and evaluation model. `scalarIso` identifies
each selected scalar presentation with the already published scalar functor by uniqueness
of its normalized adjunction. The helper `lambda` transports the existing canonical
`tensorPullbackIso`; it is not an arbitrary natural isomorphism. `beta` transports the published `openScalarIso` through `scalarIso` on X and U.
The published comparison is constructed by `Adjunction.leftAdjointUniq` from the two
composite adjunctions and the fixed restriction/pullback square, so B-linearity is
built into its module-category morphisms.

Hypotheses and clauses, exhaustively:

* Open immersion: every relevant clause binds `j : U ⟶ X` and `[IsOpenImmersion j]`.
  There is no quasi-compactness or separation hypothesis.
* Finite commutative rings and their map: clauses bind `[CommRing A] [CommRing B]`,
  `[Finite A] [Finite B]`, and `φ : A →+* B`. Composition also binds finite `C` and `ψ`.
* Ordinary unbounded pro-etale module derived categories: `proEtaleDerivedCategory T A`
  is the existing localization of complexes indexed by all integers over
  `proEtaleConstantRing T A`. There is no completion, constructibility, boundedness,
  flatness, perfectness, or finite Tor-dimension restriction. The small site's object
  universe is `u+1`, its morphism universe is `u`, modules are in `u+1`, and the standard
  localization is in `u+2`; these universes have not been equated.
* Scalar extension/restriction and exact open operations: `scalarPair` and `scalar`,
  the existing `scalarRestriction`, `openExtension`, `constantPullback`, and `openAdj`.
  `rightSquare` is the published identity-on-actions restriction/pullback comparison.
* The specified canonical lambda: `lambda`, as described above; direction in functor
  notation is `scalar X ⋙ constantPullback B ≅ constantPullback A ⋙ scalar U`.
* Natural B-linear beta: `beta` is a natural isomorphism in the B-module derived
  categories, from `openExtension A ⋙ scalar X` to `scalar U ⋙ openExtension B`.
* Its inverse-open-adjunct formula: `Normalization.beta_inverse` states precisely
  `homEquiv beta.inv = scalar U .map (openAdj A).unit ≫ lambda.inv`.
* Its restricted constant-B projection formula: `Normalization.restricted_beta`.
  `coefficient` is restriction of the B tensor unit, hence the constant A-module B.
  `scalarProjection` is the specified scalar-adjunction transpose of the normalized
  scalar tensorator followed by scalar counit and right unitor. Its invertibility
  is asserted by `scalar_projection_isIso`; it is not a freely selected identification.
  `coefficientPullback` uses the identity-on-actions square and the strong inverse-image
  unit comparison. `restrictionOpen` is the fixed adjunction mate, and
  `restriction_open_isIso` asserts its invertibility. The displayed equation says that
  these canonical identifications take restricted beta exactly to forward gamma at B.
* Forward open projection gamma: `Projection.iso`. Its inverse is fixed, rather than
  chosen freely: `Projection.inverse_adjunct` is the open unit tensor identity followed
  by the inverse canonical restriction tensorator. This is the direction of the
  published projection isomorphism's inverse, as in Stacks 0E8I.
* Balanced coefficient associativity: `scalarComp` uses the existing
  `scalarHomExtensionComp`, with the constant-sheaf map-composition equality.
  `Normalization.coefficient_comp` is exactly successive beta equals composite beta
  under this balanced associativity. `scalarId` uses the existing
  `scalarHomExtensionId` and the constant-sheaf identity equality;
  `Normalization.coefficient_id` explicitly includes identity ring maps.
* Arbitrary second tensor factor: `Normalization.tensor_square` binds unrestricted
  `K : proEtaleDerivedCategory U A` and `Q : proEtaleDerivedCategory X A`.
  Its left side is scalar of gamma-A, beta at `K tensor r_A Q`, and open extension of
  the scalar tensorator then `1 tensor lambda.inv Q`. Its right side is the scalar
  tensorator on X, `beta K tensor 1`, and gamma-B. All maps have the exact endpoints
  in the node; no reduction to Q equal to the unit is made.
* Unit normalization: the tensorators are fixed on their actual K-flat representatives,
  `Choices.open_normalization` fixes the inverse-image tensorator, and `Projection`
  prescribes its inverse adjunct. The mixed square includes the tensor-unit case.

Dependency declarations read and used:

* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` (def-pc-sheaf-restrict-scalars).
* `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `AlgebraicGeometry.ProEtale.FiniteCoefficientModules` (underlying coefficient context).
* `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`:
  `AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso` (the
  projection whose inverse-adjunct normalization is recorded by `Projection`).
* `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`: `proEtale_extension_by_zero`, and
  the published ringed derived open adjunction inherited by `openAdj`.
* `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel` (unbounded universal scalar model).
* `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction` (normalized scalar adjunction).
* `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`:
  `SheafOfModules.SuccessiveDerivedQuotient.successive_derived_quotient_normalization`
  (balanced coefficient normalization, used by the proof).
* `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  its public specialized interface supplies `ProEtaleTensorModel` and
  `proEtaleCanonicalTensorComparison` for the actual small pro-etale site.
* `Sheaf.Paper.KFlatScalarComparisonNormalization`:
  `SheafOfModules.ScalarPullback.kflat_scalar_comparison_normalization`. The specialized
  `tensorPullbackIso` supplies the normalized lambda without equating site universes.
* `Sheaf.SecSmoothPurity.OpenScalarExchange`: `scalarExtension`, `scalarRestriction`,
  `constantPullback`, `openExtension`, `tensorPullbackIso`, `openScalarIso`, now recorded
  by `def-sp-open-scalar-operations`. `beta` transports `openScalarIso` to the
  normalized scalar presentation; the theorem `openScalarExchange` is not used.
* `Sheaf.Algebra.Homology.ScalarInternalHomData`: `ScalarDerivedPair`, `ScalarHomModels`,
  `ScalarHomTensorComparison`, `scalarHomExtensionComp`, `scalarHomExtensionId`.
* `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`:
  `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`
  supplies the monoidal coherence in proof steps 1 and 7--8.

The statement adds `def-sfb-scalar-hom-comparison-data` and the new existing-definition
record `def-sp-open-scalar-operations` to the live node's stmt_deps. The earlier packet's
`lem-sfb-scalar-tensor-comparison`, `lem-sfb-dc-hom-scalar-adjunction`, and
`lem-fix-open-scalar-exchange` edges are removed: their theorem conclusions are unused.
The existential `m` and `c` remain supplied by this item. No dependency node is edited.

Edge cases checked against the actual formulas before finishing: empty open U (both
open extensions are zero), j the identity (open units and projection reduce to unitors),
identity coefficients A=B (explicit coefficient_id), zero rings (no nontriviality
assumption), Q the tensor unit (the normalization case), nonflat Z/4 → Z/2 (derived
scalar/tensor functors, no ordinary-flat substitution), and unbounded K,Q. Composition
includes either or both coefficient maps being identities. No STATEMENT-DISPUTED fault.

Searches (no exact existing declaration found):

* msearch LeanFinder, `Derived scalar extension commutes with open extension by zero and
  preserves projection tensor maps`: eight hits, chiefly underived
  `ModuleCat.extendScalarsComp_hom_app_one_tmul`, `extendScalars_assoc'`; no derived open square.
* msearch Loogle, `"extendScalarsComp", "tensor"`: zero hits.
* msearch grep, `extensionByZero.*[Tt]ensor|[Ss]calar.*[Ss]hriek|[Ss]hriek.*[Ss]calar`:
  zero Mathlib hits.
* msearch LeanSearch, `Derived scalar extension commutes with open extension by zero with
  tensor and coefficient composition normalization`: eight hits, chiefly
  `ModuleCat.ExtendScalars.obj'`, `smul_tmul`, and unrelated scalar constructions.
* Repository rg searches for the item id and open/scalar/tensor patterns in
  `lean/WeilConjectures` and `lean/Sheaf`: the item id occurs in the consumer docstring
  `Sheaf/Paper/ReductionOpenEtaleOrigin.lean`; no theorem states all these clauses.
  `OpenScalarExchange` supplies beta/lambda, but not the restricted constant-B clause,
  coefficient cocycle/identity, or arbitrary-Q tensor square. The existing open projection
  supplies gamma, and is reused through its precise inverse-adjunct normalization.

Source checked locally: sites-cohomology.tex Tag 0GL1, and sites-modules.tex Tag 0E8I
(the Yoneda chain fixes the inverse projection), together with the full node's eight
proof steps and all direct dependency statements/declaration signatures/docstrings.

## Second reading by Q154

A separate sequential self-review compared the full node and all fields of Normalization;
no independent worker was started, as the dispatcher explicitly prohibits other agents
and assigns the maintainer's independent review to the delivery. This section records
that limitation rather than claiming a second person reviewed it.

During elaboration review I corrected the K-flat predicate universe order to
`.{u+1, u, u+1}` (site objects, site morphisms, coefficients), and made the adapter
functor type explicit. This preserves the original site and changes no hypothesis.
A short line was split to meet the 100-character convention.

Checked every composite endpoint and direction: lambda inverse is used in beta_inverse
and the arbitrary-Q square; Projection.iso is forward gamma, while its prescribed adjunct
belongs to its inverse. The scalar-restriction clause includes both the scalar tensor
identification and the open/restriction mate. Coefficient identities are explicit and
not inferred merely from a cocycle without its unitor. Every binder and universe is
explicit with autoImplicit disabled. No new assumption on geometric or coefficient data
was introduced. The only sorry is the named main theorem with its full proof docstring.

Prior packet validation: scompile.py compiled the module cleanly. At the beginning of
this repair, the saved packet also passed deliver2.py --no-push (6362e450a82). That
mechanical pass did not repair the independent return; the changes below do.


## New nodes

`def-sp-open-scalar-operations` records the existing declarations in
`Sheaf.SecSmoothPurity.OpenScalarExchange`, lines 42--129. Its primary declaration is
`AlgebraicGeometry.ProEtale.openScalarIso`; `lean.declarations` also names
`scalarExtension`, `scalarRestriction`, `constantPullback`, `openExtension`, and
`tensorPullbackIso`, all in `AlgebraicGeometry.ProEtale`. The record has `existing: true`;
no module or definition is duplicated. These are exactly the underlying constant-ring
operations and canonical comparisons required by the item. The theorem in their owning
module is not needed to state this item.

Each part of the definition node matches the existing signatures: `A B : Type u` with
commutative-ring instances and `φ : A →+* B`; scalarExtension and scalarRestriction
are respectively the ring-sheaf derived extension and the exact restriction functor
localized termwise. `T : Scheme.{u}` specifies their small pro-etale site. For any
`f : U ⟶ X`, constantPullback is the exact derived inverse image using the canonical
constant-ring comparison; tensorPullbackIso is the inverse scalar mate of the
identity-on-actions square. For `j : U ⟶ X` and `[IsOpenImmersion j]`, openExtension
is the recorded exact derived open extension and openScalarIso is its composite
left-adjoint-uniqueness comparison. The definitions have no finiteness restriction,
and therefore specialize to all the finite coefficients of this item. The new node's
statement introduces no additional coherence theorem.

Searches for the new definition record (2026-10-21):

* msearch LeanFinder: `Constant coefficient scalar extension restriction inverse image
  and extension by zero on pro etale derived module categories and their common right
  adjoint isomorphism`: eight hits, ordinary ModuleCat scalar adjunctions and one
  Condensed counit, none for these pro-etale operations.
* msearch LeanSearch: `Derived scalar extension restriction of scalars open immersion
  extension by zero canonical comparison`: eight hits, ordinary scalar restrictions
  and ModuleCat scalar adjunctions, none for these derived open comparisons.
* msearch grep: `openScalarIso|scalarExtension|scalarRestriction|constantPullback|tensorPullbackIso`:
  five hits, all Mathlib.CategoryTheory.Monoidal.Mod scalarRestriction declarations.
* rg in `lean/WeilConjectures` found no declarations with these names; rg in `lean/Sheaf`
  found the six existing definitions in OpenScalarExchange. Full signatures, bodies,
  and docstrings at lines 42--129 were read. DAG exact declaration binding search found
  only the parent theorem's auxiliary declaration list, with no independent definition
  node. `tools/blueprint_refs.py search 'open scalar'` found only
  lem-finite-compact-support-scalar-transport, which is a different theorem.

The new node retains the raw msearch hit-name lists in mathlib_searches, and cites the
existing general operations, restriction, scalar adjunction, change-of-rings square,
open immersion and open extension nodes. Its blueprint ancestor is
lem-fix-compact-support-coefficient-change with this item prefixed to via.

## Repair of return 0dc45a25334e

1. Added def-sp-open-scalar-operations with existing:true records on all six existing
   data declarations, and replaced the lem-fix-open-scalar-exchange statement edge with
   this definition edge. No use of the openScalarExchange theorem conclusion remains.
2. Removed lem-sfb-scalar-tensor-comparison and lem-sfb-dc-hom-scalar-adjunction from
   stmt_deps and removed their two imports. Kept def-sfb-scalar-hom-comparison-data,
   which owns ScalarHomModels and ScalarHomTensorComparison used by the statement.
3. Replaced beta's fresh leftAdjointUniq construction with
   `isoWhiskerLeft (openExtension (A := A) j) (scalarIso m φ X) ≪≫
   openScalarIso φ j ≪≫
   isoWhiskerRight (scalarIso m φ U).symm (openExtension (A := B) j)`.
   This has the same direction and endpoints
   as before and reuses the published comparison itself.

For the advisory on Projection, its docstring now explicitly names
`derivedOpenImmersionLowerShriekProjectionIso` and
`derivedOpenImmersionLowerShriekProjectionMap`. I read their full signatures and bodies:
the published iso goes from open extension of tensor to tensor with open extension,
so Projection.iso has the reverse direction. Its inverse_adjunct is exactly the
published projectionMap construction, transported to the selected tensor and
constant-ring module presentations. This pinning was independently accepted in the
return; no extra hypothesis or auxiliary unproved identification was introduced.

The repair self-review rechecked the empty open, identity immersion, zero coefficients,
identity scalar maps, nonflat Z/4 → Z/2 and arbitrary unbounded Q. The whiskered scalarIso
maps only change universal presentations, so no case is excluded. The theorem signature
and every field of Normalization are unchanged; there is still exactly one sorry, the
main named theorem. The live node differs from the saved packet only in lean and the
extra statement dependencies, and the live module is not yet present. The wrapper rebases
the delivery against current main. No shared source or git state was edited directly.


Repair validation: after making both whiskered open functors explicit to avoid expensive
endpoint inference, scompile.py compiled the final sandbox and library module cleanly
in 47.4 s and 46.8 s respectively. There were no errors or warnings. The earlier implicit
transport exceeded the library's 60-second limit, and was repaired without changing any
signature. deliver2.py --no-push then passed preflight and both the module compile and
existing-definition declaration check at c5a853508d3. The signature in the node is verbatim,
the source has one named theorem with sorry, no line exceeds 100 characters, and only lean
and stmt_deps of the existing item differ from the current live node. The final report
update records these results; the push wrapper rechecks the resulting packet.
