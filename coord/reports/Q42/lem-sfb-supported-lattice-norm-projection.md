## Worker report

Item: lem-sfb-supported-lattice-norm-projection. Stage 2, group Q42, 2026-10-22.

The module `Sheaf.Paper.SupportedLatticeNormProjection` states
`AlgebraicGeometry.ProEtale.supportedLatticeNormProjection_isIso`, with proof `sorry`.
It constructs the integral coefficient ring, its actual rationalization map, the
embedded finite-field inclusion into the normed algebraic closure, and the actual
supported rationalized degree-zero object. It then uses the existing
`FieldActionTransport.pointProjection`, specialized to canonical normalized data.
There are no new axioms and no proofs supplied. The two auxiliary uniqueness
obligations belonging to the new definition node also have `sorry` proofs.

The node's statement, source and proof are unchanged. Its statement dependencies
add the new construction node and the already recorded definitions actually used:
`def-sfb-locally-closed-coefficient-extension`,
`def-sfb-field-action-geometric-transport-data`, `def-sfb-field-action-transport-data`,
`def-sfb-norm-continuous-monodromy-data`,
and `def-sfb-continuous-map-condensed-ring-map`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Distinct primes p and ell: `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)`.
- Separably closed K of characteristic p: `(K : Type u) [Field K] [IsSepClosed K]
  [CharP K p]`. The statement imposes no perfection or algebraic closedness on K.
- Algebraic closure Omega of Q_ell, with the extended norm: `(Ω : Type u)
  [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]`.
  `NormedAlgebra` already includes the Q_ell algebra structure and expresses the
  norm extension. The independent redundant Algebra binder was removed after the
  compiler's overlapping-instance diagnostic. The norm-algebra field embedding
  is isometric. No CompleteSpace instance is requested.
- Finite extension E inside Omega: `(E : IntermediateField ℚ_[ℓ] Ω)
  [FiniteDimensional ℚ_[ℓ] E]`. IntermediateField gives the actual inclusion and
  inherited norm topology; this covers every finite embedded extension.
- O_E is exactly `Padic.coefficientExtensionIntegers ℓ E`, the dependency's
  valuation subring defined from the unique extended spectral absolute value.
  Uniqueness of the extended norm identifies its unit ball with the induced norm
  unit ball. Its ordinary Subring topology is the subspace topology from E.
- O(P)=C(P,O_E): `supportedLatticeIntegralRing` explicitly uses
  `Profinite.continuousMapRingObjOfUniverse` and its recorded monoid and
  commutativity structures. A(P)=C(P,E) and B(P)=C(P,Ω) use the existing
  `FieldActionTransport.normCoefficients`. These constructions lift the section
  universe only; none restricts the image to a finite subextension.
- O to A and A to B: `supportedLatticeRationalization` and
  `supportedLatticeNormInclusion` use the existing continuous-map morphism
  construction, respectively with the actual valuation-subring inclusion and
  `algebraMap E Ω`, both with `continuous_subtype_val`.
- Pulled-back coefficients R_Y: `CondensedGalois.Modules R.toMon Y` is exactly
  `Mod (Sheaf (Scheme.ProEt.topology Y) Ab) (coefficientRing Y R.toMon).X`.
  The existing `coefficientRing` transports R along the actual `upperStarFromPoint`.
- Internal modules and ordinary unbounded derived categories: the above `Modules`
  and `DerivedCategory.{u + 2}` use the recorded internal-module and localization
  constructions. The object site has universe u+1 and morphisms u; these are not
  forced equal. Coefficients and the chosen base field lie in the common universe u.
- T separated of finite type over K: `T : Over (Spec (.of K))` with
  `[LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]`.
  The first two classes together express finite type.
- Constructible locally closed immersion a:S to T: `(a : S ⟶ T.left)
  (ha : IsImmersion a) (_hconstructible : Topology.IsConstructible (Set.range a))`.
  No separate finite-type or separatedness assumptions are imposed on S.
- L_0 lisse of finite rank: `L₀ : Modules (supportedLatticeIntegralRing ℓ E).toMon S`
  and `_hL₀ : IsLisseCoefficientModule ... L₀`. Reading the definition and
  `Mod.IsFree` confirms finite ranks varying over the trivializing cover and rank 0.
- a_!=i_*j_!: `coefficientHeartLocallyClosedExtension ... a ha` uses `a.toImage`
  and `a.imageι`, the canonical open-into-closure/closed factorization. Its body is
  exactly `openImmersionLowerShriek ⋙ lowerStar`. The finite-type hypotheses
  supply the Noetherian structure within `supportedRationalizedLattice`; they
  are derived properties, not extra theorem assumptions.
- Q=A_T tensor_{O_T} a_!L_0 in degree zero: `supportedRationalizedLattice` first
  applies that exact support functor to L_0, then ordinary `extend` along
  `supportedLatticeRationalization`, then `(DerivedCategory.singleFunctor _ 0).obj`.
  In particular this is ordinary rationalization after support extension, not
  an unexplained replacement by a merely isomorphic object.
- H_R=Rp_{T*,R}: `pointProjection` uses `(CondensedGalois.pointModules R.toMon
  T.left).rightDerivedFunctor`. The underived functor is the complete point
  direct-image/mapMod/scalar-restriction composite. It is derived as a whole,
  using ordinary module K-injective resolutions, not derived factors.
- B tensor^L_A and B_T tensor^L_{A_T}: `pointProjection` uses the existing
  `condensedDerivedExtend` and `derivedExtend`, the actual total left derivations
  of internal `Mod.extendScalars`, with their K-flat scalar adjunctions.
- Specified map, not just endpoints: `pointProjection φ T.left
  (canonicalPointScalar φ T.left) Q` is the recorded geometric-counit adjunct of
  the scalar/pullback comparison followed by scalar extension of the counit.
  The canonical data's normalization fixes exact localization of `mapModComapIso`;
  its transpose equation fixes both scalar units and counits. Therefore it is
  equivalently the scalar-adjunction transpose of H_A of insertion of 1. Its
  flat-term K-flat formula is q maps to 1 tensor q. No comparison map is a
  parameter or hypothesis of the final theorem.
- Conclusion: `IsIso (...)` asserts invertibility of that specific morphism in
  `DerivedCategory (Profinite.CondensedAction.Modules (normCoefficients Ω).toMon)`.
  This is an assertion about the derived morphism itself, not only its cohomology.
- No unrestricted constructible-complex theorem or arithmetic Galois comparison
  is asserted. No coefficient flatness or completion is assumed.

Dependency declarations read and used (full signatures and docstrings were opened):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` reexports
  `Padic.coefficientExtensionIntegers` and its spectral absolute-value construction.
- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingObjOfUniverse`,
  `continuousMapRingObjOfUniverseMonObj`,
  `isCommMonObj_continuousMapRingObjOfUniverse`.
- `Sheaf.Topology.ContinuousMapCondensedRingMap`:
  `Profinite.continuousMapRingObjMapOfUniverse` and its IsMonHom theorem.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`,
  `upperStarFromPoint` and preservation of commutative ring objects.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  the recorded total-derived convention; the actual modules here are Grothendieck,
  so their existing `rightDerivedFunctor` specializes the same convention.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` and
  `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  ordinary K-flat relative derived tensor and its scalar adjunction.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`:
  `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`.
- `Sheaf.Paper.CondensedOpenClosedRecollement`:
  `AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_closed_recollement`;
  its exact support functors are those already used in the support construction.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`;
  the point version uses the identical total-derived convention on pointModules.
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`:
  `sfbPullbackFromPoint`, `sfbPullbackFromPointRightAdjoint` and their specification.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  the recorded finite locally closed scheme-stratification notion, retained as
  the node's given background statement dependency; no new stratification is assumed.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`; the closure construction uses precisely these.
- `Sheaf.Paper.CoefficientHeartFiltration`:
  `AlgebraicGeometry.ProEtale.coefficientHeartLocallyClosedExtension`.
- `Sheaf.Paper.NormContinuousMonodromyData`: `normContinuousRing` and its
  commutative ring structure;
  `Sheaf.AlgebraicGeometry.FieldActionGeometricTransportData`: `normCoefficients`,
  `PointScalar`, `pointProjection`, the actual normalized counit-adjoint morphism.
- `Sheaf.AlgebraicGeometry.FieldActionTransportData`: `PointAdjunctionData`,
  `pointPull`, `pointDerivedAdjunction`, `extend`, `derivedExtend`,
  `condensedDerivedExtend`, and their fixed ordinary/derived scalar adjunctions.

The stated proof-dependency modules are imported privately, including the proper,
open, countable-basis and geometric-fibre inputs. The currently unstated
`lem-sfb-tame-pair-proper-generators` has no recorded module and cannot be imported;
its step remains explicitly present in the main theorem's proof docstring.
No existing node or Lean module for another worker was modified.

Edge cases checked before writing: S empty, T empty, L_0=0, varying local rank and
rank 0. There is no Nonempty, ConnectedSpace or positive-rank binder. The support
functors, ordinary scalar extension, degree-zero functor and derived functors all
send zero to zero, so the displayed morphism is the unique isomorphism on zero.
E=Q_ell and arbitrary finite embedded E are permitted. Omega is only an algebraic
closure with its extended norm, with no completeness assumption.

Searches:

- msearch leanfinder: "The derived coefficient projection from continuous l-adic
  field coefficients to continuous algebraic closure coefficients is an isomorphism
  for the cohomology of a supported rationalized lisse lattice" returned eight
  continuous/group-cohomology matches; none states this supported-lattice result.
- msearch loogle: "CategoryTheory.Mod, DerivedCategory" returned 0 hits.
- msearch grep: "coefficientProjection|supportedLattice|normProjection" returned 0 hits.
- msearch leansearch: "Canonical scalar extension comparison for pullback of module
  objects along a monoidal functor" returned eight general sheaf-module or
  constant-coefficient scalar-change matches, no canonical point data.
- msearch leanfinder and grep for the canonical point data are recorded with their
  exact outputs in the new node's mathlib_searches.
- rg in both project Lean roots and Mathlib found no declaration under any of the
  nine newly introduced names. Searching the item id in WeilConjectures found none.
  Concept searches found the existing FieldActionTransport interfaces, which are used.
- DAG grep and `tools/blueprint_refs.py search 'point scalar'`: no existing canonical
  point scalar construction node; the blueprint search returned 0 matches.
- A dependency-path audit from the added recorded definitions to the item found no
  path, so the new helper introduces no dependency wait or dependency cycle.

The source explicitly labels the all-continuous incomplete-coefficient literature
proof WANTED. That limitation is retained in the main theorem docstring; the
statement is not attributed to HRS Lemma 7.9. No concrete counterexample or
ill-typed mathematical clause was found, so no statement correction is made.

## New nodes

`def-sfb-canonical-point-scalar-comparison` constructs the canonical normalized point
adjunction and point scalar square for every commutative condensed coefficient and
scheme. It uses the existing `PointAdjunctionData` and `PointScalar` types and the
existing `pointProjection`; it does not copy any of those definitions. The previous
interfaces only specify compatible data and explicitly make no existence assertion.
This node supplies their unique canonical inhabitants, with named construction
obligations and complete proof plans. The first uniqueness theorem fixes the actual
module adjunction by its underlying geometric unit/counit; the second fixes the
scalar square by its prescribed restriction and all Hom transposes. The definitions
choose only from these uniqueness assertions, so the selected data are determined
up to equality. The source is the direct-images paragraph (3) canonical point
coefficient projection, with the elementary monoidal-module adjunction construction.
The three kinds of searches, plus the DAG search, are recorded in the new JSON.

`def-sfb-locally-closed-coefficient-extension` owns the already existing
`AlgebraicGeometry.ProEtale.coefficientHeartLocallyClosedExtension` in
`Sheaf.Paper.CoefficientHeartFiltration`, recorded with `existing: true`.
For commutative condensed coefficients, a topologically Noetherian target and an
immersion, it is exactly open extension along `a.toImage` followed by direct image
along `a.imageι`. The statement names those canonical arrows and both module
functors; it imposes no lisse or constructibility restriction. This is the support
construction used in the direct-images paragraph (3), before rationalization.
The theorem nodes mentioning it do not own a definition node for this notion.
LeanSearch and LeanFinder returned scheme structure-module restriction functors,
not this internal coefficient construction; Mathlib and WeilConjectures grep had
no matches. Sheaf grep found the exact existing definition, so no new Lean module
or copy is supplied. Exact search-service records are in `mathlib_searches`.
The four statement dependencies own the open/closed immersion notions and the
actual open extension and direct image functors. Empty schemes and zero modules
are covered; Noetherianity is the existing definition's topological assumption,
and follows from finite type in the consuming item.

## Second reading by Q42

I reopened the completed node records and both modules for a second pass. This is a
self-review by the dispatched worker; no independent worker review is claimed.
The maintainer's independent review remains the delivery review specified in the brief.

The second pass checked the prime, characteristic, separable-closedness, finite
embedded extension, induced norm topology, finite-type/separated scheme, constructible
immersion and finite-rank lisse binders against the unchanged node. It checked the
construction order support extension then ordinary rationalization then degree zero.
It also traced the conclusion to the existing pointProjection definition and its
canonical scalar/counit normalization. The initial canonical data were absent from
the library, so the new definition node supplies their unique inhabitants instead of
assuming them in the theorem. Compiler fixes changed an IntermediateField inclusion
to the explicit `algebraMap E Ω`, qualified `Topology.IsConstructible`, marked the
canonical class-valued definition instance-reducible, and removed a redundant algebra
instance. None changes the mathematical hypotheses or conclusion. Both definitions'
choices are justified by equality uniqueness, and all three postponed theorems are
recorded under their owning DAG nodes with natural-language proof plans.

Validation: scompile.py compiled each module separately, including its named library
module, with no errors or warnings. Final delivery dry-run results are recorded below.

Final dry run: `deliver2.py Q42 lem-sfb-supported-lattice-norm-projection --no-push`
returned `OK (dry run): commit 21d713a5370 passes the preflight and compiles; nothing pushed`.
Its staged set contained exactly the two Lean modules, the item and new definition
node JSON files, and this report. The final scompile pass checked both modules in
isolation and their named library modules, without errors or warnings.

## Returned delivery repair

The independent review of immutable head `83060bea33a5` accepted the complete
clause check and the canonical-data construction, but returned H3 because the
worker-added theorem dependency `det-lem-coefficient-heart-filtration` only
provided a plain helper definition. The saved packet's first dry run passed
mechanically at `2ba91d97369`; this does not discharge that semantic return.

Repaired H3 by introducing the definition node
`def-sfb-locally-closed-coefficient-extension` with an existing declaration record,
and replacing that worker-added theorem dependency in the item. The original
base dependencies remain. Reopened the full definition and its docstring: its
body composes the actual two functors and makes no theorem choice. Reopened the
four dependency statements and the open-extension/direct-image definitions.

Addressed both advisories: the item now directly cites and publicly imports
`def-sfb-field-action-geometric-transport-data` and
`def-sfb-field-action-transport-data`; the report attributes `normCoefficients`
to `Sheaf.AlgebraicGeometry.FieldActionGeometricTransportData` and `extend` to
`Sheaf.AlgebraicGeometry.FieldActionTransportData`. The former wraps
`normContinuousRing` from `NormContinuousMonodromyData`.

Self-check against current main: the saved item differs only in `lean` and
worker-added `stmt_deps`; its statement, source and proof equal current main.
The theorem signature and all mathematical definitions are retained from the
reviewed packet. Reread both modules, the new ownership node and the repaired
item record. Every original hypothesis and conclusion still has the correspondence
listed above; this repair changes only ownership/dependency records and explicit
imports. The new definition node's signature is verbatim from the existing module,
with its section coefficient/monoid/commutativity binders made explicit in the
natural-language statement. No duplicate declaration or extra postponed theorem
is introduced.

Repair validation: `scompile.py` compiled both delivered modules separately,
including their named library-module forms, with no errors or warnings. The repaired
`deliver2.py --no-push` passed preflight and compilation at `e598518046d`.
Its staged packet contains both Lean modules, the item record, both new definition
node records (including the existing-definition attachment), and this report.
