## Worker report

The theorem `AlgebraicGeometry.ProEtale.CondensedRing.kummer_stratum_scalar_mate_detection`
states the identification of the actual geometric scalar mate on every Kummer stratum
cover and the resulting global isomorphism criterion. Its sole proof is `sorry`.
`KummerScalarStratumModel` bundles exactly the supplied representation, its two
all-continuous coefficient models, the two model isomorphisms, and their normalization
by the actual coefficient unit. All helper definitions have real data.

Hypothesis and clause correspondence:

* Distinct primes are `ℓ`, `[Fact ℓ.Prime]`, `p`, `[Fact p.Prime]`, and `_hpℓ : p ≠ ℓ`.
  The normed algebraic closure is the published `PadicAlgCl ℓ`, and the finite
  intermediate field is `E : PadicAlgCl.FiniteIntermediateField ℓ`.
* `k : Type u`, `[Field k]`, `[CharP k p]` render the characteristic-p base field.
  `Y.Over (Spec (.of k))`, `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`
  render the separated finite-type k-scheme. `_hY : IsRegularScheme Y` includes
  the node's local Noetherianity, rather than merely stalkwise regularity.
* `D : Y.IdealSheafData` and `hD : IsStrictNormalCrossingsBoundary D` give the
  finite reduced SNC divisor. `kummerComponents D hD` enumerates its actual
  irreducible component ideals; `ULift (Fin hD.2.2.choose)` changes only the size
  of this finite index set. `tameBoundaryOpen D` is the complement and `.ι` its
  open immersion. Quantification over `Finset` includes every component subset.
* `L` is a module on this complement over `(kummerCoefficientRing E.1).X` pulled
  back to W. `_hL : IsLisseCoefficientModule ... L` is precisely pro-etale locally
  finite free with variable finite rank, including rank zero.
* `kummerCoefficientRing` is the actual `C(-,F)` ring object with all continuous
  functions. `tameBoundaryScalarMap` is postcomposition by `E.1.subtype`.
  `KummerModules`, `DerivedCategory`, `tameBoundaryScalarExtension`,
  `moduleObjectDerivedPushforward`, and `derivedFromCondensed` are the recorded
  internal-module and ordinary unbounded derived constructions.
* `ParameterStratum (kummerComponents D hD) J` with its inclusion is the actual
  reduced locally closed stratum. For the empty subset its intersection is Y.
  `U J : Scheme.Cover Scheme.proetalePrecoverage ...` is the supplied pro-etale
  cover. `((U J).f j ≫ parameterStratumInclusion ... J)` is v_alpha.
  Covers are also provided on empty strata; they may be taken empty, so this
  adds no mathematical requirement to the nonempty-stratum formulation.
* The model's `representation` is `PartialKummer.FiniteRepresentation` of
  `kummerStratumInertia p J`, exactly the full product over q != p, including
  q = ell. `primeToEll` uses the recorded `KummerFinitePrimeToEllImage`, imposing
  the finite prime-to-ell image condition only on H_I. There is no faithfulness
  or finite-image requirement on the full inertia representation.
* `coefficients` uses `KummerCoefficientModels`, whose finite and closure
  objects are the actual two condensations of that representation, and whose
  unit is fixed by its coordinate insertion-of-one equation.
* The model's `finite` and `closure` are exactly phi_(alpha,E) and
  phi_(alpha,Omega), on the entire covering scheme, from `kummerOpenImage` to
  `kummerStratumPointObject`. The latter is the actual point pullback of
  `CondensedDerivedRestriction.derived` applied to the degree-zero action.
* `normalized` states equality of the coefficient-unit-induced open-image map
  followed by scalar restriction of `closure.hom` and `finite.hom` followed by
  `kummerStratumPointUnit`. That last arrow is pullback of the actual invariant
  unit, followed by the inverse scalar-restriction/point comparison. These are
  specified arrows, not maps chosen between isomorphic objects.
  Restricting the supplied isomorphisms means applying the actual inverse-image
  functor and the canonical composition comparisons; naturality gives the same
  square on refinements. No independent noncanonical refinement data is needed.
* `kummerScalarSingle` is the scalar adjunct of the ordinary coefficient unit,
  using the published exact restriction/single comparison. It is the
  scalar-unit-normalized iota arrow; local finite freeness makes it invertible.
  `kummerScalarTheta` composes beta with direct image of this arrow, in that order.
  `kummerGeometricBeta` is a specialization of the prescribed beta to L[0];
  `kummerModelTheta` is its resulting Theta pulled back along v and followed by phi_Omega.
* `kummerStratumInvariantUnit` is `CondensedDerivedRestriction.coefficientMap`
  of the actual unit with the canonical single-degree comparison.
  `kummerStratumSigma` is its scalar adjunct under the published derived
  extension/restriction adjunction. `kummerPointSigma` is point pullback
  of sigma preceded by the scalar-unit-preserving point comparison.
* The first conclusion is an equality of actual derived morphisms: restricted
  Theta followed by phi_Omega equals the geometric scalar/pullback comparison,
  followed by scalar extension of phi_E, followed by `kummerPointSigma`.
  These two composites are named `kummerModelTheta` and `kummerModelSigma`; their
  declared domains and codomains agree, so the conclusion uses ordinary equality.
  The second conclusion says that invertibility of every `kummerStratumSigma`
  implies `IsIso (kummerGeometricBeta ... L)` on Y. There are no stalk,
  boundedness, or constructibility assumptions on either direct image.

Dependencies read and used:

* `Sheaf.Topology.ContinuousMapCondensedRing` and `ContinuousMapCondensedRingMap`:
  `Profinite.continuousMapRingObjOfUniverse` and the postcomposition map; at
  coefficient universe zero these are the published continuous-map constructions
  used by the coefficient models.
* `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`.
* `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` and the published
  module-object derived framework: ordinary unbounded `DerivedCategory` and total
  derived functors, not a bounded or completed substitute.
* `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`; the internal form used
  in the maps is the published `Mod.derivedExtendMapDerivedCategoryAdjunction`
  from `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the explicit separated finite-type setting recorded at `sk-def-sfb-dc-setting`.
* `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`.
* `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `IsStrictNormalCrossingsBoundary`; `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `IsOpenImmersion` for the complement inclusion.
* `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, and the actual monoidal point pullback.
* `Sheaf.Paper.CondensedModuleDerivedPushpull`: `moduleObjectDerivedPushforward`.
* `Sheaf.Paper.AllContinuousScalarMate`: `tameBoundaryScalarMap`,
  `tameBoundaryScalarExtension`, `tameBoundaryScalarPullIso`,
  `tameBoundaryScalarComparison`, retaining the K-flat unit normalization.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: the small pro-etale site and covers.
* `Sheaf.CategoryTheory.CondensedDerivedInvariants`: `derived`, `scalarAction`,
  and `coefficientMap`, with the normalized fixed-section coefficient comparison.
* `Sheaf.Paper.KFlatScalarComparisonNormalization`:
  `SheafOfModules.ScalarPullback.kflat_scalar_comparison_normalization`.
* The new definition node reuses `KummerCoefficientModels`, `kummerOpenImage`,
  `KummerFinitePrimeToEllImage`, `kummerDerivedRestriction`,
  `kummerSourceScalarMap`, `purityAdjunctionSingleMap`, and
  `derivedFromCondensed` from its cited existing modules. No existing dependency
  declaration is replaced or copied.

The theorem docstring carries all five DAG proof steps, including the double
transpose calculation, pullback composition, equality of scalar adjuncts, finite
stratification of the Noetherian scheme, and cancellation of the scalar-single
isomorphism. The stated proof dependencies are imported for this future proof.

Edge cases checked: empty divisor (the unique empty subset stratum is Y), empty
Y, empty strata and empty covering families, the I=empty full inertia group
(which is trivial), rank-zero representation and zero L, arbitrary normed
continuous coefficients rather than locally constant functions, and potentially
unbounded invariant complexes. No false or disputed assertion was found. The
chosen enumeration of finite components is harmless under reindexing.

Searches: `searches.jsonl` records the actual msearch results. LeanFinder searched
for normalized Kummer stratum scalar mate detection (eight unrelated normalization
or Galois-restriction results); Loogle `CategoryTheory.Adjunction, "homEquiv"`
returned the generic adjunction API, which is reused; msearch grep for Kummer/stratum
scalar/mate and the new helper names returned no hits. LeanSearch on scalar
adjuncts of derived continuous invariants returned generic derived adjunction,
ordinary module scalar extension, and topological-representation invariants,
not this statement. Direct rg of `lean/WeilConjectures` and `lean/Sheaf` found no
existing declarations of these helpers or this theorem. DAG and blueprint
searches found the existing coefficient, root, model and scalar-square notions;
these are reused, and their stronger geometric chart assumptions are not imposed
on this conditional model-detection theorem.

## New nodes

`def-sfb-kummer-stratum-scalar-maps` owns the canonical maps named in the item's
statement: scalar-single and Theta, the exact scalar-restriction/point comparison
and its scalar adjunct, the actual invariant-unit rho and its scalar adjunct sigma,
and their point pullbacks. These use real existing functors, units, adjunction
bijections and natural comparisons. The node explicitly cites all existing
coefficient/model/geometry/invariant/pullback notions that it uses. Its source is
the same main-20261015 direct-images paragraph (3), as extracted by the item.
Searches above and in its `mathlib_searches` found no existing declaration of
these composites. Existing `KummerInvariantScalarArrow` packages resolution lifts
on a geometric chart, and `KummerStratumChart` requires the full root chart; neither
is the unconditional scalar adjunct used here. Bundled endpoints avoid repeated
expansion of ring-object monoidal data during elaboration without changing a map.

## Validation

Every delivered module is checked separately with the prescribed `scompile.py`.
The final clean current-source check passed both modules (46.7/57.7 seconds in the
current-source confirmation of the prescribed compiler). The final module layout
places canonical scalar maps in their definition node and model-specific composites
with the theorem. Both composites have explicit common endpoints and ordinary
equality is used. The dry run and final delivery are checked with deliver2.py.

## Second reading by NP

I reread the node and the final Lean signature against the source. The prime,
characteristic, scheme, regularity, SNC boundary, lisse-module, cover,
representation and prime-to-ell-image hypotheses are present as listed above.
The `finite` and `closure` model fields use the actual all-continuous condensations;
`normalized` compares the actual coefficient-unit maps. Restriction to refinements
is the inverse image of these supplied arrows with canonical composition
comparisons. The empty stratum imposes no extra existence requirement, since its
cover may be empty. The two conclusions respectively identify the actual derived
arrows (`kummerModelTheta = kummerModelSigma`) and deduce global invertibility of
the prescribed beta from invertibility of every invariant sigma. No boundedness,
stalk detection or direct-image constructibility has entered the signature.
During rereading I replaced inferred composite endpoints by explicit common
endpoints and bundled scalar interfaces; these changes preserve the maps and make
the equality usable. There is one postponed theorem and no postponed definition.
This is the worker's second reading; no separate agent was started.

The first dry run found the current schema requires `import_flags` on new nodes;
added the empty list and reran preflight.
