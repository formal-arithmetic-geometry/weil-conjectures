# lisseCoefficientDiagramData

## Reason

The old definition chose an arbitrary `LisseCoefficientDiagramData` from a mere
nonemptiness theorem. Its specification fixed objects and arrow functors but did
not fix the unit and composition constraints. The automorphism pullback theorem
requires the canonical tensor constraints. A gauge twist of the coefficient diagram
can violate that specification for a component-swapping scheme automorphism.

Construct the coefficient diagram with the canonical tensor constraints explicitly.
The existing integral identity and composite comparisons are explicit tensor
constructions. Their rationalizations use these same integral isomorphisms.
Expose those constructions and their generator formulas, and construct the diagram
from them and their already proved associativity and unit laws. No unspecified
pseudofunctor, unit comparison or composite comparison is chosen.

`Sheaf.Paper.LisseAdicSheaves` was unclaimed when this repair began. The assigned
item is `Sheaf.Paper.LisseAdicAutomorphismPullback`. No source-library declaration
is changed. No target signature is changed. Review of targets depending on the
algebraic coefficient category is reopened for this canonical-coherence repair.

The original expanded full-subcategory/tensor interfaces exceeded the per-file
compile limit in diagnostics. The named inherited structures and semireducible
type definitions address that conversion cost without changing the objects or
morphisms. The repaired coefficient module has compiled with artifacts in 56.8
seconds; the completed item takes 32.6 seconds and its axiom list is exactly the
three permitted logical axioms.

## Old

```lean
@[irreducible]
def lisseCoefficientDiagramData : LisseCoefficientDiagramData l Y K :=
  Classical.choice (lisseCoefficientDiagram_exists l Y K)
```

The conversion-performance changes replace the following abbreviations by
semireducible definitions of the same types, adding their inherited structure caches:

```lean
abbrev LisseIntegralSheaf [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)] :=
  ObjectProperty.FullSubcategory (IsLisseIntegralDiagram l E Y)

abbrev lisseRationalHom (F G : LisseRationalSheaf l E Y) :=
  TensorProduct (Padic.coefficientExtensionIntegers l E) E (F.integral ⟶ G.integral)
```

## New

`lisseCoefficientDiagramData` directly assembles `lisseCoherentCategoryDiagram`
with `lisseRationalScalarIdentityIso`, `lisseRationalScalarCompositeIso`, and their
proved associativity and unit laws. Objects, scalar-extension functors and all
existing written public signatures are retained. Its complete definition is in the
delivered `LisseAdicSheaves.lean`.

The public scalar comparison API gives the explicit integral/rational isomorphisms
and their generator/component formulas. The existing construction helpers become
public under the `lisseCoherence_` prefix because a public data definition cannot
refer to private data. Their proofs are retained; the rational identity naturality
proof now uses the same generic tensor-intertwining lemma as composite naturality.
The scalar-level generators and index/extensionality lemmas receive public names.
The scalar structure caches are definitionally the existing algebra module,
subring ring/algebra and quotient ring/algebra structures, registered only locally.
The coefficient file uses the inherited ring instances after defining these named
copies: retaining the copies as competing local instances caused repeated expensive
conversion checks. The automorphism generator proof enables the named copies only
where needed. Operations and ring structures are unchanged.

The scalar-level isomorphism in the item is now an alias of the shared public
`lisseScalarLevelIso`; its underlying isomorphism is unchanged. The rational Hom
is a semireducible definition of the same tensor product, with named copies of its
existing additive and scalar structures. This avoids repeatedly constructing the
same instances. `catToReflQuiver` is disabled while each file elaborates and restored
at its end, so categorical morphisms use the direct category quiver throughout the
new proofs. The explicit coefficient-diagram record uses the component functions
directly, avoiding costly intermediate local functor definitions.

The integral sheaf type is now a semireducible definition of the same full
subcategory, with `lisseIntegralCategory` naming its inherited category structure.
The preadditive, linear, and integral Hom caches are registered globally so the
nominal integral type retains its inherited typeclass interface. The preadditive
and linear cache bodies explicitly use that full subcategory. This keeps
morphism types from repeatedly expanding the lissity predicate during conversion;
objects, morphisms, identities and composition are definitionally unchanged. During
scalar-extension record elaboration, the named scalar level, tensor generators and
Hom structures are locally irreducible; they are made semireducible again
for the ensuing construction proofs. The records retain all their fields and
constructors and projections. The expensive, unused generated constructor-injectivity
lemmas and size functions are suppressed for `LisseRationalComposition`,
`LisseIntegralScalarExtensionData`, `LisseRationalScalarExtensionData` and
`LisseCoefficientDiagramData`. No consumer refers to these generated names.
Named ring copies are enabled locally for the tensor-comparison proofs, after
the scalar-extension construction has been checked with inherited instances.

## Users

The table lists all transitive importers. The textual users of the changed
coefficient diagram are the item itself, `LisseAdicFiberFunctors`,
`AlgebraicFibrePathConstruction`, `CoefficientFibreComparisonNaturality`,
`LisseCoefficientFiberComparisons`, and `LisseCoefficientFiberEndomorphisms`.
They use the unchanged `obj_eq` and `map_eq` interface. No consumer signature
is weakened, strengthened or otherwise changed. The repaired canonical coherence
now fixes the intended tensor 2-colimit in their categories and fibres.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.AlgebraicGeometry.LocalSystemTensorMonodromy | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.AlgebraicGeometry.TorsionLocalSystemMonodromy | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.ConstructibleSheaf.GaloisDescentMonodromyTensor | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.AdicFibrePathExtension | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.AlgebraicFibrePathConstruction | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.CoefficientFibreComparisonNaturality | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.CtfHomLocallyConstant | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.EtaleLocalMonodromyRealization | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.EtaleLocalMonodromyRealizationBase | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.EtaleLocalMonodromyRealizationLocal | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.EtaleMonodromyRealizationData | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.EtaleWeilFundamentalRepresentation | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.EtaleWeilSheafEquivalence | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.FibreFunctorBasepointTransport | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.FibreFunctorBasepointTransportData | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.FibreFunctorLinearTransport | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.GaloisAdicFromFinite | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.GaloisFiniteModuleLift | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.GaloisFiniteTensorScalar | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.GaloisLisseCorrespondenceData | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.GaloisPartitionTensorClosure | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.IntegralFibrePathConstruction | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.IntegralFibreScalarComparison | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.IntegralRationalizationExact | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.LatticeNormalizationRationalExact | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.LisseAdicAutomorphismPullback | D7 | assigned proof completed against canonical coherence |
| Sheaf.Paper.LisseAdicFiberFunctors | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.LisseCoefficientFiberComparisons | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.LisseCoefficientFiberEndomorphisms | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.LisseCompletedPointwiseComparison | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.LisseCompletedSystemComparison | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.LisseCompletedSystemData | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.LisseCompletedTensorOperations | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.LisseIntegralScalarFiberIsomorphism | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.LisseIntegralSmallCoefficients | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.LisseRationalScalarFiberMaps | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.LisseScalarFiberMaps | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.LisseScalarFiberReductions | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.MonodromyLimitRationalExact | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.MonodromyObjectCover | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.MonodromySingleObjectCover | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.NormalCompletedIntegralModel | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.NormalizedMonodromyExact | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.NormalizedMonodromyFunctor | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.RationalFibrePathConstruction | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.RationalFibrePathScalarSquare | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.RationalFibreScalarComparison | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.RealBoundaryPathIndependence | unclaimed | same public interface; canonical tensor coherence |
| Sheaf.Paper.SmoothLisseIntegralLattice | unclaimed | same public interface; canonical tensor coherence |
| TargetsCheck | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.Statement | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.ZetaFunction.Examples | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | same public interface; canonical tensor coherence |
| WeilConjectures.ZetaFunction.Weights | unclaimed | same public interface; canonical tensor coherence |

All 70 downstream modules were compiled individually in dependency order against
the repaired definitions. No consumer adaptation was necessary; the delivery
contains only the two changed Lean modules. The root entrypoints `TargetsCheck`
and `WeilConjectures` are covered by the maintainer's global build.

## Status

landed 20261021T020113-L-2585388 2026-10-21 (merge of deliver/D7/Sheaf.Paper.LisseAdicAutomorphismPullback)
