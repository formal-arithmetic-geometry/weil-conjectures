# AlgebraicGeometry.SingleComplexBaseChange.comparisonIntoPullback_naturality

## Reason

The assigned rework row records an old duplicate DerivedPullback import failure.
The current file has already been restored by V4 and repaired by P9; it compiles
with zero holes. It still redeclares the two public names already implemented
by the adopted upstream module. A concrete import probe loading the current
Sheaf item and its upstream twin fails with:

```text
import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality failed,
environment already contains
'AlgebraicGeometry.SingleComplexBaseChange.comparisonIntoPullback_naturality'
from Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality
```

Use the existing implementation as the unique declaration provider and retain the
historical module path as a public re-export. This fixes the reproduced collision;
it is a zero-hole environment repair, not an unchanged restoration or a rebase.
No adopted upstream file, declaration, import, attribute or definition is edited.

## Old

The old module has these public imports and a private extension-comparison import:

```lean
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
public import Sheaf.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.StalkDerivedExtensionComparison
```

It locally declares the following constructed map and theorem (signatures and
map body copied verbatim):

```lean
def comparisonIntoPullback (z : X')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (i : ℤ) :=
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  letI := (tensorMap f f' g g' sq z).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  letI := hP
  (cohomologyModel f f' g g' sq z P).localizedComparison i ≫
    HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i ≫
    (comparisonStalkHomologyIso X' z
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) i).inv ≫
    (comparisonStalkCohomology X' z i).map
      (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))

theorem comparisonIntoPullback_naturality (z : X')
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsAcyclicTensorKFlat) (hQ : Q.IsAcyclicTensorKFlat)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
    (a : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    ∀ e : (cohomologyModel f f' g g' sq z P).cohomology i ≅
        (cohomologyModel f f' g g' sq z Q).cohomology i,
      (ModuleCat.restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map e.hom =
        (comparisonSourceUnderlyingIso f f' g g' sq z P Q a i).hom →
      comparisonIntoPullback f f' g g' sq z P hcP i ≫
        (comparisonStalkCohomology X' z i).map ((derivedPullback g').map a.hom) =
      (ModuleCat.extendScalars.{u, u, u}
        (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z))).map e.hom ≫
        comparisonIntoPullback f f' g g' sq z Q hcQ i
```

Its theorem proof is already complete, using the private canonical_kflat,
conjugate_naturality and paste_naturality helpers.

## New

The historical module declares nothing a second time:

```lean
module
public import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Sheaf.Algebra.Homology.KFlat
```

The existing upstream declaration has this map and signature:

```lean
def comparisonIntoPullback (z : X')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (i : ℤ) :=
  letI := leftAlgebra f g' z
  letI := rightAlgebra f f' g g' sq z
  letI := (tensorMap f f' g g' sq z).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  letI := hP
  (cohomologyModel f f' g g' sq z P).localizedComparison i ≫
    HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i ≫
    (comparisonStalkHomologyIso X' z
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) i).inv ≫
    (comparisonStalkCohomology X' z i).map
      (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))

theorem comparisonIntoPullback_naturality (z : X')
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (hQ : Q.IsKFlatTensor)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
    (a : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    ∀ e : (cohomologyModel f f' g g' sq z P).cohomology i ≅
        (cohomologyModel f f' g g' sq z Q).cohomology i,
      (ModuleCat.restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map e.hom =
        (comparisonSourceUnderlyingIso f f' g g' sq z P Q a i).hom →
      comparisonIntoPullback f f' g g' sq z P hcP i ≫
        (comparisonStalkCohomology X' z i).map ((derivedPullback g').map a.hom) =
      (ModuleCat.extendScalars.{u, u, u}
        (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z))).map e.hom ≫
        comparisonIntoPullback f f' g g' sq z Q hcQ i
```

The map expressions are identical. The theorem signature differs only in the
spelling IsAcyclicTensorKFlat versus IsKFlatTensor: both definitions quantify over
all acyclic complexes F and require mapBifunctor F P (curriedTensor _) to be
acyclic, with the same SheafOfModules monoidal structure. They are definitionally
equal, not merely related by an implication. Retain the public KFlat import so
old callers can continue using the original predicate spelling.

A compiled probe repeats the complete original theorem signature and applies the
upstream theorem with all original arguments unchanged. A second check defines
the old map by its entire original expression and proves its equality with the
canonical map by rfl. Thus no hypothesis, universe, comparison map or conclusion
changes, including empty schemes, arbitrary degrees and the zero complex. No new
flatness or invertibility assumption is introduced. No target meaning changes.
The node attaches to the upstream implementation; its mathematical statement,
statement dependencies, three proof dependencies and unit route are preserved.

## Users

A source-only downstream.py query finds zero live direct importers of the Sheaf
item, and no live downstream declaration users. The ten archived importers below
are retained, together with their DAG parent edges. This is a working re-export,
not an empty withdrawal. None of those parents or archived files is deleted,
replaced or claimed repaired by this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality | S1 | Replace duplicate declarations by their canonical public re-export. |
| Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso | unclaimed | Quarantined importer; same names, arguments and defining map, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalComparisonSquare | unclaimed | Quarantined importer; same names, arguments and defining map, no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpectrumComparisonSourceTransport | unclaimed | Quarantined importer; same names, arguments and defining map, no adaptation. |
| Sheaf.AlgebraicGeometry.OpenComparisonIntoPullbackTransport | unclaimed | Quarantined importer; same names, arguments and defining map, no adaptation. |
| Sheaf.AlgebraicGeometry.OpenRestrictedCanonicalSquare | unclaimed | Quarantined importer; same names, arguments and defining map, no adaptation. |
| Sheaf.AlgebraicGeometry.OpenRestrictedComparisonCore | unclaimed | Quarantined importer; same names, arguments and defining map, no adaptation. |
| Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport | unclaimed | Quarantined importer; same names, arguments and defining map, no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData | unclaimed | Quarantined importer; same names, arguments and defining map, no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenTermwiseComparison | unclaimed | Quarantined importer; same names, arguments and defining map, no adaptation. |
| Sheaf.AlgebraicGeometry.TensorStalkFixedMapSquare | unclaimed | Quarantined importer; same names, arguments and defining map, no adaptation. |

The current upstream consumers already import the canonical module, so their
sources and signatures do not change. An import probe successfully loads the
re-export together with the upstream AffineBaseChangeSourceRepresentativeIso,
OpenComparisonIntoPullbackTransport and StalkComparisonCoordinateInvariance
modules. Loading both module paths now also succeeds, where the original fails.
The full old-signature and map-equation probes exercise the API used by the
archived consumers without asserting that their unrelated quarantine repairs
are complete. The two canonical declarations print only propext,
Classical.choice and Quot.sound as axioms.

## Status

landed 20261020T235622-L-1196463 2026-10-20 (merge of deliver/S1/Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality)
