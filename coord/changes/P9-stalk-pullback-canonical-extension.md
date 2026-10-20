# AlgebraicGeometry.SingleComplexBaseChange.comparisonIntoPullback_naturality

## Reason

Finish the assigned upstream-sync rework using the existing proved upstream
extension comparison. The rework row still reports the archived duplicate
DerivedPullback import error. V4 already restored this item with corrected
imports and a complete proof. This packet additionally removes its dependency
on the duplicate Sheaf extension-comparison chain; it is not a rebase or an
unchanged restoration.

## Old

```lean
import Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparison
```

The proof applies that module's `exists_stalkDerivedExtensionComparison`, whose
K-flat hypothesis is named `IsAcyclicTensorKFlat`.

## New

```lean
import WeilConjectures.AlgebraicGeometry.StalkDerivedExtensionComparison
```

The upstream theorem has the same name, comparison formula, universal counit,
and quantifiers, with K-flatness named `IsKFlatTensor`. Both predicates are
defined by the same acyclic-test-complex formula. Supply their conversion
through a proved private helper, reused for both representatives:

```lean
private theorem canonical_kflat (Y : Scheme.{u})
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : P.IsAcyclicTensorKFlat) : P.IsKFlatTensor :=
  fun F hF ↦ hP F hF
```

```lean
  have hP' := canonical_kflat X P hP
  have hQ' := canonical_kflat X Q hQ
  obtain ⟨hsP, hjP⟩ := hj P hP' hcP
  obtain ⟨hsQ, hjQ⟩ := hj Q hQ' hcQ
```

The public imports, all declaration signatures, and the entire constructed
value of `comparisonIntoPullback` stay verbatim. Two diagram calculations now
use proved private generic lemmas in the same file: `conjugate_naturality`
cancels the stalk-factor isomorphisms and applies naturality; `paste_naturality`
postcomposes and combines the two squares. This performs rewriting on abstract
morphisms instead of unfolding the large concrete stalk terms. The calculation
and its conclusion are unchanged. The model-input identification, algebraic
localized naturality application, homology map and both computation equations
stay verbatim. No source-library file, definition or statement changes.
No target meaning changes. The existing extension-comparison node's Lean
attachment now names the upstream declaration actually used; its mathematical
statement and proof dependencies stay unchanged. The parent node records the
explicit predicate conversion and canonical theorem application.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality | P9 assignment | Private proof import, predicate bridge, generic diagram helpers, and their applications change. |
| Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso | quarantined; no local claim | Identical public API; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalComparisonSquare | quarantined; no local claim | Identical public API; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpectrumComparisonSourceTransport | quarantined; no local claim | Identical public API; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenComparisonIntoPullbackTransport | quarantined; no local claim | Identical public API; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenRestrictedCanonicalSquare | quarantined; no local claim | Identical public API; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenRestrictedComparisonCore | quarantined; no local claim | Identical public API; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport | quarantined; no local claim | Identical public API; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData | quarantined; no local claim | Identical public API; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenTermwiseComparison | quarantined; no local claim | Identical public API; no adaptation. |
| Sheaf.AlgebraicGeometry.TensorStalkFixedMapSquare | quarantined; no local claim | Identical public API; no adaptation. |

`tools/downstream.py --direct --uses comparisonIntoPullback
comparisonIntoPullback_naturality` reports no live downstream modules. Searching
`lean/Sheaf`, `lean/WeilConjectures`, and `quarantine/Sheaf` finds the ten
archived importers listed above. None is withdrawn or edited. A separate
consumer probe imports only this item, repeats its full original public
theorem signature, and applies the theorem with its original arguments.

The final item compiles and writes its artifacts in 38.8 seconds; the consumer
probe also compiles, both without diagnostics. The two public
declarations' printed axioms are exactly `propext`, `Classical.choice`, and
`Quot.sound`. There is no direct or inherited `sorry` in either declaration.

## Status

landed 20261020T230820-L-616730 2026-10-20 (merge of deliver/P9/Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality)
