# AlgebraicGeometry.filteredSpectrumTopologicalLimit

## Reason

Make the index poset small relative to the universe of the rings, as required by the
set-indexed filtered-colimit construction in Stacks `limits.tex`, Tags 0CUE and 0CUF.
The old Lean signature used independent universes without relative smallness. Thus its
categorical colimit hypothesis did not imply the elementwise filtered-colimit properties
used in the source proof.

This is an essential size correction, not a proof shortcut. For an index set larger than
the small-ring universe, consider the rational-function fields on its finite subsets.
Any cocone into a nonzero small ring would give an injection of the whole index set into
that ring: the images of distinct independent variables remain distinct because their
difference is invertible at a common field stage. There can be no such injection.
The zero ring is therefore a colimit in the restricted category of small rings, since
it is the only possible cocone vertex and its cocone maps are unique. Its spectrum is
empty, whereas the zero ideals of all the field stages are a compatible prime family.
This contradicts the old conclusion. Relative smallness excludes this example.

No target signature or definition changes. The compatible-family homeomorphism and the
compact-open preimage conclusions are unchanged. No Lean module currently calls the theorem;
all direct and transitive importers below are unaffected. The five mathematical DAG citers
are audited in the node's `statement_change`: their diagrams use common small universes.
The node does not realize a unit statement or step (`realized` is empty for its unit).

## Old

```lean
theorem filteredSpectrumTopologicalLimit
    (I : Type u) [PartialOrder I] [Nonempty I]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (F : I ⥤ CommRingCat.{v})
    (c : Cocone F) (hc : IsColimit c) :
    (∃ e : Homeomorph (Spec c.pt)
        {p : (i : I) → Spec (F.obj i) //
          ∀ (i j : I) (hij : i ≤ j),
            (Spec.map (F.map (homOfLE hij))) (p j) = p i},
      ∀ x : Spec c.pt,
        (e.1 x : (i : I) → Spec (F.obj i)) =
          (fun i => (Spec.map (c.ι.app i)) x)) ∧
      ∀ (i : I) (Q : Set (Spec (F.obj i))),
        IsOpen Q → IsCompact Q →
          IsCompact ((Spec.map (c.ι.app i)) ⁻¹' Q)
```

## New

```lean
theorem filteredSpectrumTopologicalLimit
    (I : Type u) [Small.{v} I] [PartialOrder I] [Nonempty I]
    (hdir : Directed (· ≤ ·) (id : I → I))
    (F : I ⥤ CommRingCat.{v})
    (c : Cocone F) (hc : IsColimit c) :
    (∃ e : Homeomorph (Spec c.pt)
        {p : (i : I) → Spec (F.obj i) //
          ∀ (i j : I) (hij : i ≤ j),
            (Spec.map (F.map (homOfLE hij))) (p j) = p i},
      ∀ x : Spec c.pt,
        (e.1 x : (i : I) → Spec (F.obj i)) =
          (fun i => (Spec.map (c.ι.app i)) x)) ∧
      ∀ (i : I) (Q : Set (Spec (F.obj i))),
        IsOpen Q → IsCompact Q →
          IsCompact ((Spec.map (c.ι.app i)) ⁻¹' Q)
```

## Users

A whole-name source search (`tools/downstream.py ... --uses filteredSpectrumTopologicalLimit`)
finds only the declaration itself. No importer calls it. Complete transitive-import list:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcValuativeDescent | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.AlgebraicGeometry.CoproductFpqcEffectivity | H1 | No declaration use; imports and statements unchanged. |
| Sheaf.AlgebraicGeometry.EtaleSheafAlgebraicSpaceRealization | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.AlgebraicGeometry.FieldActionDerivedSectionTransport | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.AlgebraicGeometry.IndQuasiAffineFpqcDescent | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.AlgebraicGeometry.IntersectionCanonicalAffineEmbedding | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.AlgebraicGeometry.InvariantOpenAffinizationEquivariance | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.AlgebraicGeometry.QuasiAffineChartLimitTopology | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.AlgebraicGeometry.SeparatedLqfFpqcDescent | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.AlgebraicGeometry.UniverseEnlargedEtaleRealization | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.Paper.FieldActionToposCoefficients | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.Paper.FieldProfiniteGaloisSite | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.Paper.IntegralFibreSectionSpecialization | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.Paper.IntegralHenselianLisseSectionRigidity | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.Paper.IntegralLisseClosedBaseChange | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.Paper.NormalLatticeFiniteCoverPresentation | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.Paper.StratifiedLatticeScheme | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.Paper.SupportedLatticeNormProjection | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.Paper.TameIntegralReductionFamily | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.Paper.WStrictCommonComponentHypercovers | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.RingTheory.IndfiniteContractibleBaseWStrict | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.RingTheory.WLocalDirectedLimitTopology | unclaimed | No declaration use; imports and statements unchanged. |
| Sheaf.SecPurity.NormalLocallyConstantFiniteSection | unclaimed | No declaration use; imports and statements unchanged. |

## Status

landed 20261023T105401-L-3550553 2026-10-23 (merge of deliver/N2/Sheaf.Topology.FilteredSpectrumTopologicalLimit)
