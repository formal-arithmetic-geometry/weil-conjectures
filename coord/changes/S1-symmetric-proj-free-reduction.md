# AlgebraicGeometry.SymmetricProjTautologicalCharts.free_compatibility_of_normalized_quotient

## Reason

Separate the ordered relative polynomial comparison and the global twist-gluing
argument, and reuse the already proved normalized standard-model scheme comparison.
The original theorem is proved from these inputs. The two new theorem modules have
one named theorem each, with their own DAG nodes and source proofs in words.
This is a decomposition with two new holes and one original hole removed.

## Old

```lean
theorem free_compatibility_of_normalized_quotient (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E) :
    ProjectiveBundleQuotientGeometry.HasFreeCompatibility D := by sorry
```

## New

```lean
theorem free_compatibility_of_normalized_quotient (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E) :
    ProjectiveBundleQuotientGeometry.HasFreeCompatibility D := by
  intro r b
  obtain ⟨eRel, hRel, hAffine⟩ := exists_ordered_relative_comparison S E r b
  obtain ⟨θ, hθ, _⟩ :=
    RelativeProjectiveSpace.existsUnique_freeProjectiveBundleBaseChangeSpace S r
  obtain ⟨t, ht⟩ := exists_ordered_twist_comparison S E D r b eRel hRel hAffine θ
    hθ.1 hθ.2.1
  refine ⟨eRel, eRel ≪≫ θ, t, hRel, ?_, ht, hAffine⟩
  change (eRel.hom ≫ θ.hom) ≫ _ = _
  rw [Category.assoc, hθ.1, hRel]
```

The two new declarations are
`AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_ordered_relative_comparison`
and `AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_ordered_twist_comparison`.
Their exact statements are in the new modules and matching node records. They were
absent before this delivery. All existing signatures, definitions and public imports
are identical. All added imports of the original module are private proof imports.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SymmetricProjFreeComparison | S1 | Uses the two new lemmas and the existing standard-model comparison. |
| Sheaf.AlgebraicGeometry.SymmetricProjTautologicalCharts | unmodified consumer | Its call to the original theorem retains exactly the same type and visibility. |

The new modules have no existing consumers; the item is their only new direct
importer. No shared interface changes and no forced consumer adaptations occur.

## Status

landed 20261027T112425-L-1582438 2026-10-27 (merge of deliver/S1/Sheaf.AlgebraicGeometry.SymmetricProjFreeComparison)
