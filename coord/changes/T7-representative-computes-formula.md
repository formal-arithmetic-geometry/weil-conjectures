# Representative and colimit formulas

## Reason

Delivery path: `coord/changes/T7-representative-computes-formula.md`.
If an independent reader needs to override this record with `--apply-fixes`, the
required fix-directory filename is `T7-representative-computes-formula.change.md`.
The delivered basename without `.change` is not a supported override alias.

The concrete representative localization square takes 13.5 seconds in kernel
checking even with a `sorry` body. Name the unchanged formula in the existing
comparison-data module; this keeps the formula available to all consumers and
lets the theorem refer to it without expanding its concrete category endpoints.
There is no new axiom, hypothesis, conclusion, witness choice or weakened equation.
The target interpretation must be independently reviewed under the project rule.

## Old

```lean
theorem internalHomRepresentative_computes
    (S : CoefficientClosedStructure (hom.{u} Λ X))
    (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring.{u} Λ X) S)
    (H : HomPresentation.{u} Λ X S T)
    (P : CochainComplex (Internal.{u} Λ X) ℤ) :
    ∃ j : internalHomRepresentative.{u} Λ X P ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙
        (CondensedRing.derivedHom.{u} Λ X).obj (op (DerivedCategory.Q.obj P)),
      ∀ N : CochainComplex (Internal.{u} Λ X) ℤ,
        homRepresentativeSquare (forward.{u} Λ X)
          (Functor.uncurry.obj (CondensedRing.derivedHom.{u} Λ X)) (hom.{u} Λ X) H.homIso
          (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)
          ((DerivedCategory.Q (C := Modules.{u} Λ X)).obj ((complexForward.{u} Λ X).obj P))
          ((DerivedCategory.Q (C := Modules.{u} Λ X)).obj ((complexForward.{u} Λ X).obj N))
          ((localizationIso.{u} Λ X).app P) ((localizationIso.{u} Λ X).app N)
          (j.hom.app N)
          ((localizationIso.{u} Λ X).app ((internalHomRepresentative.{u} Λ X P).obj N))
          ((DerivedCategory.Q (C := Modules.{u} Λ X)).mapIso
            ((homRepresentativeIso.{u} Λ X P).app N))
          (coefficientHomResolutionIso.{u, u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (ring.{u} Λ X)
            ((complexForward.{u} Λ X).obj P) ((complexForward.{u} Λ X).obj N))

theorem continuity_map_transport
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (P : CochainComplex (Internal.{u} Λ X) ℤ)
    (D : I ⥤ CochainComplex (Internal.{u} Λ X) ℤ) (b : ℤ)
    (_h : ∀ (i : I) (n : ℤ), n < b → IsZero ((D.obj i).X n)) :
    (complexForward.{u} Λ X).map (colimit.post D (internalHomRepresentative.{u} Λ X P)) ≫
        (homRepresentativeIso.{u} Λ X P).hom.app (colimit D) ≫
        (SfbHomFilteredColimit.homFixed.{u + 1, u, u}
          (Scheme.ProEt.topology X) (ring.{u} Λ X) ((complexForward.{u} Λ X).obj P)).map
            ((preservesColimitIso (complexForward.{u} Λ X) D).hom) =
      (preservesColimitIso (complexForward.{u} Λ X)
        (D ⋙ internalHomRepresentative.{u} Λ X P)).hom ≫
        colimMap (Functor.isoWhiskerLeft D (homRepresentativeIso.{u} Λ X P)).hom ≫
        colimit.post (D ⋙ complexForward.{u} Λ X)
          (SfbHomFilteredColimit.homFixed.{u + 1, u, u}
            (Scheme.ProEt.topology X) (ring.{u} Λ X) ((complexForward.{u} Λ X).obj P))

theorem continuity_iff (P : CochainComplex (Internal.{u} Λ X) ℤ) :
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (D : I ⥤ CochainComplex (Internal.{u} Λ X) ℤ) (b : ℤ),
      (∀ (i : I) (n : ℤ), n < b → IsZero ((D.obj i).X n)) →
        QuasiIso (colimit.post D (internalHomRepresentative.{u} Λ X P))) ↔
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (D : I ⥤ CochainComplex (Modules.{u} Λ X) ℤ) (b : ℤ),
      (∀ (i : I) (n : ℤ), n < b → IsZero ((D.obj i).X n)) →
        QuasiIso (colimit.post D
          (SfbHomFilteredColimit.homFixed.{u + 1, u, u}
            (Scheme.ProEt.topology X) (ring.{u} Λ X) ((complexForward.{u} Λ X).obj P))))

theorem filtered_colimit_map_transport
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D E : I ⥤ CochainComplex (Internal.{u} Λ X) ℤ)
    (D' E' : I ⥤ CochainComplex (Modules.{u} Λ X) ℤ)
    (d : D ⋙ complexForward.{u} Λ X ≅ D')
    (e : E ⋙ complexForward.{u} Λ X ≅ E')
    (f : D ⟶ E) (g : D' ⟶ E')
    (h : Functor.whiskerRight f (complexForward.{u} Λ X) ≫ e.hom = d.hom ≫ g) :
    (complexForward.{u} Λ X).map (colimMap f) ≫
        (preservesColimitIso (complexForward.{u} Λ X) E).hom ≫ colimMap e.hom =
      (preservesColimitIso (complexForward.{u} Λ X) D).hom ≫
        colimMap d.hom ≫ colimMap g
```

## New

```lean
theorem internalHomRepresentative_computes
    (S : CoefficientClosedStructure (hom.{u} Λ X))
    (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring.{u} Λ X) S)
    (H : HomPresentation.{u} Λ X S T)
    (P : CochainComplex (Internal.{u} Λ X) ℤ) :
    RepresentativeComputes.{u} Λ X S T H P

theorem continuity_map_transport
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (P : CochainComplex (Internal.{u} Λ X) ℤ)
    (D : I ⥤ CochainComplex (Internal.{u} Λ X) ℤ) (b : ℤ)
    (_h : ∀ (i : I) (n : ℤ), n < b → IsZero ((D.obj i).X n)) :
    PostComparisonSquare (complexForward.{u} Λ X)
      (internalHomRepresentative.{u} Λ X P)
      (SfbHomFilteredColimit.homFixed.{u + 1, u, u} (Scheme.ProEt.topology X)
        (ring.{u} Λ X) ((complexForward.{u} Λ X).obj P))
      (homRepresentativeIso.{u} Λ X P) D

theorem continuity_iff (P : CochainComplex (Internal.{u} Λ X) ℤ) :
    BoundedFilteredContinuity.{_, _, u + 1} (internalHomRepresentative.{u} Λ X P) ↔
      BoundedFilteredContinuity.{_, _, u + 1}
        (SfbHomFilteredColimit.homFixed.{u + 1, u, u} (Scheme.ProEt.topology X)
          (ring.{u} Λ X) ((complexForward.{u} Λ X).obj P))

theorem filtered_colimit_map_transport
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D E : I ⥤ CochainComplex (Internal.{u} Λ X) ℤ)
    (D' E' : I ⥤ CochainComplex (Modules.{u} Λ X) ℤ)
    (d : D ⋙ complexForward.{u} Λ X ≅ D')
    (e : E ⋙ complexForward.{u} Λ X ≅ E')
    (f : D ⟶ E) (g : D' ⟶ E')
    (h : Functor.whiskerRight f (complexForward.{u} Λ X) ≫ e.hom = d.hom ≫ g) :
    ColimitMapSquare (complexForward.{u} Λ X) D E D' E' d e f g
```

`RepresentativeComputes` is the verbatim former conclusion, including the same
existential natural isomorphism, localization maps and evaluation square.
`PostComparisonSquare` and `ColimitMapSquare` are the generic versions of the
verbatim former comparison equations. `BoundedFilteredContinuity` is the same
quantification over small filtered diagrams and their common termwise lower bound.
All four theorem types are definitionally equal to their original types.
The new predicate bodies are in `InternalSectionHomComparisonData.lean`; none uses
an existence theorem to choose data or contains a theorem hole.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.InternalSectionHomComparisonData | unclaimed | New predicate; existing definitions unchanged. |
| Sheaf.Paper.InternalSectionHomContinuityComparison | T7 | Definitional folding of the conclusion. |
| Sheaf.Paper.InternalSectionScalarHomTransportData | unclaimed | Existing definitions unchanged; recompiled. |
| Sheaf.Paper.FiniteModelTopologyComparisonMaps | unclaimed | Transitive importer; no use of this theorem. |
| Sheaf.Paper.FiniteModelTopologyDerivedHom | unclaimed | Transitive importer; no use of this theorem. |
| Sheaf.Paper.GlobalInternalHomDetection | unclaimed | Transitive importer; no use of this theorem. |
| Sheaf.Paper.QlbarBoundedTensorColimit | unclaimed | Transitive importer; no use of this theorem. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | unclaimed | Transitive importer; no use of this theorem. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Transitive importer; no use of this theorem. |

`tools/downstream.py` reports those eight downstream modules. Text searches find
no uses of `internalHomRepresentative_computes` outside its defining module.
No forced adaptations are required: the added predicates change no existing data.

## Status

landed 20261025T203246-L-2797225 2026-10-25 (merge of deliver/T7/Sheaf.Paper.InternalSectionHomContinuityComparison)
