# Rep.nonempty_equiv_invariantResolution_continuousCohomology

## Reason

The assigned module is listed for retirement in coord/retire-items.tsv and already
has zero holes. The adopted source constructs an additive equivalence with identical
universes and hypotheses. Its underlying equivalence supplies the old Nonempty
conclusion, so the duplicate theorem and module can be retired after migrating their
sole direct consumer. The source-library files and target statements are unchanged.

## Old

```lean
theorem nonempty_equiv_invariantResolution_continuousCohomology
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    [(E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).Additive]
    (F : A) (I : InjectiveResolution F)
    (N : TopRep.{max u s} ℤ G) [DiscreteTopology N.V]
    (e : (E.functor.obj F).obj.V ≃ₗ[ℤ] N.V)
    (he : ∀ (g : G) (x : (E.functor.obj F).obj.V),
      e ((E.functor.obj F).obj.ρ g x) = N.ρ g (e x)) (q : ℕ) :
    Nonempty (((((E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).homology q) ≃
      continuousCohomology q N)
```

## New

Retire the local declaration; use the existing adopted-source construction:

```lean
noncomputable def invariantResolutionHomologyAddEquivContinuousCohomology
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    [(E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).Additive]
    (F : A) (I : InjectiveResolution F)
    (N : TopRep.{max u s} ℤ G) [DiscreteTopology N.V]
    (e : (E.functor.obj F).obj.V ≃ₗ[ℤ] N.V)
    (he : ∀ (g : G) (x : (E.functor.obj F).obj.V),
      e ((E.functor.obj F).obj.ρ g x) = N.ρ g (e x)) (q : ℕ) :
    ((((E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).homology q) ≃+
      continuousCohomology q N
```

Taking `.toEquiv` and `Nonempty.intro` proves the exact old conclusion. The direct
consumer needs the equivalence itself, so it takes `.toEquiv` directly and composes
it with its existing derived-invariants and coefficient comparisons. In degree zero,
for zero coefficients, and for the trivial group, this operation still forgets only
the additive structure: it adds no hypothesis and changes neither carrier.
The original DAG node remains, attached to the upstream construction. The parent
still cites that node, now realized by this construction; the unit route is preserved.

## Users

The tools/downstream.py inventory lists six transitive consumers. Whole-library and
quarantine searches find one direct importer and one application of the old theorem,
both in DiscreteInvariantsContinuousComparison. Its public statement, visibility,
docstring, and public imports are unchanged. The other five require no adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unclaimed | Indirect consumer; dependency public signature and visibility unchanged. |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | unclaimed | Indirect consumer; dependency public signature and visibility unchanged. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | Indirect consumer; dependency public signature and visibility unchanged. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding | unclaimed | Indirect consumer; dependency public signature and visibility unchanged. |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | unclaimed | Indirect consumer; dependency public signature and visibility unchanged. |
| Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison | unclaimed | Replace private proof import and obtain the underlying upstream additive equivalence. |

## Status

landed 20261020T163939-L-3833438 2026-10-20 (merge of deliver/E1/Sheaf.RepresentationTheory.DiscreteResolutionContinuousCohomology)
