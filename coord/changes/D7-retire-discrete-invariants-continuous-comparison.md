# Rep.nonempty_equiv_rightDerived_continuousCohomology

## Reason

The item is explicitly listed as `retire` in coord/retire-items.tsv and currently
has zero direct sorry holes. The adopted source constructs an additive equivalence
for exactly the same universes and hypotheses. Its `.toEquiv` proves the old
conclusion, so remove the duplicate Sheaf declaration after adapting both callers.
The source-library files, consumer public signatures, public imports and target
statements remain unchanged.

## Old

```lean
theorem nonempty_equiv_rightDerived_continuousCohomology
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A] [HasInjectiveResolutions A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (Γ : A ⥤ AddCommGrpCat.{max u s}) [Γ.Additive]
    (η : Γ ≅ E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat)
    (F : A) (N : TopRep.{max u t} ℤ G) [DiscreteTopology N.V]
    (e : (E.functor.obj F).obj.V ≃ₗ[ℤ] N.V)
    (he : ∀ (g : G) (x : (E.functor.obj F).obj.V),
      e ((E.functor.obj F).obj.ρ g x) = N.ρ g (e x)) (q : ℕ) :
    Nonempty ((Γ.rightDerived q).obj F ≃ continuousCohomology q N)
```

This declaration was in
Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison. Both callers
privately imported that module and extracted its Nonempty type equivalence.

## New

Retire the duplicate module using deleted.txt. The existing source construction is:

```lean
noncomputable def rightDerivedAddEquivContinuousCohomology
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A] [HasInjectiveResolutions A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (Γ : A ⥤ AddCommGrpCat.{max u s}) [Γ.Additive]
    (η : Γ ≅ E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat)
    (F : A) (N : TopRep.{max u t} ℤ G) [DiscreteTopology N.V]
    (e : (E.functor.obj F).obj.V ≃ₗ[ℤ] N.V)
    (he : ∀ (g : G) (x : (E.functor.obj F).obj.V),
      e ((E.functor.obj F).obj.ρ g x) = N.ρ g (e x)) (q : ℕ) :
    (Γ.rightDerived q).obj F ≃+ continuousCohomology q N
```

For the same inputs, the exact old proposition follows from:

```lean
  exact ⟨(Rep.rightDerivedAddEquivContinuousCohomology G A E Γ η F N e he q).toEquiv⟩
```

This implication was separately compiled against the original theorem signature.
The two consumers now privately import the source module and directly use the
construction's `.toEquiv`, composing it with their existing comparisons.
The original DAG node is retained with its mathematical statement and dependencies
unchanged, attached to this upstream declaration. Parent nodes still cite that
same node: no unit proof step is bypassed. The actual upstream proof still uses
the resolution comparison and coefficient comparison nodes.

Taking `.toEquiv` only forgets preservation of addition; it preserves the carrier,
functions, and inverse laws. This works equally in degree zero, for the trivial
group, for zero coefficients, and when the two coefficient universes differ.
No new existence choice, coefficient restriction, or finiteness assumption appears.

## Users

`tools/downstream.py` lists five transitive consumers. Searches of both library
roots and quarantine find exactly two direct imports and two applications of the
retired declaration. Both direct consumers are unclaimed in current claim records.
Their existing declarations, attributes, docstrings and public imports are kept.
The only changes are a private proof import and the expression producing their
local type equivalence. The other three consumers require no source adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison | D7 | Withdraw duplicate. |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | unclaimed | Replace private import and obtain upstream additive comparison's toEquiv. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding | unclaimed | Replace private import and obtain upstream additive comparison's toEquiv. |
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unclaimed | Indirect consumer; no source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | Indirect consumer; no source adaptation. |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | unclaimed | Indirect consumer; no source adaptation. |

## Status

landed 20261020T230729-L-605673 2026-10-20 (merge of deliver/D7/Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison)
