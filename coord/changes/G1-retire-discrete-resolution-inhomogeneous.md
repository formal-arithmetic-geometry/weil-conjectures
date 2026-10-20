# Rep.nonempty_equiv_invariantResolution_inhomogeneous

## Reason

Retirement item in coord/retire-items.tsv. The adopted source already constructs the
additive equivalence required by this theorem, with identical universes and hypotheses.
Migrate its sole direct consumer to that construction and retire the redundant copy.
No source-library file or target statement is changed. The DAG attachment follows the
upstream construction and its existing proof dependencies remain valid.

## Old

```lean
theorem nonempty_equiv_invariantResolution_inhomogeneous
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    [(E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).Additive]
    (F : A) (I : InjectiveResolution F)
    (K : CochainComplex AddCommGrpCat.{max u s} ℕ)
    (t : ∀ n : ℕ, K.X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj F).obj.V)
    (ht : ∀ (n : ℕ) (x : K.X n) (g : Fin (n + 1) → G),
      t (n + 1) ((K.d n (n + 1)) x) g =
        (E.functor.obj F).obj.ρ (g 0) (t n x (fun k ↦ g k.succ)) +
          ∑ k : Fin (n + 1),
            (-1 : ℤ) ^ (k.val + 1) • t n x (Fin.contractNth k (· * ·) g))
    (q : ℕ) :
    Nonempty (((((E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).homology q) ≃ K.homology q)
```

## New

The redundant Nonempty theorem is retired. Its replacement is the existing source definition:

```lean
noncomputable def invariantResolutionHomologyAddEquivInhomogeneous
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    [(E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).Additive]
    (F : A) (I : InjectiveResolution F)
    (K : CochainComplex AddCommGrpCat.{max u s} ℕ)
    (t : ∀ n : ℕ, K.X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj F).obj.V)
    (ht : ∀ (n : ℕ) (x : K.X n) (g : Fin (n + 1) → G),
      t (n + 1) ((K.d n (n + 1)) x) g =
        (E.functor.obj F).obj.ρ (g 0) (t n x (fun k ↦ g k.succ)) +
          ∑ k : Fin (n + 1),
            (-1 : ℤ) ^ (k.val + 1) • t n x (Fin.contractNth k (· * ·) g))
    (q : ℕ) :
    ((((E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).homology q) ≃+ K.homology q
```

Its additive equivalence gives the old conclusion by `.toEquiv` and `Nonempty.intro`.
The consumer composes the additive equivalences and then takes the underlying equivalence.
In degree zero, for zero coefficients, and for the trivial group this forgetful step
preserves exactly the same cohomology comparison; no additional hypothesis is introduced.

## Users

Computed with tools/downstream.py and a whole-library declaration search. Only the
continuous-resolution module imports the retired module or names the retired theorem.
Its public signature and visibility remain identical. No other consumer changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unclaimed | Indirect consumer; public interface of its dependency unchanged. |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | unclaimed | Indirect consumer; public interface of its dependency unchanged. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | Indirect consumer; public interface of its dependency unchanged. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding | unclaimed | Indirect consumer; public interface of its dependency unchanged. |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | unclaimed | Indirect consumer; public interface of its dependency unchanged. |
| Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison | unclaimed | Indirect consumer; public interface of its dependency unchanged. |
| Sheaf.RepresentationTheory.DiscreteResolutionContinuousCohomology | unclaimed | Proof import migrated; use additive comparison and forget addition after composition. |

## Status

landed 20261020T160943-L-3429742 2026-10-20 (merge of deliver/G1/Sheaf.RepresentationTheory.DiscreteResolutionInhomogeneousCohomology)
