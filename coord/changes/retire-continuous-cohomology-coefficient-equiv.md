# Rep.nonempty_equiv_continuousCohomology_coefficients

## Reason

The assigned item is listed as `retire` in coord/retire-items.tsv. Its only public
result is supplied by the adopted upstream construction
`Rep.continuousCohomologyAddEquivOfCoefficients`, which constructs an additive
equivalence for precisely the same inputs. Taking `.toEquiv` and `Nonempty.intro`
recovers the former proposition. Retire the duplicate Sheaf module, attach its
node to that upstream declaration, and adapt its sole direct consumer. No
upstream file is changed. No target statement or definition is changed.

## Old

In Sheaf.RepresentationTheory.ContinuousCohomologyCoefficientEquiv:

```lean
theorem nonempty_equiv_continuousCohomology_coefficients
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : TopRep.{max u s} ℤ G) (N : TopRep.{max u t} ℤ G)
    [DiscreteTopology M.V] [DiscreteTopology N.V]
    (e : M.V ≃ₗ[ℤ] N.V)
    (he : ∀ (g : G) (x : M.V), e (M.ρ g x) = N.ρ g (e x)) (q : ℕ) :
    Nonempty (continuousCohomology q M ≃ continuousCohomology q N)
```

The consumer privately imports this module and extracts an equivalence with:

```lean
  obtain ⟨b⟩ := nonempty_equiv_continuousCohomology_coefficients G M N e he q
```

## New

The local module is withdrawn using deleted.txt. The already existing upstream
construction, retained verbatim, has signature:

```lean
@[no_expose]
noncomputable def continuousCohomologyAddEquivOfCoefficients
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : TopRep.{max u s} ℤ G) (N : TopRep.{max u t} ℤ G)
    [DiscreteTopology M.V] [DiscreteTopology N.V]
    (e : M.V ≃ₗ[ℤ] N.V)
    (he : ∀ (g : G) (x : M.V), e (M.ρ g x) = N.ρ g (e x)) (q : ℕ) :
    continuousCohomology q M ≃+ continuousCohomology q N
```

The consumer privately imports
WeilConjectures.RepresentationTheory.ContinuousCohomologyCoefficientEquiv and uses:

```lean
  let b := (continuousCohomologyAddEquivOfCoefficients G M N e he q).toEquiv
```

Its own signature, attributes and public imports remain identical. The coefficient
node now records the upstream declaration and signature; its mathematical
statement continues to assert only the underlying type equivalence. The consumer
node describes forgetting the additive structure. The proof routes are unchanged.

## Users

`tools/downstream.py` lists the following transitive consumers. Searching both
library roots finds precisely one direct use of the retired public declaration,
in DiscreteInvariantsContinuousComparison. Claim metadata reports that module as
unclaimed at the time of adaptation. The other consumers need no changes because
its public signature and public imports are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RepresentationTheory.ContinuousCohomologyCoefficientEquiv | H2 | Withdraw duplicate module |
| Sheaf.RepresentationTheory.DiscreteInvariantsContinuousComparison | unclaimed | Replace private import and coefficient-equivalence proof line |
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unclaimed | Same consumer interface |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | unclaimed | Same consumer interface |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | Same consumer interface |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding | unclaimed | Same consumer interface |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | unclaimed | Same consumer interface |

## Status

landed 20261020T135410-L-1819265 2026-10-20 (merge of deliver/H2/Sheaf.RepresentationTheory.ContinuousCohomologyCoefficientEquiv)
