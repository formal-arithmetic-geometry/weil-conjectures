# Rep.representation_liftedGroupAlgebra_equivalence

## Reason

Retire the duplicate Sheaf module under the human-approved retirement task in
coord/retire-items.tsv. Its upstream twin already proves the original theorem with
exactly the same signature. The only current direct consumer uses the extra
anyUniverse theorem, absent upstream. A finite ring is small in every universe, so
that consumer can use the upstream theorem after shrinking its coefficient ring.
This works for arbitrary finite rings, including noncommutative rings and the zero
ring; it assumes neither an inequality involving the original coefficient universe
nor commutativity.

## Old

The retired module declared both:

```lean
theorem representation_liftedGroupAlgebra_equivalence_anyUniverse
    (R : Type u) [Ring R] (G : Type v) [Group G] :
    Nonempty (Rep.{w} R G ≌ ModuleCat.{w} (MonoidAlgebra (ULift.{t} R) G))

theorem representation_liftedGroupAlgebra_equivalence
    (R : Type u) [Ring R] (G : Type v) [Group G] :
    Nonempty (Rep.{max u v w} R G ≌
      ModuleCat.{max u v w} (MonoidAlgebra (ULift.{w} R) G))
```

The direct consumer's proof contained:

```lean
  let : Small.{max u w} G := small_max G
  let : Small.{max u w} (MonoidAlgebra (ULift.{max u w} A) G) :=
    small_of_injective (DFunLike.coe_injective.comp MonoidAlgebra.coeff_injective)
  obtain ⟨E⟩ := Rep.representation_liftedGroupAlgebra_equivalence_anyUniverse.{v, u,
    max u w, max u w} A G
  let : EnoughInjectives (Rep.{max u w} A G) := E.enoughInjectives_iff.mpr inferInstance
```

## New

Withdraw lean/Sheaf/RepresentationTheory/RepresentationLiftedGroupAlgebraEquivalence.lean.
Use WeilConjectures.RepresentationTheory.RepresentationLiftedGroupAlgebraEquivalence,
whose original theorem has the identical signature above. The upstream source is
unchanged. Remove the unused anyUniverse extension and all its private construction.
Point the existing DAG node at the original upstream theorem only.

The direct consumer now contains:

```lean
  let : Small.{max u w} G := small_max G
  let A₀ := Shrink.{max u w} A
  obtain ⟨E⟩ := Rep.representation_liftedGroupAlgebra_equivalence.{max u w, u, w} A₀ G
  let : EnoughInjectives (Rep.{max u w} A₀ G) := E.enoughInjectives_iff.mpr inferInstance
  let e : Action (ModuleCat.{max u w} A) G ≌ Action (ModuleCat.{max u w} A₀) G :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (show A₀ ≃+* A from Shrink.ringEquiv.{max u w, v} A)).mapAction G
  let E₀ : Rep.{max u w} A G ≌ Rep.{max u w} A₀ G :=
    (Rep.repIsoAction A G).trans (e.trans (Rep.repIsoAction A₀ G).symm)
  let : EnoughInjectives (Rep.{max u w} A G) := E₀.enoughInjectives_iff.mpr inferInstance
```

The equivalence from representations over A to representations over its small ring
model is the composite of Rep.repIsoAction, the module restriction equivalence lifted
to group actions by Equivalence.mapAction, and the inverse Rep.repIsoAction. Transfer
enough injectives through this equivalence. Every statement, definition and public
import of the consumer stays verbatim; only its private import and theorem proof change.

## Users

The current import graph has one direct consumer and nine transitive consumers.
The second consumer in the retirement inventory,
Sheaf.RepresentationTheory.DiscreteContinuousFunctorialInjectives, has already been
retired and is absent; its upstream twin already imports the upstream equivalence.
The generalized theorem occurs only in the retired module and the adapted consumer.
No upstream consumer is changed. No Challenge declaration is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DiscreteModulesAbelian | unclaimed | Private import redirected and proof adapted; exact public signatures preserved. |
| Sheaf.RepresentationTheory.ContinuousCochainsDeltaFunctor | unclaimed | Transitive consumer; public interface preserved, no adaptation. |
| Sheaf.RepresentationTheory.ContinuousCochainsDerivedInvariants | unclaimed | Transitive consumer; public interface preserved, no adaptation. |
| Sheaf.RepresentationTheory.ContinuousCochainsInvariantsZero | unclaimed | Transitive consumer; public interface preserved, no adaptation. |
| Sheaf.RepresentationTheory.DiscreteContinuousCohomology | unclaimed | Transitive consumer; public interface preserved, no adaptation. |
| Sheaf.RepresentationTheory.DvrGalois | unclaimed | Transitive consumer; public interface preserved, no adaptation. |
| Sheaf.RepresentationTheory.DvrGaloisComparison | unclaimed | Transitive consumer; public interface preserved, no adaptation. |
| Sheaf.RepresentationTheory.DvrGaloisProcyclic | unclaimed | Transitive consumer; public interface preserved, no adaptation. |
| Sheaf.RepresentationTheory.KernelInvariantsCohomology | unclaimed | Transitive consumer; public interface preserved, no adaptation. |
| Sheaf.RepresentationTheory.ProcyclicTwoTerm | unclaimed | Transitive consumer; public interface preserved, no adaptation. |

## Status

landed 20261020T144251-L-2259748 2026-10-20 (merge of deliver/J2/Sheaf.RepresentationTheory.RepresentationLiftedGroupAlgebraEquivalence)
