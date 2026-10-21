# AlgebraicGeometry.ProEtale.finiteDiscreteCtfOrigin

## Reason

Restore the module listed in `coord/rework.tsv` from its quarantine archive, preserving
its Lean attachment, statement, and public imports. Use the existing finite-Tor generator
identification directly in place of reflection followed by repeated bounded devissage.
There is no definition or public signature change and no consumer adaptation is required.
The restoration adds no holes; the archived proof already had zero holes.

## Old

The module is absent from `lean/` and preserved in
`quarantine/Sheaf/AlgebraicGeometry/FiniteDiscreteCtfOrigin.lean` with this signature:

```lean
theorem finiteDiscreteCtfOrigin
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
        Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]
    (K : DerivedCategory (pulledBackModuleObjects
      (Profinite.continuousMapRingObj A) X))
    (hK : (constantModelBoundedConstructible (Profinite.continuousMapRingObj A) X ⊓
      fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M) K) :
    ∃ L : Etale.DerivedCategoryModule (ULift.{u + 1} A) X,
      Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) X L ∧
      (∃ a b : ℤ, a ≤ b ∧
        Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) X a b L) ∧
      Nonempty (((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory ⋙
        (finiteComparisonRealization A X eR).mapDerivedCategory).obj L ≅ K)
```

## New

The restored theorem keeps exactly the same signature:

```lean
theorem finiteDiscreteCtfOrigin
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
        Profinite.continuousMapRingObj.{u} A) [IsMonHom eR.hom]
    (K : DerivedCategory (pulledBackModuleObjects
      (Profinite.continuousMapRingObj A) X))
    (hK : (constantModelBoundedConstructible (Profinite.continuousMapRingObj A) X ⊓
      fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M) K) :
    ∃ L : Etale.DerivedCategoryModule (ULift.{u + 1} A) X,
      Etale.DerivedCategory.isBoundedConstructible (ULift.{u + 1} A) X L ∧
      (∃ a b : ℤ, a ≤ b ∧
        Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) X a b L) ∧
      Nonempty (((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory ⋙
        (finiteComparisonRealization A X eR).mapDerivedCategory).obj L ≅ K)
```

All three public imports are preserved verbatim. The proved private helper
`fixedCtfOrigin` and its three now-unused proof imports are removed. The proof uses the
already stated `finiteComparisonGenerators_identification`, orders its Tor interval,
and composes the actual derived comparison isomorphisms. The new private proof import
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel` supplies the existing
Tor-predicate conversion lemma, avoiding expansion of the derived tensor definition.
No upstream source file changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.FiniteCompactProetale | unclaimed; quarantined | Both calls keep their exact hypotheses and four-part existential result; no adaptation. |

`tools/downstream.py` reports the module unknown because it is currently quarantined.
A source search over `lean/` and `quarantine/` finds only the two calls in the consumer
listed above. Its DAG parent `det-ctf-finite-compact-proetale` still names this node;
this is a restoration, never a withdrawal.

## Status

landed 20261021T020052-L-2580695 2026-10-21 (merge of deliver/B2/Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin)
