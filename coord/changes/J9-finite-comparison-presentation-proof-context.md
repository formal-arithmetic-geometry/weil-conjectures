# AlgebraicGeometry.ProEtale.finiteComparisonPresentation

## Reason

The complete proof needs private equivalences, finite-presentation and local-model
comparisons, and tensor/derived transport helpers. The interface checker flags the
new `variable`, `open`, `attribute`, and option commands. This record documents that
proof context for independent review. The public theorem signature and all three
original public imports remain verbatim. No public definition changes.

All nine new proof instances are explicitly `private local instance`. Their
registrations end with their enclosing section. The realization monoidal instance
is enabled locally again after `InternalRealization` for the later Tor proof. The
two isomorphism-closure instances are enabled only around the final theorem.
No new global instance registration is exported.

The private proof section excludes seven imported integral-coefficient instances
whose universe parameters are undetermined in these comparisons, and supplies the
same sheafification/locally-bijective constructions at the required universes.
The final declaration repeats that exclusion using `attribute ... in`. Local
instance and irreducibility attributes cache the fixed coefficient and tensor
interfaces. The elaboration options and namespace openings are file-local proof
context. They introduce no notation or changed coefficient object downstream.

## Old

```lean
theorem finiteComparisonPresentation (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom] :
    let A := ULift.{u + 1} B
    letI : IsNoetherianRing A := inferInstance
    letI : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A)) :=
      HasDerivedCategory.standard _
    let P : ObjectProperty (ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :=
      fun K ↦ Scheme.IsCoefficientBoundedConstructibleEtale.{u, u + 1} X A K ∧
        ∃ a b : ℤ, HasCoefficientModelTorAmplitude _ K a b
    let Q : ObjectProperty (ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A)) :=
      fun K ↦ coefficientBoundedConstructibleProEtale.{u, u + 1} X A K ∧
        Scheme.HasFiniteCoefficientProEtaleTorAmplitude.{u, u + 1} X A K
    P.map (finiteComparisonEtaleModelRealization X A).mapDerivedCategory =
        finiteComparisonEtaleGenerators B X ∧
    Q.map (finiteComparisonProEtaleModelRealization X A).mapDerivedCategory =
        finiteComparisonProEtaleGenerators B eR X := by
  sorry
```

There was no private helper section or additional proof-only import.

## New

```lean
theorem finiteComparisonPresentation (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom] :
    let A := ULift.{u + 1} B
    letI : IsNoetherianRing A := inferInstance
    letI : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A)) :=
      HasDerivedCategory.standard _
    let P : ObjectProperty (ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :=
      fun K ↦ Scheme.IsCoefficientBoundedConstructibleEtale.{u, u + 1} X A K ∧
        ∃ a b : ℤ, HasCoefficientModelTorAmplitude _ K a b
    let Q : ObjectProperty (ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A)) :=
      fun K ↦ coefficientBoundedConstructibleProEtale.{u, u + 1} X A K ∧
        Scheme.HasFiniteCoefficientProEtaleTorAmplitude.{u, u + 1} X A K
    P.map (finiteComparisonEtaleModelRealization X A).mapDerivedCategory =
        finiteComparisonEtaleGenerators B X ∧
    Q.map (finiteComparisonProEtaleModelRealization X A).mapDerivedCategory =
        finiteComparisonProEtaleGenerators B eR X := by
  dsimp only
  constructor
  · let : (finiteComparisonEtaleGenerators B X).IsClosedUnderIsomorphisms := by
      unfold finiteComparisonEtaleGenerators
      infer_instance
    apply map_eq_of_equivalence
    intro K
    exact and_congr (coefficient_etale_bounded X (ULift.{u + 1} B) K)
      (coefficient_etale_finiteTor X (ULift.{u + 1} B) K)
  · let : (finiteComparisonProEtaleGenerators B eR X).IsClosedUnderIsomorphisms := by
      change ((constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} B) X ⊓
        _root_.DerivedCategory.finiteTorAmplitude _).inverseImage
          (finiteComparisonRealization B X eR).mapDerivedCategory).IsClosedUnderIsomorphisms
      infer_instance
    apply map_eq_of_equivalence
    intro K
    exact and_congr (coefficient_pro_bounded B X eR K)
      (coefficient_pro_finiteTor B X eR K)
```

The proved private helpers precede this declaration in `FiniteComparisonProof`.
They construct the ordinary/internal constant modules explicitly, compare their
realizations by actual isomorphisms, and prove constructibility and finite-Tor
transport. Proved generic existence interfaces keep the tensor data construction
small enough for a single-file compile. None of these helpers has a `sorry`.
The module's additional imports are proof-only, including `import all` where the
proof needs an existing private construction or fixed-universe instance name.
No adopted source module is edited.

## Users

`tools/downstream.py Sheaf.Paper.FiniteComparisonPresentation --uses
AlgebraicGeometry.ProEtale.finiteComparisonPresentation` finds seven downstream
modules. Only `FiniteComparisonLocalizing` mentions the theorem directly. All
public predicates, definitions, signatures, and original public imports are
unchanged, so these consumers need no adaptation. No target interpretation changes
and no target statement review is reopened by a changed definition.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteComparisonPresentation | J9 | Proves the unchanged statement using private proof context. |
| Sheaf.Paper.FiniteComparisonLocalizing | unclaimed | Uses the unchanged theorem; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin | unclaimed | Transitive importer; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization | unclaimed | Transitive importer; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Transitive importer; no adaptation. |
| Sheaf.SixFunctors.FiniteCompactProetale | unclaimed | Transitive importer; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Transitive importer; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Transitive importer; no adaptation. |

Claim holders above were checked in the current shared claim records. No other
module is included or modified in this delivery.

## Status

landed 20261022T013423-L-3571527 2026-10-22 (merge of deliver/J9/Sheaf.Paper.FiniteComparisonPresentation)
