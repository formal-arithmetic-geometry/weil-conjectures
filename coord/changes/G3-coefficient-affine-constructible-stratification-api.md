# AlgebraicGeometry.Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf

## Reason

Restore the assigned quarantined module from the archive named in coord/rework.tsv.
Compiling that archive against the current published library fails at line 58:

```text
error(lean.unknownIdentifier): Unknown identifier `LocallyClosedStratification`
```

Use the current upstream `Scheme.Stratification`, provided by the existing public
import of `AffineLocallyConstructibleProEtaleModules`. The retirement record
`retire-sheaf-twins-20261020.md` explicitly records this name migration. Its fields
are the finite partition into locally closed constructible subsets, the realizing
schemes, and their immersions. The older `LocallyClosedStratification` extended
`Topology.Stratification` (see the current def-constructible-stratification node).
The original predicate already required constructibility explicitly, so retaining
that conjunct with the current structure neither strengthens nor weakens it.
No Noetherian assumption on the scheme is added, and no stratum is removed.

The fixed-scalar inverse image, all coefficient and module universes, affine-open
quantifier, covering-sieve quantifier, finite-presentation condition and local
module isomorphisms are preserved verbatim. All public imports are preserved.
This is an API repair of the existing definition, not a new constructibility notion.
The mathematical meanings used by targets are unchanged; target signatures are
untouched. The independent semantic reader should check the structure fields and
the retained explicit constructibility conjunct against Stacks Tag 09AJ.

## Old

```lean
def IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf (X : Scheme.{u})
    (R : Type (max v (u + 1))) [CommRing R] [IsNoetherianRing R]
    (F : CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X)
        R)) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U →
    ∃ S : LocallyClosedStratification U.toScheme,
      (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
      ∀ (a : Fin S.n) (V : coefficientProEtaleSiteModel.{u, v} (S.domain a)),
        ∃ T : Sieve V, T ∈ coefficientProEtaleModelTopology.{u, v} (S.domain a) V ∧
          ∀ (W : coefficientProEtaleSiteModel.{u, v} (S.domain a)) (f : W ⟶ V), T f →
            ∃ M : ModuleCat.{max v (u + 1)} R, Module.FinitePresentation R M ∧
              Nonempty
                ((((coefficientProEtaleFixedModulePullback.{u, v}
                    (S.immersion a ≫ U.ι) R).obj
                    ((coefficientModelFixedScalars _ R).obj F)).over W) ≅
                  (constantSheaf
                    ((coefficientProEtaleModelTopology.{u, v} (S.domain a)).over W)
                    (ModuleCat.{max v (u + 1)} R)).obj M)
```

## New

```lean
def IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf (X : Scheme.{u})
    (R : Type (max v (u + 1))) [CommRing R] [IsNoetherianRing R]
    (F : CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X)
        R)) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U →
    ∃ S : Stratification U.toScheme,
      (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
      ∀ (a : Fin S.n) (V : coefficientProEtaleSiteModel.{u, v} (S.domain a)),
        ∃ T : Sieve V, T ∈ coefficientProEtaleModelTopology.{u, v} (S.domain a) V ∧
          ∀ (W : coefficientProEtaleSiteModel.{u, v} (S.domain a)) (f : W ⟶ V), T f →
            ∃ M : ModuleCat.{max v (u + 1)} R, Module.FinitePresentation R M ∧
              Nonempty
                ((((coefficientProEtaleFixedModulePullback.{u, v}
                    (S.immersion a ≫ U.ι) R).obj
                    ((coefficientModelFixedScalars _ R).obj F)).over W) ≅
                  (constantSheaf
                    ((coefficientProEtaleModelTopology.{u, v} (S.domain a)).over W)
                    (ModuleCat.{max v (u + 1)} R)).obj M)
```

## Users

`tools/downstream.py` with `--allow-missing --uses
IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf
coefficientProEtaleFixedModulePullback` reports zero current library users because
the item and its three direct users are quarantined. A separate import and name
scan includes the quarantine archives, which remain needed and are not withdrawn.
The three direct archived users are listed below as well. The unchanged archived `CoefficientBoundedConstructibleProEtale` compiled on
the server against the repaired item in 3.3 seconds. Its temporary sandbox copy
was removed after checking. No consumer is edited or restored by this delivery. Their own retired-name occurrences are pre-existing
repair obligations, not failures introduced by this change. All uses of the two
item declarations retain their signatures and mathematical meanings.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules | G3 | Restore both definitions; migrate the retired stratification name. |
| Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale | unclaimed | Archived; its cohomology predicate uses only the unchanged public signature. |
| Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison | unclaimed | Archived; uses the predicate and unchanged pullback; its own old stratification names need the same existing migration independently. |
| Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility | unclaimed | Archived; uses the predicate and unchanged pullback; the current upstream constructible stratification is the one used by its gluing proof. Its own old stratification names need the existing migration independently. |

DAG parents remain `sk-thm-pe-constructible-comparison`,
`lem-sfb-noetherian-global-constructibility`, and
`lem-sfb-discrete-noetherian-constructible-serre`. Their dependency links and the
unit route are preserved. The last node uses the original affine-local predicate,
which remains publicly reexported as before.

## Status

landed 20261020T221155-L-4153708 2026-10-20 (merge of deliver/G3/Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules)
