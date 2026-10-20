# CartesianChartExchangeSource duplicate retirement

## Reason

The assigned module is a retirement item in coord/retire-items.tsv. The human's
2026-10-20 instruction in coord/changes/retire-sheaf-twins-20261020.md requires
using its official upstream twin and withdrawing the duplicate.

The three private lemmas natural_conjugate, square_single_naturality and
square_single_source have exactly the same signatures and complete proofs in
WeilConjectures.AlgebraicGeometry.CartesianChartExchangeSource. The text from
the first lemma through the namespace end agrees ignoring whitespace. There
are zero sorry holes in the duplicate. No upstream file is modified.

## Old

The assigned duplicate, verbatim:

```lean
module
public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeCoefficients
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeCore
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc
-- These comparison helpers are consumed through private proof imports.
set_option linter.privateModule false

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency true
set_option linter.unusedSimpArgs false
set_option linter.privateModule false

variable (A : Type (u + 2)) [Category.{u + 1} A]
  [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

private lemma natural_conjugate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (G : C ⥤ E) (H : D ⥤ F) (L : C ⥤ D) (L' : E ⥤ F)
    (θ : G ⋙ L' ⟶ L ⋙ H) {A A₀ : C}
    (eh : A ⟶ A₀) (ei : A₀ ⟶ A) (hi : eh ≫ ei = 𝟙 A) :
    L'.map (G.map eh) ≫ θ.app A₀ ≫ H.map (L.map ei) = θ.app A := by
  have hn := θ.naturality eh
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp, hi, CategoryTheory.Functor.map_id, Category.comp_id]

private lemma square_single_naturality {B T T' Z Z' : Scheme.{u}}
    (t : Z' ⟶ Z) (p : Z ⟶ T) (p' : Z' ⟶ T') (b : T' ⟶ T)
    (θ : D+((b)^*[A]) ⋙ D+((p')^*[A]) ⟶ D+((p)^*[A]) ⋙ D+((t)^*[A]))
    (a : T ⟶ B)
    (M : Sheaf B.smallEtaleTopology A) :
    D+((p')^*[A]).map
      (D+((b)^*[A]).map
        ((((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app M)) ≫
    θ.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((a)^*[A]).obj M)) ≫
    D+((t)^*[A]).map
      (D+((p)^*[A]).map
        ((((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app M)) =
    θ.app
      (D+((a)^*[A]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M)) := by
  exact natural_conjugate D+((b)^*[A]) D+((t)^*[A]) D+((p)^*[A]) D+((p')^*[A]) θ
    ((((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app M)
    ((((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app M)
    (Iso.hom_inv_id_app (((a)^*[A]).mapDerivedCategoryPlusSingleFunctor 0) M)

private lemma square_single_source {B T T' Z Z' : Scheme.{u}}
    (t : Z' ⟶ Z) (p : Z ⟶ T) (p' : Z' ⟶ T') (b : T' ⟶ T)
    (sq : CommSq t p' p b) (a : T ⟶ B) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (s : Z ⟶ B) (hs : s = p ≫ a) (s' : Z' ⟶ B) (hs' : s' = p' ≫ a')
    (M : Sheaf B.smallEtaleTopology A) :
    D+((p')^*[A]).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp A b a a' ha).hom.app M) ≫
          (((b)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _) ≫
      (pullbackSquareComparison A sq).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((a)^*[A]).obj M)) ≫
      D+((t)^*[A]).map
        ((((p)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp A p a s hs).inv.app M)) =
    (((p')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp A p' a' s' hs').inv.app M) ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp A t s s'
          (by rw [hs', ha, ← Category.assoc p' b a, ← sq.w, Category.assoc, ← hs])).hom.app M) ≫
      (((t)^*[A]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ := by
  rw [single_source A b a a' ha M, single_restriction A p a s hs M]
  rw [reassoc_of% (single_restriction A p' a' s' hs' M)]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (square_single_naturality A t p p' b
    (pullbackSquareComparison A sq).hom a M)]
  rw [reassoc_of% (square_comp A t p p' b sq a a' ha s hs s' hs'
    ((DerivedCategory.Plus.singleFunctor _ 0).obj M))]
  rw [single_source A t s s'
    (by rw [hs', ha, ← Category.assoc p' b a, ← sq.w, Category.assoc, ← hs]) M]
  simp only [Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, Category.comp_id]

end AlgebraicGeometry.Etale
```

Its sole direct consumer, Sheaf.AlgebraicGeometry.CartesianChartExchangeAdjunction,
uses the final lemma in actualAdjunct_pullback and imports:

```lean
import all Sheaf.AlgebraicGeometry.CartesianChartExchangeSource
```

## New

The assigned duplicate is withdrawn through deleted.txt. Its sole direct
consumer instead imports:

```lean
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeSource
```

This is the only changed line in the consumer. Every declaration, statement,
proof, definition and public import in that consumer is preserved. The upstream
module supplies the identical private lemma through import all. All upstream
signatures, attributes, imports and bodies are preserved.

There is no reference to CartesianChartExchangeSource in any DAG JSON record,
including unit and chapter records, or in quarantined Lean files. Consequently
there is no Lean node attachment or parent dependency to redirect. No target
statement, mathematical definition or unit route changes.

## Users

The table includes the item and all seven transitive importers returned by
python3 tools/downstream.py with --uses square_single_source. The other six
consumers require no edits. The consumer is unclaimed in the coordination
snapshot; its adaptation is required to remove the withdrawn import.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeSource | U2 | Withdraw duplicate; use official implementation. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeAdjunction | unclaimed | Change only the private Source import. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison | unclaimed | No edit; compile against migrated consumer. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeEvaluation | unclaimed | No edit; compile against migrated consumer. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeTransport | unclaimed | No edit; compile against migrated consumer. |
| Sheaf.AlgebraicGeometry.CartesianChartLiftCoherence | unclaimed | No edit; compile against migrated consumer. |
| Sheaf.AlgebraicGeometry.CartesianChartLiftNaturality | unclaimed | No edit; compile against migrated consumer. |
| Sheaf.AlgebraicGeometry.CartesianChartLiftRawNaturality | unclaimed | No edit; compile against migrated consumer. |

The seven consumers compiled successfully individually through lcompile.py, in import
order with the migrated Adjunction module in the sandbox overlay. Import-closure
comparison introduces no new Sheaf/WeilConjectures twin pairs. It removes the
Source twin pair from all three Lift consumers. None of the seven consumer
closures still reaches the retired Source module. The unchanged LiftRawNaturality
and LiftNaturality files emitted their existing style warnings for long lines
and letI; neither file is modified or included in this delivery.

## Status

landed 20261020T174900-L-815145 2026-10-20 (merge of deliver/U2/Sheaf.AlgebraicGeometry.CartesianChartExchangeSource)
