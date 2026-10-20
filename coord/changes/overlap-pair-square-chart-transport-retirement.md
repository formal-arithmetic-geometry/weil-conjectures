# AlgebraicGeometry.overlap_pair_square_chart_transport

## Reason

Retire the Sheaf copy in favour of the adopted source module, as assigned by
`coord/retire-items.tsv` (the row for this item) and the human's hand-off in
`coord/changes/retire-sheaf-twins-20261020.md`.
Both files already contain a complete proof. The upstream theorem drops only
`hp : p' ≫ r = p`; the old proof used it only in `have _ := hp`.
The explicit chart equations `hδf` and `hδv` already provide all compatibility
needed by the categorical transport calculation. Its chosen pair map and conclusion
are otherwise identical. This is retirement of duplicate proved code, not a new proof
or a decomposition. No adopted source file or target changes.

## Old

The Sheaf module publicly imported
`WeilConjectures.AlgebraicGeometry.OverlapPairCanonicalComparisons` and declared:

```lean
theorem overlap_pair_square_chart_transport
    {Y Y' Z : Scheme.{u}} (V : Y.OpenCover.{u}) (V' : Y'.OpenCover.{u})
    (α : V'.I₀ → V.I₀) (r : Y' ⟶ Y) (ρ : ∀ d, V'.X d ⟶ V.X (α d))
    (hr : ∀ d, ρ d ≫ V.f (α d) = V'.f d ≫ r)
    (p : Z ⟶ Y) (p' : Z ⟶ Y') (hp : p' ≫ r = p)
    (A : (d : V.I₀) → (V.X d).Modules)
    (A' : (d : V'.I₀) → (V'.X d).Modules) (M : Z.Modules)
    (c : ∀ d, (Scheme.Modules.pullback (ρ d)).obj (A (α d)) ≅ A' d)
    (δ : ∀ d, (V'.pullback₁ p').X d ⟶ (V.pullback₁ p).X (α d))
    (hδf : ∀ d, δ d ≫ (V.pullback₁ p).f (α d) = (V'.pullback₁ p').f d)
    (hδv : ∀ d, δ d ≫ V.pullbackHom p (α d) = V'.pullbackHom p' d ≫ ρ d)
    (ε : ∀ d, (Scheme.Modules.pullback (V.pullbackHom p d)).obj (A d) ≅
      (Scheme.Modules.pullback ((V.pullback₁ p).f d)).obj M)
    (ε' : ∀ d, (Scheme.Modules.pullback (V'.pullbackHom p' d)).obj (A' d) ≅
      (Scheme.Modules.pullback ((V'.pullback₁ p').f d)).obj M)
    (hε : ε' =
    (fun d ↦ (Scheme.Modules.pullback (V'.pullbackHom p' d)).mapIso (c d).symm ≪≫
      pullbackCompOfEq (V'.pullbackHom p' d) (ρ d)
        (δ d ≫ V.pullbackHom p (α d)) (hδv d).symm (A (α d)) ≪≫
      (pullbackCompOfEq (δ d) (V.pullbackHom p (α d))
        (δ d ≫ V.pullbackHom p (α d)) rfl (A (α d))).symm ≪≫
      (Scheme.Modules.pullback (δ d)).mapIso (ε (α d)) ≪≫
      pullbackCompOfEq (δ d) ((V.pullback₁ p).f (α d))
        ((V'.pullback₁ p').f d) (hδf d) M))
    (a b : V'.I₀)
    (φ : (Scheme.Modules.pullback (pullback.fst (V.f (α a)) (V.f (α b)))).obj
        (A (α a)) ⟶
      (Scheme.Modules.pullback (pullback.snd (V.f (α a)) (V.f (α b)))).obj
        (A (α b)))
    (hs : overlapPairSquare V A p
      ((modulesPseudofunctor.toDescentData (V.pullback₁ p).f).obj M) ε (α a) (α b) φ) :
    overlapPairSquare V' A' p'
      ((modulesPseudofunctor.toDescentData (V'.pullback₁ p').f).obj M)
      ε' a b
      ((Scheme.Modules.pullback (pullback.fst (V'.f a) (V'.f b))).map (c a).inv ≫
        modulesPseudofunctor.overlapPairBaseChangeHom
          (V.f (α a)) (V.f (α b)) r (ρ a) (ρ b) (V'.f a) (V'.f b)
          (hr a) (hr b) (A (α a)) (A (α b)) φ ≫
        (Scheme.Modules.pullback (pullback.snd (V'.f a) (V'.f b))).map (c b).hom)
```

Its sole direct and transitive importer,
`Sheaf.AlgebraicGeometry.OverlapPairRefinementPersistence`, imported the Sheaf
module privately and applied the theorem with the extra argument `hp`.

## New

The Sheaf module is withdrawn through `deleted.txt`; landing retains an empty
module without declarations. The consumer instead privately imports
`WeilConjectures.AlgebraicGeometry.OverlapPairSquareChartTransport` and applies
its existing, unchanged theorem:

```lean
theorem overlap_pair_square_chart_transport
    {Y Y' Z : Scheme.{u}} (V : Y.OpenCover.{u}) (V' : Y'.OpenCover.{u})
    (α : V'.I₀ → V.I₀) (r : Y' ⟶ Y) (ρ : ∀ d, V'.X d ⟶ V.X (α d))
    (hr : ∀ d, ρ d ≫ V.f (α d) = V'.f d ≫ r)
    (p : Z ⟶ Y) (p' : Z ⟶ Y')
    (A : (d : V.I₀) → (V.X d).Modules)
    (A' : (d : V'.I₀) → (V'.X d).Modules) (M : Z.Modules)
    (c : ∀ d, (Scheme.Modules.pullback (ρ d)).obj (A (α d)) ≅ A' d)
    (δ : ∀ d, (V'.pullback₁ p').X d ⟶ (V.pullback₁ p).X (α d))
    (hδf : ∀ d, δ d ≫ (V.pullback₁ p).f (α d) = (V'.pullback₁ p').f d)
    (hδv : ∀ d, δ d ≫ V.pullbackHom p (α d) = V'.pullbackHom p' d ≫ ρ d)
    (ε : ∀ d, (Scheme.Modules.pullback (V.pullbackHom p d)).obj (A d) ≅
      (Scheme.Modules.pullback ((V.pullback₁ p).f d)).obj M)
    (ε' : ∀ d, (Scheme.Modules.pullback (V'.pullbackHom p' d)).obj (A' d) ≅
      (Scheme.Modules.pullback ((V'.pullback₁ p').f d)).obj M)
    (hε : ε' =
    (fun d ↦ (Scheme.Modules.pullback (V'.pullbackHom p' d)).mapIso (c d).symm ≪≫
      pullbackCompOfEq (V'.pullbackHom p' d) (ρ d)
        (δ d ≫ V.pullbackHom p (α d)) (hδv d).symm (A (α d)) ≪≫
      (pullbackCompOfEq (δ d) (V.pullbackHom p (α d))
        (δ d ≫ V.pullbackHom p (α d)) rfl (A (α d))).symm ≪≫
      (Scheme.Modules.pullback (δ d)).mapIso (ε (α d)) ≪≫
      pullbackCompOfEq (δ d) ((V.pullback₁ p).f (α d))
        ((V'.pullback₁ p').f d) (hδf d) M))
    (a b : V'.I₀)
    (φ : (Scheme.Modules.pullback (pullback.fst (V.f (α a)) (V.f (α b)))).obj
        (A (α a)) ⟶
      (Scheme.Modules.pullback (pullback.snd (V.f (α a)) (V.f (α b)))).obj
        (A (α b)))
    (hs : overlapPairSquare V A p
      ((modulesPseudofunctor.toDescentData (V.pullback₁ p).f).obj M) ε (α a) (α b) φ) :
    overlapPairSquare V' A' p'
      ((modulesPseudofunctor.toDescentData (V'.pullback₁ p').f).obj M)
      ε' a b
      ((Scheme.Modules.pullback (pullback.fst (V'.f a) (V'.f b))).map (c a).inv ≫
        modulesPseudofunctor.overlapPairBaseChangeHom
          (V.f (α a)) (V.f (α b)) r (ρ a) (ρ b) (V'.f a) (V'.f b)
          (hr a) (hr b) (A (α a)) (A (α b)) φ ≫
        (Scheme.Modules.pullback (pullback.snd (V'.f a) (V'.f b))).map (c b).hom)
```

The consumer retains every declaration signature, including the private
existential helper's `hp` argument. Its proof acknowledges this now unused
hypothesis with `have _ := hp`, then omits it from the source theorem call.
All other consumer code and its public imports remain unchanged.
The DAG attachment points to the actual source declaration with its verbatim
signature and notes that it implies the recorded statement without needing `hp`.
The source proof already follows all three existing DAG steps, so the node's
mathematical statement, dependencies and unit route remain unchanged.
No target definition or target meaning changes and no target review is reopened.

## Users

A source import scan found exactly one direct importer and one transitive importer.
A whole-library name search found no other use of the public theorem.
`tools/downstream.py Sheaf.AlgebraicGeometry.OverlapPairSquareChartTransport
--uses overlap_pair_square_chart_transport` was also run to verify this inventory.
The consumer is unclaimed; no module held by another group is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OverlapPairSquareChartTransport | T7 | Duplicate removed; theorem remains proved in the unchanged source twin. |
| Sheaf.AlgebraicGeometry.OverlapPairRefinementPersistence | unclaimed | Private import switches to the source twin; theorem application drops hp. Every declaration signature and public import stays identical. |

The adapted consumer compiles alone through `lcompile.py` (12.5 seconds).
A separate `#print axioms` check of the source transport theorem reports exactly
`propext`, `Classical.choice`, `Quot.sound` (4.5 seconds).

## Status

landed 20261020T150708-L-2575009 2026-10-20 (merge of deliver/T7/Sheaf.AlgebraicGeometry.OverlapPairSquareChartTransport)
