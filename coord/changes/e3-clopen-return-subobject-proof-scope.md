# AlgebraicGeometry.WeilSheaf.exists_lisse_subobject_clopen_return

## Reason

Record the proof-scope command difference flagged by preflight. The item adds
`Endofunctor` to its open namespaces and opens the pro-etale notation scope for its
proved private assembly helpers. It also adds private proof imports and helpers.
The theorem signature, visibility, attributes and public imports are preserved.
No existing definition, instance or statement changes, and no target meaning changes.
The new construction and properties are in new `Sheaf.DeligneLaumon` modules.

## Old

```lean
open CategoryTheory Limits
theorem exists_lisse_subobject_clopen_return
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    [Algebra k₀ k₁] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X C : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [C.Over (Spec (CommRingCat.of k₁))]
    [Smooth (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₁))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₁))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k₁))]
    (c : C ⟶ X) [IsOpenImmersion c] [IsClosedImmersion c]
    (hc : c ≫ (X ↘ Spec (CommRingCat.of k₀)) =
      (C ↘ Spec (CommRingCat.of k₁)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)))
    (r : ℕ) (hr : Nat.card k₁ = Nat.card k₀ ^ r)
    (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    (hp : v ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
      (C ↘ Spec (.of k₁)).geometricFiberProj ≫ c)
    (hb : v ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure =
      (C ↘ Spec (.of k₁)).geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₁).symm.toRingHom))
    (hv : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫ v =
      v ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom)
    (V : WeilSheaf k₀ l X) (hV : V.IsLisse)
    (G : WeilSheaf k₁ l C) (hG : G.IsLisse)
    (i : G ⟶ (poweredGeometricPullback v r hv).obj V) [Mono i] :
    ∃ (U : WeilSheaf k₀ l X) (j : U ⟶ V), Mono j ∧ U.IsLisse ∧
      ∃ e : (poweredGeometricPullback v r hv).obj U ≅ G,
        (poweredGeometricPullback v r hv).map j = e.hom ≫ i
```

## New

```lean
open CategoryTheory Limits Endofunctor
open scoped AlgebraicGeometry.ProEtale
theorem exists_lisse_subobject_clopen_return
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    [Algebra k₀ k₁] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X C : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [C.Over (Spec (CommRingCat.of k₁))]
    [Smooth (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₁))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₁))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k₁))]
    (c : C ⟶ X) [IsOpenImmersion c] [IsClosedImmersion c]
    (hc : c ≫ (X ↘ Spec (CommRingCat.of k₀)) =
      (C ↘ Spec (CommRingCat.of k₁)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)))
    (r : ℕ) (hr : Nat.card k₁ = Nat.card k₀ ^ r)
    (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    (hp : v ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
      (C ↘ Spec (.of k₁)).geometricFiberProj ≫ c)
    (hb : v ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure =
      (C ↘ Spec (.of k₁)).geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₁).symm.toRingHom))
    (hv : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫ v =
      v ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom)
    (V : WeilSheaf k₀ l X) (hV : V.IsLisse)
    (G : WeilSheaf k₁ l C) (hG : G.IsLisse)
    (i : G ⟶ (poweredGeometricPullback v r hv).obj V) [Mono i] :
    ∃ (U : WeilSheaf k₀ l X) (j : U ⟶ V), Mono j ∧ U.IsLisse ∧
      ∃ e : (poweredGeometricPullback v r hv).obj U ≅ G,
        (poweredGeometricPullback v r hv).map j = e.hom ≫ i
```

## Users

`python3 -B tools/downstream.py Sheaf.DeligneLaumon.ClopenReturnSubobject
--uses exists_lisse_subobject_clopen_return` finds two textual users, including the
item itself, and 31 transitive downstream modules. The signature and public imports
are unchanged. The only direct importer is checked against the delivery unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.ClopenReturnSubobject | E3 | Original signature preserved; proof supplied from the explicit saturation and its properties. |
| Sheaf.DeligneLaumon.ClopenReturnRestriction | unclaimed (A8 delivery landed) | Existing theorem application unchanged; compile checked against this delivery. |

No consumer is adapted. No target statement or definition is changed, so no semantic
target review is reopened by the scope commands.

## Status

landed 20261026T222623-L-674798 2026-10-26 (merge of deliver/E3/Sheaf.DeligneLaumon.ClopenReturnSubobject)
