# AlgebraicGeometry.finitePresentation_overlap_diagonal_eventually

## Reason

The item is listed as a retirement in coord/retire-items.tsv. Its Sheaf module
has zero holes and duplicates the proved upstream theorem. The upstream theorem
has precisely the same signature except for omitting the Noetherian instance.
Its identity-defect argument, canonical refinements, and persistence conclusion
are unchanged. Redirect the sole direct consumer to the upstream module and
withdraw the redundant Sheaf module. No upstream source is edited.

## Old

Declared in Sheaf.AlgebraicGeometry.FinitePresentationOverlapDiagonalEventually:

```lean
theorem finitePresentation_overlap_diagonal_eventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
    (a : U.I₀)
    (hN : ∀ a, (N a).IsFinitePresentation) (hNq : ∀ a, (N a).IsQuasicoherent)
    :
    ∀ (k : I) (hjk : j ≤ k),
      let q₀ := overlapStageMap R f hij hjk
      let V₀ : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} :=
        U.pullback₁ q₀
      let p₀ := overlapLimitMap R c f (hij.trans hjk)
      ∀ T : modulesPseudofunctor.OverlapTransitions V₀.f,
        (∀ a, Nonempty ((T.obj a : (V₀.X a).Modules) ≅
          (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj (N a))) →
        (T.pull (p := p₀) (α := fun a ↦ a)
          (fun a ↦ V₀.pullbackHom_map p₀ a)).Coherent →
        ∃ (l : I) (hkl : k ≤ l), ∀ (m : I) (hkm : k ≤ m), l ≤ m →
          let q := overlapStageMap R f hij (hjk.trans hkm)
          let V : (pullback f (Spec.map
              (R.map (homOfLE (hij.trans (hjk.trans hkm)))))).OpenCover.{u} :=
            U.pullback₁ q
          let r := overlapStageMap R f (hij.trans hjk) hkm
          let s := overlapRefinementHom U q₀ q r
            (overlapStageMap_comp R f hij hjk hkm)
          let T' := T.pull (p := r) (α := fun a ↦ a) (p' := s)
            (fun a ↦ overlapRefinementHom_map U q₀ q r
              (overlapStageMap_comp R f hij hjk hkm) a)
          T'.hom (V.f a) (𝟙 _) (𝟙 _) (Category.id_comp _) (Category.id_comp _) = 𝟙 _
```

## New

Use the existing declaration in
WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapDiagonalEventually:

```lean
theorem finitePresentation_overlap_diagonal_eventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
    (a : U.I₀)
    (hN : ∀ a, (N a).IsFinitePresentation) (hNq : ∀ a, (N a).IsQuasicoherent)
    :
    ∀ (k : I) (hjk : j ≤ k),
      let q₀ := overlapStageMap R f hij hjk
      let V₀ : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} :=
        U.pullback₁ q₀
      let p₀ := overlapLimitMap R c f (hij.trans hjk)
      ∀ T : modulesPseudofunctor.OverlapTransitions V₀.f,
        (∀ a, Nonempty ((T.obj a : (V₀.X a).Modules) ≅
          (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj (N a))) →
        (T.pull (p := p₀) (α := fun a ↦ a)
          (fun a ↦ V₀.pullbackHom_map p₀ a)).Coherent →
        ∃ (l : I) (hkl : k ≤ l), ∀ (m : I) (hkm : k ≤ m), l ≤ m →
          let q := overlapStageMap R f hij (hjk.trans hkm)
          let V : (pullback f (Spec.map
              (R.map (homOfLE (hij.trans (hjk.trans hkm)))))).OpenCover.{u} :=
            U.pullback₁ q
          let r := overlapStageMap R f (hij.trans hjk) hkm
          let s := overlapRefinementHom U q₀ q r
            (overlapStageMap_comp R f hij hjk hkm)
          let T' := T.pull (p := r) (α := fun a ↦ a) (p' := s)
            (fun a ↦ overlapRefinementHom_map U q₀ q r
              (overlapStageMap_comp R f hij hjk hkm) a)
          T'.hom (V.f a) (𝟙 _) (𝟙 _) (Category.id_comp _) (Category.id_comp _) = 𝟙 _
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FinitePresentationOverlapDiagonalEventually | B8 | Withdraw duplicate; node attaches upstream. |
| Sheaf.AlgebraicGeometry.FinitePresentationOverlapChartEquations | unclaimed | Replace one private import; declaration signatures and proof unchanged. |
| Sheaf.AlgebraicGeometry.FinitePresentationOverlapCoherence | unclaimed | Indirect consumer; no edit or statement change needed. |

The consumer retains its Noetherian assumption and applies the upstream theorem
with identical explicit arguments. The consumer is checked by remote compilation.
No target statement or definition changes, so no target statement review reopens.

## Status

landed 20261020T141303-L-2032026 2026-10-20 (merge of deliver/B8/Sheaf.AlgebraicGeometry.FinitePresentationOverlapDiagonalEventually)
