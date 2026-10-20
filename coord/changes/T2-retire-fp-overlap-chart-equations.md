# AlgebraicGeometry.exists_finitePresentation_overlap_eventual_chart_equations

## Reason

This module is explicitly listed for duplicate retirement in coord/retire-items.tsv.
Both implementations already have complete proofs and zero local holes. Their full
signatures differ only in the Sheaf version's unused Noetherian instance binder;
the existing upstream theorem specializes to the complete old statement. The
proof bodies and proof dependencies are identical. Retire the duplicate and use
the existing upstream declaration. No upstream source file is changed.

## Old

Declared in Sheaf.AlgebraicGeometry.FinitePresentationOverlapChartEquations:

```lean
theorem exists_finitePresentation_overlap_eventual_chart_equations
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
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
        ∃ (l : I) (hkl : k ≤ l),
          let q := overlapStageMap R f hij (hjk.trans hkl)
          let V : (pullback f (Spec.map
              (R.map (homOfLE (hij.trans (hjk.trans hkl)))))).OpenCover.{u} :=
            U.pullback₁ q
          let r := overlapStageMap R f (hij.trans hjk) hkl
          let s := overlapRefinementHom U q₀ q r
            (overlapStageMap_comp R f hij hjk hkl)
          let T' := T.pull (p := r) (α := fun a ↦ a) (p' := s)
            (fun a ↦ overlapRefinementHom_map U q₀ q r
              (overlapStageMap_comp R f hij hjk hkl) a)
          ∃ sq : ∀ a b, ChosenPullback (V.f a) (V.f b),
          ∃ sq₃ : ∀ a b d, ChosenPullback₃ (sq a b) (sq b d) (sq a d),
            (∀ a, T'.hom (V.f a) (𝟙 _) (𝟙 _) (Category.id_comp _) (Category.id_comp _) = 𝟙 _) ∧
            (∀ a b d,
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₂
                (sq₃ a b d).w₁ (sq₃ a b d).w₂ ≫
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₂ (sq₃ a b d).p₃
                (sq₃ a b d).w₂ (sq₃ a b d).w₃ =
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₃
                (sq₃ a b d).w₁ (sq₃ a b d).w₃)
```

The sole direct consumer privately imports the Sheaf module.

## New

Use the existing declaration in
WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapChartEquations:

```lean
theorem exists_finitePresentation_overlap_eventual_chart_equations
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
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
        ∃ (l : I) (hkl : k ≤ l),
          let q := overlapStageMap R f hij (hjk.trans hkl)
          let V : (pullback f (Spec.map
              (R.map (homOfLE (hij.trans (hjk.trans hkl)))))).OpenCover.{u} :=
            U.pullback₁ q
          let r := overlapStageMap R f (hij.trans hjk) hkl
          let s := overlapRefinementHom U q₀ q r
            (overlapStageMap_comp R f hij hjk hkl)
          let T' := T.pull (p := r) (α := fun a ↦ a) (p' := s)
            (fun a ↦ overlapRefinementHom_map U q₀ q r
              (overlapStageMap_comp R f hij hjk hkl) a)
          ∃ sq : ∀ a b, ChosenPullback (V.f a) (V.f b),
          ∃ sq₃ : ∀ a b d, ChosenPullback₃ (sq a b) (sq b d) (sq a d),
            (∀ a, T'.hom (V.f a) (𝟙 _) (𝟙 _) (Category.id_comp _) (Category.id_comp _) = 𝟙 _) ∧
            (∀ a b d,
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₂
                (sq₃ a b d).w₁ (sq₃ a b d).w₂ ≫
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₂ (sq₃ a b d).p₃
                (sq₃ a b d).w₂ (sq₃ a b d).w₃ =
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₃
                (sq₃ a b d).w₁ (sq₃ a b d).w₃)
```

Withdraw the Sheaf module with deleted.txt. Change only line 11 of the direct
consumer, from the Sheaf private proof import to the upstream private proof import.
Keep all consumer signatures and proof bodies verbatim. Reattach
lem-pc-fp-overlap-eventual-chart-equations to the existing upstream theorem, recording
its full upstream signature. Keep the node's mathematical statement, proof steps,
proof dependencies, and all parent dependencies unchanged. The unit route is
preserved by the same theorem with the same proof.

## Users

Exact import/declaration searches cover both library roots and quarantine/.
The DAG parent lem-pc-fp-overlap-eventual-coherence still depends on the same node;
other occurrences in child nodes are provenance, not proof dependency edges.
The unit sk-thm-picard-semicon has no realized entry for this node. The direct
consumer has no claim in the shared snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FinitePresentationOverlapChartEquations | T2 | Retire duplicate and reattach its node upstream. |
| Sheaf.AlgebraicGeometry.FinitePresentationOverlapCoherence | unclaimed | Swap one private proof import; signatures and proofs unchanged. |

The exact old signature was compiled as a scratch theorem proved by application
of the upstream theorem. Its printed axioms are propext, Classical.choice, and
Quot.sound. The adapted consumer also compiled successfully through lcompile.py.
No target statement or definition changes, so target statement review does not
reopen. The existing upstream theorem and all its dependencies remain present.

## Status

landed 20261020T163702-L-3786302 2026-10-20 (merge of deliver/T2/Sheaf.AlgebraicGeometry.FinitePresentationOverlapChartEquations)
