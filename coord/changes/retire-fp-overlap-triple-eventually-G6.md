# AlgebraicGeometry.finitePresentation_overlap_triple_eventually

## Reason

The assigned module is the retirement item in coord/retire-items.tsv. It has zero
local holes and duplicates the existing upstream theorem. The upstream signature
omits only the unused Noetherian instance. Its full proof and all of its existing
source-library dependencies are preserved. The exact old statement specializes
from upstream, as checked by the sandbox specialization compile.

## Old

The declaration in Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleEventually:

```lean
theorem finitePresentation_overlap_triple_eventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
    (a b d : U.I₀)
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
          ∀ sq : ∀ x y, ChosenPullback (V.f x) (V.f y),
          ∀ sq₃ : ∀ x y z, ChosenPullback₃ (sq x y) (sq y z) (sq x z),
            T'.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₂
                (sq₃ a b d).w₁ (sq₃ a b d).w₂ ≫
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₂ (sq₃ a b d).p₃
                (sq₃ a b d).w₂ (sq₃ a b d).w₃ =
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₃
                (sq₃ a b d).w₁ (sq₃ a b d).w₃
```

The direct consumer privately imports
`Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleEventually`.

## New

Withdraw the duplicate via deleted.txt and attach the existing node to the existing
declaration in WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapTripleEventually:

```lean
theorem finitePresentation_overlap_triple_eventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
    (a b d : U.I₀)
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
          ∀ sq : ∀ x y, ChosenPullback (V.f x) (V.f y),
          ∀ sq₃ : ∀ x y z, ChosenPullback₃ (sq x y) (sq y z) (sq x z),
            T'.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₂
                (sq₃ a b d).w₁ (sq₃ a b d).w₂ ≫
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₂ (sq₃ a b d).p₃
                (sq₃ a b d).w₂ (sq₃ a b d).w₃ =
              T'.hom (sq₃ a b d).p (sq₃ a b d).p₁ (sq₃ a b d).p₃
                (sq₃ a b d).w₁ (sq₃ a b d).w₃
```

The direct consumer privately imports
`WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapTripleEventually` instead.
Exactly one import is swapped, on line 14 of the current live consumer.
The landed upstream diagonal import on line 13 is preserved.
Its declarations and proof bodies are unchanged. The mathematical node statement,
all parent node dependencies, and the unit route stay in place: the same result
is now supplied by its existing upstream proof. No target statement or definition
changes. The node proof steps now describe the canonical equation and transport
that both implementations actually use.

## Users

The downstream.py --uses query lists the following downstream modules and the
item's declaration. Exact import and name searches include quarantine/ and the
DAG; no other importer or affected declaration was found. The chart-equations
parent retains its dependency on lem-pc-fp-overlap-triple-eventually, now attached
upstream. Neither consumer has a current claim in the shared snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleEventually | G6 | Retire duplicate. |
| Sheaf.AlgebraicGeometry.FinitePresentationOverlapChartEquations | unclaimed | Swap one private proof import; all declarations and proofs unchanged. |
| Sheaf.AlgebraicGeometry.FinitePresentationOverlapCoherence | unclaimed | Indirect user; no edit needed. |

## Status

landed 20261020T161139-L-3455060 2026-10-20 (merge of deliver/G6/Sheaf.AlgebraicGeometry.FinitePresentationOverlapTripleEventually)
