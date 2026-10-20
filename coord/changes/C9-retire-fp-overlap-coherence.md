# AlgebraicGeometry.exists_finitePresentation_overlap_eventual_coherence

## Reason

The assigned module is explicitly listed for duplicate retirement in
coord/retire-items.tsv. Both versions already have complete proofs and zero
local holes. The upstream version differs only by omitting the unused
Noetherian ring instance. Its proof body is identical and specializes directly
to the complete old statement. Retire the duplicate and attach its node to the
existing upstream theorem. No source-library file is modified.

## Old

Declared in Sheaf.AlgebraicGeometry.FinitePresentationOverlapCoherence:

```lean
theorem exists_finitePresentation_overlap_eventual_coherence
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
    (M : (pullback f (c.π.app (op i))).Modules) :
    ∀ (k : I) (hjk : j ≤ k),
      let q₀ := overlapStageMap R f hij hjk
      let V₀ : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} :=
        U.pullback₁ q₀
      let p₀ := overlapLimitMap R c f (hij.trans hjk)
      ∀ T : modulesPseudofunctor.OverlapTransitions V₀.f,
        (∀ a, Nonempty ((T.obj a : (V₀.X a).Modules) ≅
          (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj (N a))) →
        Nonempty ((T.pull (p := p₀) (α := fun a ↦ a)
          (fun a ↦ V₀.pullbackHom_map p₀ a)).Comparison
          ((modulesPseudofunctor.toDescentData (V₀.pullback₁ p₀).f).obj M)) →
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
          let p := overlapLimitMap R c f (hij.trans (hjk.trans hkl))
          T'.Coherent ∧
            Nonempty ((T'.pull (p := p) (α := fun a ↦ a)
              (fun a ↦ V.pullbackHom_map p a)).Comparison
              ((modulesPseudofunctor.toDescentData (V.pullback₁ p).f).obj M))
```

## New

Use the existing declaration in
WeilConjectures.AlgebraicGeometry.FinitePresentationOverlapCoherence:

```lean
theorem exists_finitePresentation_overlap_eventual_coherence
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
    (M : (pullback f (c.π.app (op i))).Modules) :
    ∀ (k : I) (hjk : j ≤ k),
      let q₀ := overlapStageMap R f hij hjk
      let V₀ : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} :=
        U.pullback₁ q₀
      let p₀ := overlapLimitMap R c f (hij.trans hjk)
      ∀ T : modulesPseudofunctor.OverlapTransitions V₀.f,
        (∀ a, Nonempty ((T.obj a : (V₀.X a).Modules) ≅
          (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj (N a))) →
        Nonempty ((T.pull (p := p₀) (α := fun a ↦ a)
          (fun a ↦ V₀.pullbackHom_map p₀ a)).Comparison
          ((modulesPseudofunctor.toDescentData (V₀.pullback₁ p₀).f).obj M)) →
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
          let p := overlapLimitMap R c f (hij.trans (hjk.trans hkl))
          T'.Coherent ∧
            Nonempty ((T'.pull (p := p) (α := fun a ↦ a)
              (fun a ↦ V.pullbackHom_map p a)).Comparison
              ((modulesPseudofunctor.toDescentData (V.pullback₁ p).f).obj M))
```

Withdraw the Sheaf module through deleted.txt. Reattach
lem-pc-fp-overlap-eventual-coherence to the existing upstream declaration,
recording the full upstream signature. Keep the node's mathematical statement,
proof steps, proof dependencies, and parent dependency edges unchanged.
No target statement or definition changes; target statement review does not
reopen.

## Users

tools/downstream.py reports zero downstream modules and no declaration users
outside the retiring file. Exact import and declaration searches covered both library roots and the
quarantine tree. There are no current imports of the Sheaf module. The former
Sheaf.FinitePresentationLocalOverlapModels consumer has already been retired;
its upstream counterpart already privately imports the upstream coherence module
and applies the same declaration. It requires no edit. The DAG parent
lem-pc-fp-local-overlap-models keeps its eventual-coherence dependency and will
resolve it through the updated Lean attachment. Other DAG mentions are
provenance edges. The unit sk-thm-picard-semicon has empty realized statement
and step lists; no unit statement or route is bypassed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FinitePresentationOverlapCoherence | C9 | Retire duplicate. |
| WeilConjectures.AlgebraicGeometry.FinitePresentationLocalOverlapModels | unclaimed | Already imports and uses upstream theorem; no edit. |

The exact old signature was compiled in a sandbox scratch theorem by direct
application of the upstream theorem. Both that specialization and the upstream
theorem have exactly propext, Classical.choice, and Quot.sound as printed axioms.
The unchanged upstream local-overlap-models consumer was also compiled
independently, with the same three permitted axioms. The upstream declaration
and its proof dependencies remain present.

## Status

landed 20261020T211650-L-3486194 2026-10-20 (merge of deliver/C9/Sheaf.AlgebraicGeometry.FinitePresentationOverlapCoherence)
