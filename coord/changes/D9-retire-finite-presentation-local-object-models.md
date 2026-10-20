# AlgebraicGeometry.exists_finitePresentation_local_object_models

## Reason

The Sheaf module has zero `sorry` and no direct or transitive importers.
The adopted source library already supplies the same declaration and conclusion,
with the unnecessary Noetherian instance hypothesis omitted. Its proof follows the
same finite affine cover, common upper bound and chart transport argument.
`WeilConjectures.AlgebraicGeometry.FinitePresentationLocalDescentDatum` already
imports and uses that source declaration. Withdraw the unused duplicate as required
by the worker brief, step 8d, and attach its DAG node to the existing source theorem.
No declaration or import in the adopted source library is changed.

## Old

In `Sheaf.AlgebraicGeometry.FinitePresentationLocalObjectModels`:

```lean
theorem exists_finitePresentation_local_object_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (M : (pullback f (c.π.app (op i))).Modules)
    (hM : M.IsFinitePresentation) (hMq : M.IsQuasicoherent) :
    ∃ (j : I) (hij : i ≤ j)
      (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u}),
      let p := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
      Finite U.I₀ ∧ (∀ a, IsAffine (U.X a)) ∧
      ∃ N : (a : U.I₀) → (U.X a).Modules,
        (∀ a, (N a).IsFinitePresentation) ∧ (∀ a, (N a).IsQuasicoherent) ∧
        (∀ a, Nonempty ((Scheme.Modules.pullback (U.pullbackHom p a)).obj (N a) ≅
          (Scheme.Modules.pullback ((U.pullback₁ p).f a)).obj M))
```

## New

The Sheaf module is withdrawn (the landing tool leaves an empty module).
The unchanged theorem in
`WeilConjectures.AlgebraicGeometry.FinitePresentationLocalObjectModels` is:

```lean
theorem exists_finitePresentation_local_object_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (M : (pullback f (c.π.app (op i))).Modules)
    (hM : M.IsFinitePresentation) (hMq : M.IsQuasicoherent) :
    ∃ (j : I) (hij : i ≤ j)
      (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u}),
      let p := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
      Finite U.I₀ ∧ (∀ a, IsAffine (U.X a)) ∧
      ∃ N : (a : U.I₀) → (U.X a).Modules,
        (∀ a, (N a).IsFinitePresentation) ∧ (∀ a, (N a).IsQuasicoherent) ∧
        (∀ a, Nonempty ((Scheme.Modules.pullback (U.pullbackHom p a)).obj (N a) ≅
          (Scheme.Modules.pullback ((U.pullback₁ p).f a)).obj M))
```

The latter directly proves the old statement by
`exact exists_finitePresentation_local_object_models R c hc i f M hM hMq`
after importing the source module. No hypothesis or conclusion of a project target
is changed, and no definition is changed. The node's mathematical statement and
its proof dependencies remain unchanged.

## Users

`tools/downstream.py` reports zero modules downstream of the withdrawn Sheaf module.
A search of all Lean sources finds no import of it. Thus there are no consumer
adaptations. The source module and its consumer already use the retained version.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FinitePresentationLocalObjectModels | D9 | Withdraw unused duplicate. |
| WeilConjectures.AlgebraicGeometry.FinitePresentationLocalObjectModels | not adapted | Retained unchanged; DAG attachment points here. |
| WeilConjectures.AlgebraicGeometry.FinitePresentationLocalDescentDatum | not adapted | Already imports and uses source theorem; unchanged. |

## Status

landed 20261020T131949-L-1395573 2026-10-20 (merge of deliver/D9/Sheaf.AlgebraicGeometry.FinitePresentationLocalObjectModels)
