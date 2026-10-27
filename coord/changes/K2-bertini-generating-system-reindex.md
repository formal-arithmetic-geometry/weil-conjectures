# AlgebraicGeometry.ProjectiveSpace.generatingSections_immersion_iso_reindex

## Reason

The affine Bertini system needs its existing immersive finite family transported along
an isomorphism of invertible modules and an equivalence of finite index types. Isolate
this general coordinate-invariance step, without repeating any Bertini existence,
vanishing, smoothness, coefficient-open or dimension conclusion.

## Old

There was no declaration or module for this coordinate-invariance statement.
The signature of `AlgebraicGeometry.exists_smooth_affine_prescribedPoint_linearSystem`
and every existing definition are unchanged.

## New

New module `Sheaf.AlgebraicGeometry.GeneratingSectionsImmersionReindex` declares:

```lean
theorem generatingSections_immersion_iso_reindex
    {X B : Scheme.{u}} (f : X ⟶ B)
    {I J : Type u} [Finite I] [Finite J] (e : J ≃ I)
    (M N : X.Modules) [M.IsInvertible] [N.IsInvertible] (α : M ≅ N)
    (s : I → Γ(M, ⊤)) (t : J → Γ(N, ⊤))
    (ht : ∀ j, α.hom.app ⊤ (s (e j)) = t j)
    (hs : ∃ h : Epi (M.freeHomEquiv.symm
        (fun i ↦ SheafOfModules.unitHomEquiv _ (homOfGlobalSection M (s i)))),
      IsImmersion (@homOfGeneratingSections I inferInstance X B f M inferInstance
        (fun i ↦ SheafOfModules.unitHomEquiv _ (homOfGlobalSection M (s i))) h)) :
    ∃ h : Epi (N.freeHomEquiv.symm
        (fun j ↦ SheafOfModules.unitHomEquiv _ (homOfGlobalSection N (t j)))),
      IsImmersion (@homOfGeneratingSections J inferInstance X B f N inferInstance
        (fun j ↦ SheafOfModules.unitHomEquiv _ (homOfGlobalSection N (t j))) h)
```

This theorem has one named whole-proof sorry and its own sourced DAG node. The
assigned module now proves its existing statement from the existing eventual
smooth-system theorem and this coordinate-invariance theorem. All imports added to
an existing module are private proof imports. Local irreducibility annotations keep
large scheme and module constructions folded during elaboration; no definition or
global attribute changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GeneratingSectionsImmersionReindex | K2, new | New coordinate-invariance theorem. |
| Sheaf.AlgebraicGeometry.BertiniSmoothAffineLinearSystem | K2 | Private proof import and application; existing signature unchanged. |
| Sheaf.AlgebraicGeometry.BertiniFiniteCoverDimensionCut | unmodified consumer | Existing affine-system signature unchanged; no adaptation required. |

## Status

landed 20261025T205515-L-3269181 2026-10-25 (merge of deliver/K2/Sheaf.AlgebraicGeometry.BertiniSmoothAffineLinearSystem)
