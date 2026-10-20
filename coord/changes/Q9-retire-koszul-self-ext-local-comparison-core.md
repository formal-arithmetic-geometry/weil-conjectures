# AlgebraicGeometry.koszulRegularImmersion_self_ext_conormal_local_iso

## Reason

Retire the duplicate Sheaf module listed in coord/retire-items.tsv in favor of its
already proved upstream counterpart. The assigned module currently has zero sorry
bodies. Its upstream counterpart differs in using exteriorPower instead of the
legacy exteriorSheaf. The proved exteriorSheaf_eq_exteriorPower identifies these
objects for every module and degree, with no extra hypotheses. Rewrite the local
existence result in the only direct consumer; its public signature stays identical.

The old PROOFDIFF_UNSAFE retirement note records dependency twins from an earlier
source state. In the current graph, the upstream core adds only itself to the
consumer's import closure: every one of its dependencies is already present.
The retirement therefore introduces no additional pair of dependency twins.
The pre-existing GlueSheavesOfModules pair is unchanged by this delivery.

## Old

In Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalComparisonCore:

```lean
theorem koszulRegularImmersion_self_ext_conormal_local_iso
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ)
    (hregular : ∀ z : Z, z ∈ V → ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let T := (Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G)
    let F := (Scheme.Modules.restrictFunctor V.ι).obj
      (Scheme.Modules.dual (Scheme.Modules.exteriorSheaf
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n))
    ∀ z : V.toScheme, ∃ W : V.toScheme.Opens,
      z ∈ W ∧ Nonempty (F.over W ≅ T.over W)
```

## New

Withdraw that Sheaf module using deleted.txt, and point the existing node at
WeilConjectures.AlgebraicGeometry.KoszulSelfExtConormalLocalComparisonCore:

```lean
theorem koszulRegularImmersion_self_ext_conormal_local_iso
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ)
    (hregular : ∀ z : Z, z ∈ V → ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let T := (Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G)
    let F := (Scheme.Modules.restrictFunctor V.ι).obj
      (Scheme.Modules.dual (Scheme.Modules.exteriorPower
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n))
    ∀ z : V.toScheme, ∃ W : V.toScheme.Opens,
      z ∈ W ∧ Nonempty (F.over W ≅ T.over W)
```

In the consumer, replace the private core import by the upstream core import and
add the private ExteriorSheafComparison import. Immediately after obtaining the
upstream local-isomorphism result, transport its source with:

```lean
  rw [← Scheme.Modules.exteriorSheaf_eq_exteriorPower] at hlocal
```

No other proof line changes. The rewrite is valid also in degree zero, above the
local rank, for a length-zero regular sequence, and on empty opens, because the
exterior comparison is unconditional. The mathematical node statement is unchanged;
its Lean attachment records the upstream signature verbatim. The consumer node
records the equality used for transport.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalComparisonCore | Q9 | Duplicate retired; node points to the existing upstream theorem. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalComparison | unclaimed | Only direct importer and external use; replace the private import and transport the result. Public imports, signature, and remaining proof are unchanged. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtConormalComparisonSurjection | unclaimed | Indirect consumer; theorem signature and public environment are unchanged. No adaptation. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtDualExteriorConormal | unclaimed | Indirect consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtYonedaSurjection | unclaimed | Indirect consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtExterior | unclaimed | Indirect consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulExtConstantRankTop | unclaimed | Indirect consumer; no adaptation. |

These are all modules listed by tools/downstream.py with the declaration-use
filter. The only DAG parent is the compatible local-comparison node, and it
continues to cite the same local-isomorphism node. No quarantined parent cites
the withdrawn module or its node. The unit's realized lists are unchanged.
No file under lean/WeilConjectures, no definition, and no target statement changes.

## Status

landed 20261020T221317-L-4172109 2026-10-20 (merge of deliver/Q9/Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalComparisonCore)
