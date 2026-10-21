# AlgebraicGeometry.koszulRegularImmersion_self_ext_stalk_bases

## Reason

The assigned coord/retire-items.tsv row identifies a duplicate implementation of the
source-library stalk-bases theorem. Retire that implementation, including its private
coordinate constructions, and re-export the official theorem. The sole difference in
the public conclusion is the use of exteriorPower in place of exteriorSheaf. Their
proved equality permits both consumers to keep their original public statements.
No source-library file, target, or mathematical hypothesis changes.

## Old

The Sheaf module declared the following theorem, together with private coordinate
cocones, maps, basis germs, restriction frames, and stalk equivalences:

```lean
theorem koszulRegularImmersion_self_ext_stalk_bases
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ)
    (z : V.toScheme) (U : Y.affineOpens) (hzU : i z.1 ∈ U.1)
    (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let T := (Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G)
    let E := Scheme.Modules.exteriorSheaf
      ((Scheme.Modules.restrictFunctor V.ι).obj
        (SheafOfModules.homObj (R := Z.sheaf)
          ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
          (SheafOfModules.unit Z.ringCatSheaf))) n
    Nonempty (Module.Basis (Set.powersetCard (Fin m) n)
      (V.toScheme.presheaf.stalk z) (T.presheaf.stalk z)) ∧
    Nonempty (Module.Basis (Set.powersetCard (Fin m) n)
      (V.toScheme.presheaf.stalk z) (E.presheaf.stalk z))
```

## New

The Sheaf module declares nothing and has these public imports:

```lean
public import WeilConjectures.AlgebraicGeometry.KoszulSelfExtStalkBases
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
```

The unchanged source-library theorem is:

```lean
theorem koszulRegularImmersion_self_ext_stalk_bases
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ)
    (z : V.toScheme) (U : Y.affineOpens) (hzU : i z.1 ∈ U.1)
    (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let T := (Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G)
    let E := Scheme.Modules.exteriorPower
      ((Scheme.Modules.restrictFunctor V.ι).obj
        (SheafOfModules.homObj (R := Z.sheaf)
          ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
          (SheafOfModules.unit Z.ringCatSheaf))) n
    Nonempty (Module.Basis (Set.powersetCard (Fin m) n)
      (V.toScheme.presheaf.stalk z) (T.presheaf.stalk z)) ∧
    Nonempty (Module.Basis (Set.powersetCard (Fin m) n)
      (V.toScheme.presheaf.stalk z) (E.presheaf.stalk z))
```

Each consumer imports the official module and ExteriorSheafComparison privately,
specializes this theorem, eliminates its let bindings with dsimp only, rewrites
exteriorPower to exteriorSheaf, and destructs the resulting pair of bases. The
remainder of each proof, every public import, and each consumer signature is unchanged.
The node attachment follows the official theorem; the consumer nodes record the
additional equality dependency. This is representation transport, not a weakening.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.KoszulSelfExtStalkBases | Q8 | Duplicate implementation removed; official module re-exported. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtExterior | unclaimed | Import official theorem and rewrite its exterior basis type; signature unchanged. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtDualExteriorConormal | unclaimed | Import official theorem and rewrite its exterior basis type; signature unchanged. |
| Sheaf.AlgebraicGeometry.KoszulExtConstantRankTop | unclaimed | Transitive importer; public statements unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtYonedaSurjection | unclaimed | Transitive importer; public statements unchanged; no adaptation. |

The downstream.py query and the full Lean-tree name/import search found precisely
two direct consumers, both included. The other two modules above are transitive
importers reported by downstream.py. No consumer is held by another group at the
checked shared snapshot. The source-library counterpart is untouched. The consumers are adapted only at the stalk-basis call and preserve their current proof imports and bodies elsewhere.
The equality holds for all modules and degrees, so degree zero, degree above the
sequence length, the empty sequence and empty opens require no additional conditions.

## Status

landed 20261021T004840-L-1794601 2026-10-21 (merge of deliver/Q8/Sheaf.AlgebraicGeometry.KoszulSelfExtStalkBases)
