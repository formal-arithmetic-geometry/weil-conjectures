# Scoped proof commands for GrothendieckEtaleLocalEpimorphism

## Reason

The static delivery checker records scoped `omit` and `set_option` commands as a possible
interface change. The first removes unused scheme instances only from a private helper;
the second suppresses an unused-section-instance warning while preserving the original
public theorem's qcqs assumptions on X. Both commands are scoped by `in` to the next
declaration. Neither changes downstream elaboration, any existing signature, or any definition.
This record makes the conservative checker finding explicit for the independent reader.

## Old

Original public signature, verbatim:

```lean
theorem eq_zero_of_locally_liftable_maps
    {F G : Sheaf X.smallEtaleTopology A} (p : F ⟶ G) [Epi p]
    (W : X.Etale) [CompactSpace W.left] [QuasiSeparatedSpace W.left]
    (B T : A) (x : B ⟶ G.obj.obj (op W)) (g : B ⟶ T)
    (hkill : ∀ (B' : A) (π : B' ⟶ B) (R : Sieve W), R ∈ X.smallEtaleTopology W →
      (∀ (Z : X.Etale) (f : Z ⟶ W), R f →
        ∃ l : B' ⟶ F.obj.obj (op Z), l ≫ p.hom.app (op Z) = π ≫ x ≫ G.obj.map f.op) →
      π ≫ g = 0) : g = 0
```

The original module had no private helper and no scoped linter command.

## New

The public signature is identical, including the same surrounding variables, universes,
and original public import:

```lean
theorem eq_zero_of_locally_liftable_maps
    {F G : Sheaf X.smallEtaleTopology A} (p : F ⟶ G) [Epi p]
    (W : X.Etale) [CompactSpace W.left] [QuasiSeparatedSpace W.left]
    (B T : A) (x : B ⟶ G.obj.obj (op W)) (g : B ⟶ T)
    (hkill : ∀ (B' : A) (π : B' ⟶ B) (R : Sieve W), R ∈ X.smallEtaleTopology W →
      (∀ (Z : X.Etale) (f : Z ⟶ W), R f →
        ∃ l : B' ⟶ F.obj.obj (op Z), l ≫ p.hom.app (op Z) = π ≫ x ≫ G.obj.map f.op) →
      π ≫ g = 0) : g = 0
```

Added `omit [CompactSpace X] [QuasiSeparatedSpace X] in` before the new private helper
`localImage_eq_top_of_isSheaf`. Added `set_option linter.unusedSectionVars false in` before
the existing theorem. The helper and the theorem are completely proved. The new helper
modules are brought into this module by private imports only.

## Users

`tools/downstream.py ... --uses eq_zero_of_locally_liftable_maps` reports the item and one
consumer mentioning the theorem; all 171 transitive importers keep the same interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GrothendieckEtaleLocalEpimorphism | C1 | Own item; public signature identical, private proof helper added. |
| Sheaf.AlgebraicGeometry.GrothendieckHypercoverLocalPrimitives | unclaimed | Original module compiled against the sandbox artifacts; no adaptation needed. |

No target statement or definition used by a target changes. No forced adaptation occurs.

## Status

landed 20261016T073458-L-1079934 2026-10-16 (merge of deliver/C1/Sheaf.AlgebraicGeometry.GrothendieckEtaleLocalEpimorphism)
