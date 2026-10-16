# AlgebraicGeometry.Scheme.ProEt.map_eq_of_boundedBelow_homotopy

## Reason

`Sheaf.Paper.CondensedHypercoverComparison` duplicated the private
`map_eq_of_boundedBelow_homotopy` proof already present in
`Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex`. The helper
is exposed at its original declaration and imported by the condensed comparison.
The duplicate declaration and its `Mathlib.Algebra.Homology.HomotopyCofiber`
import are removed from the condensed module.

## Changed source

`lean/Sheaf/AlgebraicGeometry/ProEtaleHypercoverComputesBoundedComplex.lean`
changes only the declaration visibility from `private theorem` to `theorem`;
its type and proof are unchanged. The module is currently unclaimed (its prior
landing holder was C3). The public declaration remains
`AlgebraicGeometry.Scheme.ProEt.map_eq_of_boundedBelow_homotopy`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex` | unclaimed | Exposes the existing helper; its internal use remains unchanged. |
| `Sheaf.Paper.CondensedHypercoverComparison` | G2 | Imports the source module and calls the exposed helper; removes the duplicate proof. |

The source module has 23 transitive downstream importers, but none requires an
interface adaptation: this is a visibility-only change. The DAG node
`lem-weil-pbc-condensed-hypercover-comparison` now lists
`lem-weil-pbc-bounded-below-homotopy-invariance` in its proof uses and
proof dependencies. This new DAG attachment names the existing helper; it adds
no theorem body. The source comparison node also records its helper dependency.

## Old

```lean
private theorem map_eq_of_boundedBelow_homotopy
    {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D]
    (H : CochainComplex C ℤ ⥤ D)
    (hH : ∀ (K L : CochainComplex.Plus C) (f : K ⟶ L),
      QuasiIso f.hom → IsIso (H.map f.hom))
    (K L : CochainComplex.Plus C) (f g : K.obj ⟶ L.obj) (h : Homotopy f g) :
    H.map f = H.map g
```

`CondensedHypercoverComparison` also contained an identical private theorem
body and imported `Mathlib.Algebra.Homology.HomotopyCofiber` directly.

## New

```lean
theorem map_eq_of_boundedBelow_homotopy
    {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D]
    (H : CochainComplex C ℤ ⥤ D)
    (hH : ∀ (K L : CochainComplex.Plus C) (f : K ⟶ L),
      QuasiIso f.hom → IsIso (H.map f.hom))
    (K L : CochainComplex.Plus C) (f g : K.obj ⟶ L.obj) (h : Homotopy f g) :
    H.map f = H.map g
```

The source declaration's type and proof are preserved; only `private` is
removed. `CondensedHypercoverComparison` imports
`Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex` and calls
`Scheme.ProEt.map_eq_of_boundedBelow_homotopy`, deleting the duplicate theorem
and its direct `HomotopyCofiber` import. The source helper's internal call is
unchanged. No user signature changes.

## Status

landed 20261016T040116-L-2417209 2026-10-16 (merge of deliver/G2/Sheaf.Paper.CondensedQcqsPushforwardLocalComparison)

The source module is currently unclaimed; its historical landing
holder was C3. The condensed comparison is held by G2 in this delivery. Both
affected modules compile, and the reused helper is attached to the condensed
hypercover comparison node's proof dependencies.
