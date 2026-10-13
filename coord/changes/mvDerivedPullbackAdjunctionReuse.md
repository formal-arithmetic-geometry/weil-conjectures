# mvDerivedPullbackAdjunction

## Reason

Reviewer X-00326, H4 requires removing the duplicate derived pullback adjunction
constructor. Stage 3 §3 requires an abbreviation when two definitions describe the
same notion. Reuse `canonicalPullbackAdjunction` from
`Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap` with a public import, because
this constructor appears in exposed definition bodies. Both bodies select the same
normalized adjunction with the same composition-family counit. Unfolding both old
constructors gives definitional equality; no hypothesis or conclusion changes.
The component node gains `def-pc-affine-global-hom-base-change-map` in `stmt_deps`.
No target signature or target definition changes, and no consumer adaptation is needed.

## Old

```lean
@[irreducible] def mvDerivedPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPullback f ⊣ schemeDerivedDirectImage f :=
  by
    let h := exists_derivedPullbackComposition.{u, w}
    let hAdd := @Classical.choose _ _ h
    let ε := @Classical.choose _ _ (Classical.choose_spec h)
    let hε := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec h))
    exact Classical.choose (exists_schemeDerivedAdjunction.{u, w} f
      (hAdd := hAdd f) (ε f) (hε f))
```

## New

Added `public import Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap`.

```lean
abbrev mvDerivedPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPullback f ⊣ schemeDerivedDirectImage f :=
  canonicalPullbackAdjunction f
```

## Users

The component module is new in this delivery. Its users are the other three modules
of this delivery; no existing repository module refers to the new abbreviation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps | C4 | Reuses the existing constructor; signature and canonical data preserved. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisSquares | C4 | Same canonical open adjunctions; recompiles unchanged. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary | C4 | Same canonical open adjunctions; recompiles unchanged. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris | C4 | Same comparison and assembly; recompiles unchanged. |

## Status

landed 20261013T142853-L-496277 2026-10-13 (merge of deliver/C4/Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris)
