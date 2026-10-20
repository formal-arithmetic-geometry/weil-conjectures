# AlgebraicGeometry.VectorBundleZeroSection.antiEquivalence

## Reason

The original definition exposes a `Classical.choose` from a large dependent
existential every time its structure-algebra functor is reduced. Profiling isolated
repeated dependent conversions in the zero-section section calculation, and the
complete proof exceeded the 60-second check. The replacement constructs that
functor on objects and section maps and proves it is an equivalence by the object
and morphism characterizations of `affine_morphism_relative_spec`. Its chosen
quasi-inverse is a genuine inverse, uniquely determined up to algebra-compatible
isomorphism. No existence-only arbitrary geometric object is introduced.

The module still constructs `Spec_S Sym(F)`, with the same augmentation and
fully faithful inverse image defining the zero section. All existing public
signatures remain identical. The concrete choice of quasi-inverse can change;
this is a representation repair, not a claim of literal equality of chosen
schemes. The algebra-compatible isomorphism preserves the projection,
augmentation, charts, frame coordinates, and their transition formulas. The
meaning review of targets using these definitions must therefore be reopened;
their Lean statements and mathematical strength are unchanged.

## Old

```lean
def antiEquivalence (S : Scheme.{u}) :
    (ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))ᵒᵖ ≌
      ObjectProperty.FullSubcategory
        (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent) :=
  (affine_morphism_relative_spec S).2.choose
```

## New

```lean
def antiEquivalence (S : Scheme.{u}) :
    (ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))ᵒᵖ ≌
      ObjectProperty.FullSubcategory
        (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent) := by
  letI := structureAlgebraFunctor_isEquivalence S
  exact (structureAlgebraFunctor S).asEquivalence
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ConormalConeZeroSectionPullback` | unclaimed | Its private object/map proofs must use the concrete functor. |
| `Sheaf.AlgebraicGeometry.ReesConeNormalization` | unclaimed | Its counit algebra isomorphism must omit the old chosen-functor cast. |
| `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` | N3 | Same relative-spectrum universal property; signature unchanged. |
| `Sheaf.AlgebraicGeometry.VectorIntegrationMate` | unclaimed | Same relative-spectrum universal property; signature unchanged. |
| `Sheaf.Paper.FiniteRingSectionDeformation` | unclaimed | Same relative-spectrum universal property; signature unchanged. |
| `Sheaf.Paper.PurityNormalBundle` | unclaimed | Same relative-spectrum universal property; signature unchanged. |
| `Sheaf.Paper.VectorPurityDirectSum` | unclaimed | Same relative-spectrum universal property; signature unchanged. |
| `Sheaf.Targets.VectorBundlePurity` | unclaimed | Same relative-spectrum universal property; signature unchanged. |

## Status

landed 20261020T211804-L-3502452 2026-10-20 (merge of deliver/N3/Sheaf.AlgebraicGeometry.VectorBundleZeroSection)
