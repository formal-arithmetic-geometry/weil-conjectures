# AlgebraicGeometry.Etale.FiniteSmoothPurity.coneAlgebraIso

## Reason

Forced by the concrete structure-algebra functor repair in
`VectorBundleZeroSection.antiEquivalence` (see `N3-vector-bundle-antiEquivalence.md`).
The original compiler rejects the `eqToIso` argument at line 45: the object equation
of the old chosen functor no longer has the source of the new mapped inverse counit.
The new functor returns the structure algebra definitionally, so the inverse counit
already has the required codomain. Omit exactly this obsolete cast.

This is still the algebra-compatible identification of the same conormal algebra
with functions on its relative spectrum. Its normalization on homogeneous classes
is unchanged. No existing signature, hypothesis, conclusion or public import changes.
The meaning review for targets depending on this representation must be reopened.

## Old

```lean
def coneAlgebraIso {V S : Scheme.{u}} (s : S ⟶ V) [IsClosedImmersion s] :
    (PurityNormalBundle.algebraObject s).obj ≅
      Under.mk (⟨(PurityNormalBundle.projection s).c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u}
          (PurityNormalBundle.projection s).base).obj
            (PurityNormalBundle.normalCone s).sheaf) :=
  ((ObjectProperty.ι (fun B : S.CommAlgebraSheaf ↦ B.toModule.IsQuasicoherent)).mapIso
    ((VectorBundleZeroSection.antiEquivalence S).counitIso.app
      (PurityNormalBundle.algebraObject s))).symm ≪≫
    eqToIso ((affine_morphism_relative_spec S).2.choose_spec.choose
      (PurityNormalBundle.over s))
```

## New

```lean
def coneAlgebraIso {V S : Scheme.{u}} (s : S ⟶ V) [IsClosedImmersion s] :
    (PurityNormalBundle.algebraObject s).obj ≅
      Under.mk (⟨(PurityNormalBundle.projection s).c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u}
          (PurityNormalBundle.projection s).base).obj
            (PurityNormalBundle.normalCone s).sheaf) :=
  ((ObjectProperty.ι (fun B : S.CommAlgebraSheaf ↦ B.toModule.IsQuasicoherent)).mapIso
    ((VectorBundleZeroSection.antiEquivalence S).counitIso.app
      (PurityNormalBundle.algebraObject s))).symm
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ConormalConeZeroSectionPullback` | unclaimed | Same canonical relative-Spec comparison; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ReesConeNormalization` | unclaimed | Same canonical relative-Spec comparison; signature unchanged. |
| `Sheaf.AlgebraicGeometry.ReesConeNormalizedExistence` | unclaimed | Same canonical relative-Spec comparison; signature unchanged. |
| `Sheaf.Paper.FiniteSmoothCanonicalInterfaces` | unclaimed | Same canonical relative-Spec comparison; signature unchanged. |

The private object/map characterization proofs in `ConormalConeZeroSectionPullback`
are adapted to the concrete functor. Its final simplification also cancels the now
reflexive cast. All its existing signatures stay identical.

## Status

landed 20261020T211804-L-3502452 2026-10-20 (merge of deliver/N3/Sheaf.AlgebraicGeometry.VectorBundleZeroSection)
