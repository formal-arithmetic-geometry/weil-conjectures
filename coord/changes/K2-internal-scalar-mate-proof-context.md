# internal_scalar_mate_projection proof context

## Reason

Restore the formal mate calculation after the previous packet was reverted.
Local proof options and reducibility attributes keep the scalar and section functor
interfaces usable without changing any exported declaration or mathematical data.
The restored normalization modules use their existing DAG signatures verbatim.

## Old

```lean
theorem internal_scalar_mate_projection (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (tX : TensorNormalization a X) (tY : TensorNormalization a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (hX : TensorNormalized a X tX) (hY : TensorNormalized a Y tY)
    (hlam : PullNormalized a f lam) :
    IsIso (scalarRestrictionPush a f) ∧
    ScalarMatePullEquation a f tX tY lam ∧
    (∀ K : DerivedCategory (Modules Λ X),
      (V a Y).map ((rho a f lam).app K) ≫
          (scalarRestrictionPush a f).app ((D a X).obj K) ≫
          (F Λ f).map (tX.derived.hom.app K) =
        tY.derived.hom.app ((F Λ f).obj K) ≫ scalarProjection a f K) ∧
    ScalarMateSectionEquation a f tX tY lam ∧
    (∀ K : DerivedCategory (Modules Λ X),
      IsIso ((rho a f lam).app K) ↔ IsIso (scalarProjection a f K)) ∧
    (∀ (K K' : DerivedCategory (Modules Λ X)) (q : K ⟶ K'),
      ((CondensedRing.derivedTensor Λ Y).map ((F Λ f).map q)).app (B a Y) ≫
        scalarProjection a f K' =
        scalarProjection a f K ≫
          (F Λ f).map (((CondensedRing.derivedTensor Λ X).map q).app (B a X)))
```

The theorem has one sorry. Existing public imports and definitions are retained.

## New

```lean
theorem internal_scalar_mate_projection (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (tX : TensorNormalization a X) (tY : TensorNormalization a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (hX : TensorNormalized a X tX) (hY : TensorNormalized a Y tY)
    (hlam : PullNormalized a f lam) :
    IsIso (scalarRestrictionPush a f) ∧
    ScalarMatePullEquation a f tX tY lam ∧
    (∀ K : DerivedCategory (Modules Λ X),
      (V a Y).map ((rho a f lam).app K) ≫
          (scalarRestrictionPush a f).app ((D a X).obj K) ≫
          (F Λ f).map (tX.derived.hom.app K) =
        tY.derived.hom.app ((F Λ f).obj K) ≫ scalarProjection a f K) ∧
    ScalarMateSectionEquation a f tX tY lam ∧
    (∀ K : DerivedCategory (Modules Λ X),
      IsIso ((rho a f lam).app K) ↔ IsIso (scalarProjection a f K)) ∧
    (∀ (K K' : DerivedCategory (Modules Λ X)) (q : K ⟶ K'),
      ((CondensedRing.derivedTensor Λ Y).map ((F Λ f).map q)).app (B a Y) ≫
        scalarProjection a f K' =
        scalarProjection a f K ≫
          (F Λ f).map (((CondensedRing.derivedTensor Λ X).map q).app (B a X)))
```

The theorem has a proof from the separate pull/tensor and restriction-mate
normalizations already recorded in the DAG. Local proof attributes expose interface
wrappers and proof options control matching of their definitionally equal endpoints.
The section comparison explicitly uses scalarSectionPushMate_eq instead of assuming
that the mate-based scalarSectionPushComparison and derivedPushComparison are
definitionally the same. No existing signature, definition body, or visibility changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.InternalScalarMateProjection | K2 | Private proof helpers and local commands. |
| Sheaf.Paper.NormalizedScalarRestrictionPush | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FlatCoefficientSquareNormalization | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.FlatScalarGeometricCoherence | unclaimed | Unchanged public interface; no adaptation. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | unclaimed | Unchanged public interface; no adaptation. |

All transitive users see the same existing declarations, definitions and public
imports. The proof commands and private proof imports do not escape this module;
no transitive consumer requires adaptation. The downstream query was read before
changing the local proof context.

## Status

landed 20261025T202352-L-2711568 2026-10-25 (merge of deliver/K2/Sheaf.Paper.InternalScalarMateProjection)
