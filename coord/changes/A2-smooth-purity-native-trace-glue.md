# AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityMap

## Reason

Partial formalization of the declared smooth trace route. The finite normalized tower
exists for the native Over(Spec k) map. The actual open comparison preserves the
specified counits and monoidal unit. Given the actual reconstructed comparison and
its trace formula, full faithfulness constructs the purity comparison and identifies
its ambient inverse; a common-source square then gives composition compatibility.
All eight added helpers are private and completely proved. No public statement,
attribute, definition body, public import or instance changes. Four original holes
remain; this is partial proof work, not a completed trace-definition repair.

## Old

The three original public imports of six-functor and Tate machinery, the public
smoothTrace/smoothPurityMap/smoothPurityIso signatures and all four original holes
remain unchanged. The already proved private invertibility helper was:

```lean
private theorem isIso_smoothPurityMap_of_trace_formula
    (e : boundedConstructibleTateTwist ℓ X d (2 * d) ≅
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
    (htrace : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map e.hom ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ f).counit.app (𝟙_ _)) :
    IsIso (smoothPurityMap ℓ f d) := by
  have h : smoothPurityMap ℓ f d = e.hom := by
    change (boundedConstructibleUpperShriekAdjunction _ ℓ f).homEquiv _ _
      (smoothTrace ℓ f d) = e.hom
    rw [htrace, ← (boundedConstructibleUpperShriekAdjunction
      (Profinite.padicAlgClRingObj ℓ) ℓ f).homEquiv_counit _ _ e.hom]
    exact ((boundedConstructibleUpperShriekAdjunction _ ℓ f).homEquiv _ _).apply_symm_apply _
  rw [h]
  infer_instance
```

## New

The same private helper consumes the more general proved adjunct identity:

```lean
private theorem isIso_smoothPurityMap_of_trace_formula
    (e : boundedConstructibleTateTwist ℓ X d (2 * d) ≅
      (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)))
    (htrace : smoothTrace ℓ f d =
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map e.hom ≫
        (boundedConstructibleUpperShriekAdjunction
          (Profinite.padicAlgClRingObj ℓ) ℓ f).counit.app (𝟙_ _)) :
    IsIso (smoothPurityMap ℓ f d) := by
  rw [smoothPurityMap_eq_of_trace_formula ℓ f d e.hom htrace]
  infer_instance
```

Add the private proof import Sheaf.Paper.CondensedTateIntegralTower. Add the proved
private helpers smoothTrace_openComparison_counit, smoothTrace_openUnit_counit,
smoothTrace_reconstructionInputs, smoothPurityMap_eq_of_trace_formula,
smoothPurityMap_of_reconstructed_trace, smoothPurityIso_eq_of_reconstructed_trace,
smoothPurityIso_comp_of_reconstructed_traces, and
smoothPurityIso_zero_of_trace_formula. Their docstrings name their
corresponding route steps. The first three are actual native prerequisite results;
the last five retain the geometric trace/comparison equalities as explicit inputs.
The matching three route nodes record precisely which parts are now formalized.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SmoothPurity.Defs | A2 | Private proof work only. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Same public interface; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same public interface; no adaptation. |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Same public interface; no adaptation. |
| TargetsCheck | unclaimed | Same public interface; no adaptation. |
| WeilConjectures | unclaimed | Same public interface; no adaptation. |

The table contains all direct importers in the shared source. No existing module
besides the item is edited. The new import is private, the added declarations are
private, and the instances used for native input construction are local lets.
No target meaning changes and no forced adaptation is required.

## Status

landed 20261027T021255-L-2751797 2026-10-27 (merge of deliver/A2/WeilConjectures.SmoothPurity.Defs)
