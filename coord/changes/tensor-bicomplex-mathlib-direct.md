# HomologicalComplex₂.tensorBicomplex / tensorBicomplexMap

## Reason

Repair the landing rejection at ae6f73591. The return explicitly allows keeping
the old names. Restore them as transparent abbreviations of Mathlib, preserving
the public interface and withdrawing unnecessary downstream adaptations.
This supersedes the earlier proposed removal, not the mathematical construction.

## Old

The returned version removed both declarations and introduced local notation in
four callers. The sheaf-dag compatibility signatures and bodies are:

```lean
/-- The commuting tensor bicomplex, with terms `Pᵢ ⊗ Qⱼ` and no totalization signs.
-- The construction is the canonical Mathlib bifunctor.
-- Its terms and commuting differentials are inherited definitionally.
Source: Stacks Project, Algebra, Tag 00M3, proof, first paragraph.
(blueprint: def-weil-pbc-tensor-bicomplex) -/
abbrev tensorBicomplex (P Q : ChainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} R) (.down ℕ) (.down ℕ) :=
  ((Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R)) (.down ℕ)
      (.down ℕ)).obj P).obj Q

/-- A pair of chain maps acts termwise on the tensor bicomplex.
Source: Stacks Project, Algebra, Tag 00M3, functoriality paragraph.
(blueprint: def-weil-pbc-tensor-bicomplex) -/
abbrev tensorBicomplexMap {P P' Q Q' : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : P ⟶ P') (b : Q ⟶ Q') :=
  (Functor.uncurry.obj
    (Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ))).map (X := (P, Q)) (Y := (P', Q')) (a, b)

```

## New

The same two compatibility abbreviations, with identical signatures and bodies,
are restored. Their documentation explicitly describes their compatibility role.
chainTensorMap keeps its original signature and body. All public imports stay.
There is no separate tensor-bicomplex construction and no target meaning changes.
No caller adaptation is included: every original caller continues to compile.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.TensorBicomplex | D2 | Restore compatibility names. |
| Sheaf.Algebra.Homology.TensorResolutionColumnCokernelIso | unclaimed | Original retained; no adaptation. |
| Sheaf.Algebra.Homology.TensorResolutionRowCokernelIso | unclaimed | Original retained; no adaptation. |
| Sheaf.Algebra.Category.ModuleCat.TorSymmetry | unclaimed | Original retained; no adaptation. |
| Sheaf.Algebra.Homology.FlatResolutionTorComparison | unclaimed | Original retained; no adaptation. |

Holder labels reflect the previous delivery snapshot; no edits to callers are
proposed or require their claims. The independent reader must replace the prior
second reading after checking this repaired delivery.

## Status

landed 20261014T030641-L-342008 2026-10-14 (merge of deliver/D2/Sheaf.Algebra.Homology.TensorBicomplex)
