# AlgebraicGeometry.Scheme.Modules.determinant_liftWedge_kernel_exists

## Reason

Retire the zero-hole duplicate under coord/retire-items.tsv row 1205 and the human's
2026-10-20 retirement hand-off. The official twin proves the same mathematical
statement with exteriorPower and wedge. The canonical exteriorSheafPowerIso
identifies the exterior sheaves and preserves their wedge sections.

The sole direct consumer, DeterminantWedgeMorphismGlue, imports the official twin
instead of the copy. Its private proved compatibility lemma conjugates q by tensor
comparison isomorphisms and applies the official kernel-annihilation theorem.
The source comparison maps the old kernel into the new kernel: kernel.lift,
kernel.lift_ι and the official annihilation equation prove annihilation after
transport. The tensor-section equation and the comparison wedge equations prove
the original concatenated-wedge formula. The existing Abelian.epiDesc argument
then applies unchanged. This construction works in rank zero, in either degree
zero, on empty opens and schemes, and over zero rings, using the same isomorphisms.
It introduces no existence choice, hypothesis, new public declaration or hole.

The duplicate is withdrawn through deleted.txt. Its node attaches to the official
theorem with its verbatim signature and actual proof dependencies. The parent node
retains the kernel-annihilation step and describes the transport explicitly. The
unit statement and its determinant route are preserved.

## Old

Duplicate module Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel:

```lean
theorem determinant_liftWedge_kernel_exists {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (q : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₂ r₃ ⟶
      exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃)
    (hq : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (c : Fin r₃ → S.X₂.val.obj (op U)),
      q.val.app (op U)
          (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
            (exteriorSheafSection S.X₂ r₃ U c)) =
        tmulSection (M := exteriorSheaf S.X₁ r₁) (N := exteriorSheaf S.X₃ r₃)
          (exteriorSheafSection S.X₁ r₁ U a)
          (exteriorSheafSection S.X₃ r₃ U (fun i ↦ S.g.val.app (op U) (c i)))) :
    ∃ w : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₂ r₃ ⟶ exteriorSheaf S.X₂ r₂,
      kernel.ι q ≫ w = 0 ∧ ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (c : Fin r₃ → S.X₂.val.obj (op U)),
        w.val.app (op U)
            (tmulSection (exteriorSheafSection S.X₁ r₁ U a)
              (exteriorSheafSection S.X₂ r₃ U c)) =
          exteriorSheafSection S.X₂ r₂ U
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))
```

## New

Existing, unchanged declaration in
WeilConjectures.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel:

```lean
theorem determinant_liftWedge_kernel_exists {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (q : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₂ r₃ ⟶
      exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃)
    (hq : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (c : Fin r₃ → S.X₂.val.obj (op U)),
      q.val.app (op U)
          (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
            (wedge (M := S.X₂) (r := r₃) (U := U) c)) =
        tmulSection (M := exteriorPower S.X₁ r₁) (N := exteriorPower S.X₃ r₃)
          (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₃) (r := r₃) (U := U) (fun i ↦ S.g.val.app (op U) (c i)))) :
    ∃ w : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₂ r₃ ⟶ exteriorPower S.X₂ r₂,
      kernel.ι q ≫ w = 0 ∧ ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (c : Fin r₃ → S.X₂.val.obj (op U)),
        w.val.app (op U)
            (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
              (wedge (M := S.X₂) (r := r₃) (U := U) c)) =
          wedge (M := S.X₂) (r := r₂) (U := U)
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))
```

## Users

The downstream.py --uses scan finds seven downstream modules. The only direct
consumer and declaration user is the glue module; it is unclaimed. No upstream
source file, target statement, public consumer signature or definition changes.
All consumers keep the same exteriorSheaf API, with no change in mathematical
meaning, so no target statement review is reopened by a changed definition.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Unchanged; consumer API is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Unchanged; consumer API is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Unchanged; consumer API is preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphism | unclaimed | Unchanged; compiles against the adapted glue consumer. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismGlue | unclaimed | Replace the private import, add two proved private helpers, and change the kernel theorem call. Public imports and theorem signature are verbatim. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocal | unclaimed | Unchanged; compiles against the adapted glue consumer. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Unchanged; consumer API is preserved. |

## Status

landed 20261021T011042-L-2033555 2026-10-21 (merge of deliver/U4/Sheaf.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel)
