# AlgebraicGeometry.ProEtale.DiagonalCoefficients.completedAffineFree_presheaf_localDual

## Reason

The old hypothesis `y ≠ 0` is false. Let `X = Spec(F₂)` and let `U = W` be the
finite étale affine scheme `X ⊔ X`. A map `W → U` over `X` is a function from its
two connected components to the two components of `U`. Write `a = 00`, `b = 11`,
`c = 01`, and `d = 10`. They are four distinct maps. The free-presheaf section
`y = [a] + [b] - [c] - [d]` has coefficient one at `a`, so is nonzero. Completed
coefficient sections on this finite discrete scheme are `Z₂ × Z₂`, a nonzero
ring. On the first component, `a=c` and `b=d`; on the second, `a=d` and `b=c`.
Thus `y` restricts to zero on the two-component Zariski cover, so its
sheafification image is zero. Every linear sheaf map sends that image to zero.
This contradicts the old conclusion, even with a finite étale representable.

The proved private theorem `free_presheaf_swap_kernel` verifies the algebraic
and sheafification calculation for any ringed site, given these local swap
relations and a nonzero section ring. It uses coefficient evaluation, naturality
of the sheafification unit, and separatedness. It does not claim to formalize
the construction of the concrete scheme example.

The intended geometric detection argument concerns nonzero *sheafified*
sections. Replace the hypothesis by `eta(y) ≠ 0`, keeping the conclusion.
This is an explicit correction of a false intermediate statement, not a proof
of the old statement or a claimed decrease in proof holes. The original single
geometric proof obligation remains a named theorem with `sorry`.

## Old

```lean
theorem completedAffineFree_presheaf_localDual (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ) (hU : proAffineEtale U.unop.hom)
    (W : X.ProEt) :
    let R := Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)
    let F := (PresheafOfModules.free R.obj).obj
      (uliftYoneda.{u + 1}.obj U.unop)
    let P := (PresheafOfModules.sheafification (𝟙 R.obj)).obj F
    ∀ y : F.obj (op W), y ≠ 0 →
      ∃ (φ : P.over W ⟶ SheafOfModules.unit (R.over W)),
        φ.val.app (op (Over.mk (𝟙 W)))
          (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app F).app
            (op W) y) ≠ 0
```

## New

```lean
theorem completedAffineFree_presheaf_localDual (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (U : X.ProEtᵒᵖ) (hU : proAffineEtale U.unop.hom)
    (W : X.ProEt) :
    let R := Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)
    let F := (PresheafOfModules.free R.obj).obj
      (uliftYoneda.{u + 1}.obj U.unop)
    let P := (PresheafOfModules.sheafification (𝟙 R.obj)).obj F
    ∀ y : F.obj (op W),
      (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app F).app
        (op W) y) ≠ 0 →
      ∃ (φ : P.over W ⟶ SheafOfModules.unit (R.over W)),
        φ.val.app (op (Over.mk (𝟙 W)))
          (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app F).app
            (op W) y) ≠ 0
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedAffineFreePresheafLocalDual | W3 | Repair the false hypothesis; add the proved private kernel certificate. |
| Sheaf.Paper.CompletedAffineFreeLocalDual | unclaimed in the shared claim records | Case-split on the image of the lifted section instead of on the representative. Its public signature is identical. |

`tools/downstream.py --uses completedAffineFree_presheaf_localDual` finds only
these two textual users, and there is exactly one direct importer. The other
241 downstream modules use the unchanged interface of the consumer. No
definition, instance, attribute, public import, target statement, or universe
of an existing public declaration changes. The correction does not reopen a
target-definition review: no target definition is changed.

The sole DAG citer is `lem-sfb-completed-affine-free-local-dual`; its statement
continues to hold and its proof plan is updated to the repaired application.
The unit's statement and route are preserved.

## Status

landed 20261027T053012-L-506028 2026-10-27 (merge of deliver/W3/Sheaf.Paper.CompletedAffineFreePresheafLocalDual)
