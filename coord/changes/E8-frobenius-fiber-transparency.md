# WeilConjectures.PurityFiniteSetting.frobeniusFiber

## Reason

The four abbreviations eagerly expand chosen scheme pullbacks and their maps
while instantiating categorical coherence. Profiling the new proof reported
thousands of reductions of `frobeniusFiber`, `pullback`, `LimitCone.cone`, and
`getLimitCone`. Use ordinary transparent definitions with verbatim types and
bodies, then keep these values folded locally during the categorical calculation.
The local attribute scope starts after the existing geometric proofs and the
coefficient-characteristic proof. This preserves the exact same fibre and maps;
there is no alternative pullback or new witness.

## Old

```lean
abbrev frobeniusFiber (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    Over (Spec (CommRingCat.of P.field.k)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k)))).obj T₀

abbrev frobeniusMap (P : PurityFiniteSetting.{u})
    {X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))} (f₀ : X₀ ⟶ Y₀) :
    (P.frobeniusFiber X₀).left ⟶ (P.frobeniusFiber Y₀).left :=
  ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k)))).map f₀).left

abbrev frobeniusGaloisMap (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    (P.frobeniusFiber T₀).left ⟶ (P.frobeniusFiber T₀).left :=
  P.field.galoisMap T₀.hom
    (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic P.field.k₀ P.field.k _
      (Fintype.ofFinite P.field.k₀) _ _ _)

abbrev frobeniusArithmeticMap (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    (P.frobeniusFiber T₀).left ⟶ (P.frobeniusFiber T₀).left :=
  P.field.galoisMap T₀.hom
    (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic P.field.k₀ P.field.k _
      (Fintype.ofFinite P.field.k₀) _ _ _).symm
```

## New

```lean
def frobeniusFiber (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    Over (Spec (CommRingCat.of P.field.k)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k)))).obj T₀

def frobeniusMap (P : PurityFiniteSetting.{u})
    {X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))} (f₀ : X₀ ⟶ Y₀) :
    (P.frobeniusFiber X₀).left ⟶ (P.frobeniusFiber Y₀).left :=
  ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k)))).map f₀).left

def frobeniusGaloisMap (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    (P.frobeniusFiber T₀).left ⟶ (P.frobeniusFiber T₀).left :=
  P.field.galoisMap T₀.hom
    (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic P.field.k₀ P.field.k _
      (Fintype.ofFinite P.field.k₀) _ _ _)

def frobeniusArithmeticMap (P : PurityFiniteSetting.{u})
    (T₀ : Over (Spec (CommRingCat.of P.field.k₀))) :
    (P.frobeniusFiber T₀).left ⟶ (P.frobeniusFiber T₀).left :=
  P.field.galoisMap T₀.hom
    (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic P.field.k₀ P.field.k _
      (Fintype.ofFinite P.field.k₀) _ _ _).symm
```

The factorization proof has four forced `rw`-to-`erw` changes: the first
projection calculation for each ordering, the second projection calculation for
the second ordering, and the final inverse-action cancellation. The previous
`rw` calls cannot match the underlying `field.galoisMap` equations through the
new semireducible definitions. `erw` permits precisely that unfolding; the
statements and argument stay identical. No other original proof line changes.

## Users

The current downstream query for the item finds no Lean importers. The existing
factorization and square proofs remain in the same module and are checked against
the new transparency. All downstream statements and target meanings are identical
by delta reduction. The DAG parents, node attachments and unit route stay intact.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.SchemeGeometricFrobenius | E8 | Same fibre and maps; local folding during the new categorical proof. |

## Status

landed 20261021T120348-L-3836512 2026-10-21 (merge of deliver/E8/Sheaf.SixFunctors.SchemeGeometricFrobenius)
