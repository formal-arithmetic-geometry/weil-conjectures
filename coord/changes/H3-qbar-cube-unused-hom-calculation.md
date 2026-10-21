# AlgebraicGeometry.ProEtale.CondensedRing.qbarPull_square_cube

## Reason

The current restored item contains zero holes but its unchanged whole-file compile
is 53.4 seconds, close to the fixed 60-second limit. It still elaborates and checks
a concrete hom-component square equation that no proof uses. The public cube
already follows directly from the isomorphism equation through the generic
coefficientCube_of_iso. Remove that redundant concrete calculation, retaining
all used proofs, definitions and the complete public interface.

## Old

```lean
private lemma qbarPull_square_cube
    (sq : CommSq g' f' f g) (M : PadicSubfieldConstructible Y ℓ E) :
    (constructibleToPadicAlgCl X' ℓ E).map
        ((boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ
          (sq.asOver (Spec (.of k)))).hom.app M) ≫
      (constructibleToQbarPullIso ℓ k E g'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (f.asOver (Spec (.of k)))).obj M)).hom ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (g'.asOver (Spec (.of k)))).map
        (constructibleToQbarPullIso ℓ k E f M).hom =
    (constructibleToQbarPullIso ℓ k E f'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (g.asOver (Spec (.of k)))).obj M)).hom ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (f'.asOver (Spec (.of k)))).map
        (constructibleToQbarPullIso ℓ k E g M).hom ≫
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        (sq.asOver (Spec (.of k)))).hom.app
          ((constructibleToPadicAlgCl Y ℓ E).obj M) := by
  have h := congrArg Iso.hom (qbarPull_square_cube_iso ℓ k E f g f' g' sq M)
  dsimp only [Iso.trans, Functor.mapIso, Iso.app] at h
  exact h
```

## New

The unused private lemma is removed. The public theorem retains exactly this proof:

```lean
  exact coefficientCube_of_iso _ _ _ _ _ _ V
    (qbarPull_square_cube_iso ℓ k E f g f' g' sq V)
```

No definition data, global or local reducibility attribute, public declaration,
public import, geometric hypothesis, or target statement changes. The DAG route
retains the composition comparison, equality transport, rectangle pasting and
generic isomorphism cancellation; only its mention of the unused calculation is
updated.

## Users

The downstream query reports zero live importers. Searching both library roots
and quarantined sources finds no caller of qbarPull_square_cube. Its only textual
occurrences are its declarations in the current and archived item. The sole
archived direct importer uses a normal import and calls the public theorem at
line 376, so the removed private declaration is inaccessible there in any case.
No live or quarantined source imports this module with import all. The public
interface and all consumer theorem applications remain unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedQbarPullbackCube | H3 | Remove the unused concrete hom-component calculation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unqueried; not edited | Identical public theorem application; no access to removed private helper. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unqueried; not edited | Same public environment; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unqueried; not edited | Same public environment; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unqueried; not edited | Same public environment; no adaptation. |

## Status

landed 20261021T193351-L-1133436 2026-10-21 (merge of deliver/H3/Sheaf.Paper.CondensedQbarPullbackCube)
