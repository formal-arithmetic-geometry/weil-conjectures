# AlgebraicGeometry.Scheme.picardCoefficientTranspose

## Reason

Restore the assigned coefficient-transpose module after the cluster-restore
regression in `coord/rework.tsv`. The live Lean path is absent; the full
implementation remains in quarantine. The two existing DAG attachments and
the quarantined factorization and pasting consumers still require it.

The restored file is byte-for-byte identical to the quarantine archive.
The coefficient transpose remains the explicit counit composite with the
fixed tensor single-coefficient morphism and canonical fibre-product lift.
The complete archived pasting proof now uses the restored, proved tensor
composition API. This is a restoration of missing implementation, with zero
holes, rather than a rebase or a change of mathematical route.

## Old

No file exists at the live library path. The preserved archived definitions are:

```lean
@[irreducible]
def coefficientCounitTranspose {A B W V : Scheme.{v}}
    (p : A ⟶ W) (p' : B ⟶ V) (r : V ⟶ W) (a : B ⟶ A)
    (ha : a ≫ p = p' ≫ r) (K : schemeDerivedCategory A)
    (N : schemeDerivedCategory B) (e : (derivedPullback a).obj K ⟶ N) :
    (derivedPullback p').obj
      ((derivedPullback r).obj ((schemeDerivedDirectImage p).obj K)) ⟶ N :=
  canonicalDerivedSquareComparison p p' r a ha ((schemeDerivedDirectImage p).obj K) ≫
    (derivedPullback a).map ((canonicalSchemeDerivedAdjunction p).counit.app K) ≫ e

@[irreducible]
def picardCoefficientTranspose {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S) :
  ∀ {V : Scheme.{v}} (r : V ⟶ W),
    (derivedPullback (pullback.snd f (r ≫ k))).obj
      ((derivedPullback r).obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
              ((Modules.tensorPullback (pullback.fst f k)).obj L)))) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (r ≫ k)).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f (r ≫ k))).obj L) :=
  fun {V : Scheme.{v}} (r : V ⟶ W) ↦ by
    let M := (Modules.tensorPullback (pullback.fst f k)).obj L
    let a : pullback f (r ≫ k) ⟶ pullback f k :=
      pullback.lift (pullback.fst f (r ≫ k)) (pullback.snd f (r ≫ k) ≫ r)
        (by rw [Category.assoc]; exact pullback.condition)
    have ha : a ≫ pullback.fst f k = pullback.fst f (r ≫ k) := pullback.lift_fst ..
    have hb : a ≫ pullback.snd f k = pullback.snd f (r ≫ k) ≫ r := pullback.lift_snd ..
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj M
    exact coefficientCounitTranspose (pullback.snd f k)
      (pullback.snd f (r ≫ k)) r a hb K _
      (tensorSingleCoefficientMap (pullback.fst f k)
        (pullback.fst f (r ≫ k)) a ha L)
```

## New

Restore the original module and the following identical definitions:

```lean
@[irreducible]
def coefficientCounitTranspose {A B W V : Scheme.{v}}
    (p : A ⟶ W) (p' : B ⟶ V) (r : V ⟶ W) (a : B ⟶ A)
    (ha : a ≫ p = p' ≫ r) (K : schemeDerivedCategory A)
    (N : schemeDerivedCategory B) (e : (derivedPullback a).obj K ⟶ N) :
    (derivedPullback p').obj
      ((derivedPullback r).obj ((schemeDerivedDirectImage p).obj K)) ⟶ N :=
  canonicalDerivedSquareComparison p p' r a ha ((schemeDerivedDirectImage p).obj K) ≫
    (derivedPullback a).map ((canonicalSchemeDerivedAdjunction p).counit.app K) ≫ e

@[irreducible]
def picardCoefficientTranspose {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S) :
  ∀ {V : Scheme.{v}} (r : V ⟶ W),
    (derivedPullback (pullback.snd f (r ≫ k))).obj
      ((derivedPullback r).obj
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
              ((Modules.tensorPullback (pullback.fst f k)).obj L)))) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f (r ≫ k)).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f (r ≫ k))).obj L) :=
  fun {V : Scheme.{v}} (r : V ⟶ W) ↦ by
    let M := (Modules.tensorPullback (pullback.fst f k)).obj L
    let a : pullback f (r ≫ k) ⟶ pullback f k :=
      pullback.lift (pullback.fst f (r ≫ k)) (pullback.snd f (r ≫ k) ≫ r)
        (by rw [Category.assoc]; exact pullback.condition)
    have ha : a ≫ pullback.fst f k = pullback.fst f (r ≫ k) := pullback.lift_fst ..
    have hb : a ≫ pullback.snd f k = pullback.snd f (r ≫ k) ≫ r := pullback.lift_snd ..
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj M
    exact coefficientCounitTranspose (pullback.snd f k)
      (pullback.snd f (r ≫ k)) r a hb K _
      (tensorSingleCoefficientMap (pullback.fst f k)
        (pullback.fst f (r ≫ k)) a ha L)
```

Restore `coefficientCounitTranspose_eq`, the proved private categorical
pasting helpers, and `picardCoefficientTranspose_pasting` with their complete
proofs. All signatures, visibility, attributes, universes, definition data,
public imports and docstrings are identical to the archived file. Both DAG
attachments and all proof dependencies are preserved. There is no change to
a target statement or to a definition already present in the live library.

## Users

`tools/downstream.py` reports `unknown module(s)` for the absent live module.
A source search in both `lean/` and `quarantine/` finds exactly the two direct
importers below; the corresponding two DAG parents cite the retained nodes.
No live consumer imports the absent module. No consumer is edited or withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardCoefficientTransposePasting | F3 | Restore the assigned module and its original public declarations. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeFactorization | no local claim record; quarantined | Its public import and use of the coefficient transpose regain the same interface; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposePasting | no local claim record; quarantined | Its proof import and use of the pasting theorem regain the same interface; no adaptation. |

The consumer files remain quarantined for their own rework assignments.
Restoration preserves the public API they were written against, including
the explicit coefficient comparison in the conclusion. The cube unit route
is unchanged.

## Status

landed 20261021T012357-L-2182413 2026-10-21 (merge of deliver/F3/Sheaf.AlgebraicGeometry.PicardCoefficientTransposePasting)
