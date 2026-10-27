# AlgebraicGeometry.Scheme.proEtaleProjectionMateData

## Reason

STATEMENT-DISPUTED (repaired): arbitrary independent shift structures need not make a
fixed natural transformation shift-compatible. The old split universally quantified
those structures, although the source and its parent need jointly chosen canonical
structures. Over integer coefficients, twist only the target shift comparison by
(-1)^n. At n = 1 the compatibility equation changes sign. Requiring both equations
would force twice the invertible unit component to vanish, impossible for the
nonzero integer coefficient ring (take the identity scheme map and ring unit E).

The corrected theorem constructs compatible shifts together with the mate and its
exactness. All clauses of the parent theorem remain, with its signature unchanged.
The proof uses the existing global-model construction and comparison, exact fixed
factor tensor theorem and signed projection normalization, without new holes.

## Old

```lean
theorem proEtaleProjectionMateData
    [_sF : ((Functor.curryObj a.tensor).obj
      ((proEtaleRingDerivedDirectImage f R S c).obj E)).CommShift ℤ]
    [_sG : (proEtaleRingDerivedPullback f R S c ⋙
      (Functor.curryObj b.tensor).obj E ⋙
        proEtaleRingDerivedDirectImage f R S c).CommShift ℤ] :
    ∃ τ : (Functor.curryObj a.tensor).obj
          ((proEtaleRingDerivedDirectImage f R S c).obj E) ⟶
        proEtaleRingDerivedPullback f R S c ⋙
          (Functor.curryObj b.tensor).obj E ⋙ proEtaleRingDerivedDirectImage f R S c,
        (∀ P, τ.app P = proEtaleProjectionFormulaMate f R S c a b E P) ∧
        NatTrans.CommShift τ ℤ ∧
        IsIso (τ.app ((DerivedCategory.singleFunctor (proEtaleRingModules Y R) 0).obj
          (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))))
```

## New

```lean
theorem proEtaleProjectionMateData :
    ∃ (_sF : ((Functor.curryObj a.tensor).obj
      ((proEtaleRingDerivedDirectImage f R S c).obj E)).CommShift ℤ)
      (_sG : (proEtaleRingDerivedPullback f R S c ⋙
      (Functor.curryObj b.tensor).obj E ⋙
        proEtaleRingDerivedDirectImage f R S c).CommShift ℤ),
      ((Functor.curryObj a.tensor).obj
        ((proEtaleRingDerivedDirectImage f R S c).obj E)).IsTriangulated ∧
      (proEtaleRingDerivedPullback f R S c ⋙
        (Functor.curryObj b.tensor).obj E ⋙
          proEtaleRingDerivedDirectImage f R S c).IsTriangulated ∧
    ∃ τ : (Functor.curryObj a.tensor).obj
          ((proEtaleRingDerivedDirectImage f R S c).obj E) ⟶
        proEtaleRingDerivedPullback f R S c ⋙
          (Functor.curryObj b.tensor).obj E ⋙ proEtaleRingDerivedDirectImage f R S c,
        (∀ P, τ.app P = proEtaleProjectionFormulaMate f R S c a b E P) ∧
        NatTrans.CommShift τ ℤ ∧
        IsIso (τ.app ((DerivedCategory.singleFunctor (proEtaleRingModules Y R) 0).obj
          (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))))
```

## Users

`tools/downstream.py --uses proEtaleProjectionMateData` found only the declaration
itself and the following consumer. A direct-import search has the same sole consumer.
The transitive imports mention no other use of this declaration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProEtaleProjectionMateData | D7 | Correct and prove the joint data statement. |
| Sheaf.Paper.ProEtaleProjectionMateExact | unclaimed | Its signature stays verbatim; replace the now-invalid independent-shift assembly by applying the corrected theorem. Remove the unused private ShiftData import. |

The consumer is compiled against the corrected module in this delivery. No
shared definition, instance, attribute, or public import changes. No target statement
or definition used by a target changes. Private helpers use only existing objects.

## Status

landed 20261027T034630-L-3667613 2026-10-27 (merge of deliver/D7/Sheaf.Paper.ProEtaleProjectionMateData)
