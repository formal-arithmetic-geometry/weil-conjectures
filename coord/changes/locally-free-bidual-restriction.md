# SheafOfModules.bidualOverIso

## Reason

Computing the supplied restriction isomorphism repeatedly unfolds an equality transport
between whole internal-Hom presheaves, exceeding the single-file compile limit. Replace
that implementation by an explicit sectionwise isomorphism. The forward and inverse maps
are precisely the existing restrictOverHomObjFwd and restrictOverHomObjBwd, using the
canonical iterated-slice equivalence; no choices or new mathematical objects are introduced.
The double-dual composite, coefficients, domain and codomain stay the same.

## Old

```lean
noncomputable def bidualOverIso
    (M : CategoryTheory.ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) (U : C) :
    (homObj (R := R) (homObj (R := R) M (unit _)) (unit _)).over U ≅
      homObj (R := R.over U) (homObj (R := R.over U) (M.over U) (unit _)) (unit _) :=
  overHomObjIso (R := R) (homObj (R := R) M (unit _)) (unit _) U ≪≫
    ((homFunctor (R.over U)).flip.obj (unit _)).mapIso
      (overHomObjIso (R := R) M (unit _) U).symm.op
```

## New

```lean
noncomputable def bidualOverIso
    (M : CategoryTheory.ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) (U : C) :
    (homObj (R := R) (homObj (R := R) M (unit _)) (unit _)).over U ≅
      homObj (R := R.over U) (homObj (R := R.over U) (M.over U) (unit _)) (unit _) :=
  evaluationOverHomIso (R := R) (homObj (R := R) M (unit _)) (unit _) U ≪≫
    ((homFunctor (R.over U)).flip.obj (unit _)).mapIso
      (evaluationOverHomIso (R := R) M (unit _) U).symm.op
```

The new public helper evaluationOverHomIso constructs both linear maps explicitly and
uses PresheafOfModules.isoMk to infer inverse naturality. Its inverse laws are the existing
restrictOverHomObjBwd_fwd and restrictOverHomObjFwd_bwd. The double-dual evaluation
compatibility is proved componentwise in locallyFreeEvaluationBiduality.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.LocallyFreeEvaluationBiduality | A4 | Proves all clauses with the sectionwise restriction isomorphism. |

The downstream query reports zero other modules. No target uses this definition in its
statement. The theorem and the three original helper signatures are unchanged.

## Status

landed 20261024T184530-L-3063305 2026-10-24 (merge of deliver/A4/Sheaf.Algebra.Category.ModuleCat.Sheaf.LocallyFreeEvaluationBiduality)
