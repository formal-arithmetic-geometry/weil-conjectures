# homologyEvaluation_roof_naturality

## Reason

The preflight conservatively flags the new section variables, local notation,
open command and local instance registrations as a possible interface change.
This record documents that flag. All new helper declarations are private,
all instance registrations are local to section Evaluation, and the section
ends before the original public theorem. No public definition, signature,
visibility, attribute or public import changes. There is no global instance.
The same tensor and internal-Hom structures are already proved in the source
library. No targets need statement review, because their definitions and
statements do not change.

## Old

There was no Evaluation section or helper context. The public signature was:

```lean
theorem homologyEvaluation_roof_naturality
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    {R : Sheaf S CommRingCat.{u}}
    (A E L K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (π : ∀ (B M : CochainComplex (SheafOfModules.{u}
        ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (n a b : ℤ), a + n = b →
        ((homComplex (R := R) B M).X n ⟶
          SheafOfModules.homObj (R := R) (B.X a) (M.X b)))
    (hπdiff : ∀ (B M : CochainComplex (SheafOfModules.{u}
        ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (n m a b b' a' : ℤ) (_hnm : n + 1 = m)
      (hab : a + m = b) (hb' : a + n = b') (ha' : a' + n = b),
      (homComplex (R := R) B M).d n m ≫ π B M m a b hab =
        π B M n a b' hb' ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (M.d b' b) -
          n.negOnePow • (π B M n a' b ha' ≫
            SheafOfModules.homObjMap (R := R) (B.d a a') (𝟙 _)))
    (hπnat : ∀ (B B' M M' : CochainComplex (SheafOfModules.{u}
        ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (t : B' ⟶ B) (s : M ⟶ M') (n a b : ℤ) (hab : a + n = b),
      ((((homComplexFunctor (R := R)).map t.op).app M) ≫
          ((homComplexFunctor (R := R)).obj (op B')).map s).f n ≫ π B' M' n a b hab =
        π B M n a b hab ≫ SheafOfModules.homObjMap (R := R) (t.f a) (s.f b))
    (n : ℤ) (q : L ⟶ A) (p : L ⟶ E)
    [IsIso (HomologicalComplex.homologyMap
      (((homComplexFunctor (R := R)).map p.op).app K) n)] :
    let Q := homComplex (R := R) A K
    let P := homComplex (R := R) E K
    ∀ (g : Q.homology n ⟶ SheafOfModules.homObj (R := R)
        (A.homology (-n)) (K.homology 0))
      (d : Q.cycles n ⟶ SheafOfModules.homObj (R := R) (A.cycles (-n)) (K.cycles 0))
      (f : P.homology n ⟶ SheafOfModules.homObj (R := R)
        (E.homology (-n)) (K.homology 0))
      (c : P.cycles n ⟶ SheafOfModules.homObj (R := R) (E.cycles (-n)) (K.cycles 0)),
      d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
        Q.iCycles n ≫ π A K n (-n) 0 (by omega) ≫
          SheafOfModules.homObjMap (R := R) (A.iCycles (-n)) (𝟙 _) →
      d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
        Q.homologyπ n ≫ g ≫
          SheafOfModules.homObjMap (R := R) (A.homologyπ (-n)) (𝟙 _) →
      c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
        P.iCycles n ≫ π E K n (-n) 0 (by omega) ≫
          SheafOfModules.homObjMap (R := R) (E.iCycles (-n)) (𝟙 _) →
      c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
        P.homologyπ n ≫ f ≫
          SheafOfModules.homObjMap (R := R) (E.homologyπ (-n)) (𝟙 _) →
      g ≫ SheafOfModules.homObjMap (R := R)
          (HomologicalComplex.homologyMap q (-n)) (𝟙 _) =
        HomologicalComplex.homologyMap
            (((homComplexFunctor (R := R)).map q.op).app K) n ≫
          inv (HomologicalComplex.homologyMap
            (((homComplexFunctor (R := R)).map p.op).app K) n) ≫
          f ≫ SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.homologyMap p (-n)) (𝟙 _)
```

## New

The public signature is identical, verbatim:

```lean
theorem homologyEvaluation_roof_naturality
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    {R : Sheaf S CommRingCat.{u}}
    (A E L K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (π : ∀ (B M : CochainComplex (SheafOfModules.{u}
        ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (n a b : ℤ), a + n = b →
        ((homComplex (R := R) B M).X n ⟶
          SheafOfModules.homObj (R := R) (B.X a) (M.X b)))
    (hπdiff : ∀ (B M : CochainComplex (SheafOfModules.{u}
        ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (n m a b b' a' : ℤ) (_hnm : n + 1 = m)
      (hab : a + m = b) (hb' : a + n = b') (ha' : a' + n = b),
      (homComplex (R := R) B M).d n m ≫ π B M m a b hab =
        π B M n a b' hb' ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (M.d b' b) -
          n.negOnePow • (π B M n a' b ha' ≫
            SheafOfModules.homObjMap (R := R) (B.d a a') (𝟙 _)))
    (hπnat : ∀ (B B' M M' : CochainComplex (SheafOfModules.{u}
        ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (t : B' ⟶ B) (s : M ⟶ M') (n a b : ℤ) (hab : a + n = b),
      ((((homComplexFunctor (R := R)).map t.op).app M) ≫
          ((homComplexFunctor (R := R)).obj (op B')).map s).f n ≫ π B' M' n a b hab =
        π B M n a b hab ≫ SheafOfModules.homObjMap (R := R) (t.f a) (s.f b))
    (n : ℤ) (q : L ⟶ A) (p : L ⟶ E)
    [IsIso (HomologicalComplex.homologyMap
      (((homComplexFunctor (R := R)).map p.op).app K) n)] :
    let Q := homComplex (R := R) A K
    let P := homComplex (R := R) E K
    ∀ (g : Q.homology n ⟶ SheafOfModules.homObj (R := R)
        (A.homology (-n)) (K.homology 0))
      (d : Q.cycles n ⟶ SheafOfModules.homObj (R := R) (A.cycles (-n)) (K.cycles 0))
      (f : P.homology n ⟶ SheafOfModules.homObj (R := R)
        (E.homology (-n)) (K.homology 0))
      (c : P.cycles n ⟶ SheafOfModules.homObj (R := R) (E.cycles (-n)) (K.cycles 0)),
      d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
        Q.iCycles n ≫ π A K n (-n) 0 (by omega) ≫
          SheafOfModules.homObjMap (R := R) (A.iCycles (-n)) (𝟙 _) →
      d ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
        Q.homologyπ n ≫ g ≫
          SheafOfModules.homObjMap (R := R) (A.homologyπ (-n)) (𝟙 _) →
      c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
        P.iCycles n ≫ π E K n (-n) 0 (by omega) ≫
          SheafOfModules.homObjMap (R := R) (E.iCycles (-n)) (𝟙 _) →
      c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
        P.homologyπ n ≫ f ≫
          SheafOfModules.homObjMap (R := R) (E.homologyπ (-n)) (𝟙 _) →
      g ≫ SheafOfModules.homObjMap (R := R)
          (HomologicalComplex.homologyMap q (-n)) (𝟙 _) =
        HomologicalComplex.homologyMap
            (((homComplexFunctor (R := R)).map q.op).app K) n ≫
          inv (HomologicalComplex.homologyMap
            (((homComplexFunctor (R := R)).map p.op).app K) n) ≫
          f ≫ SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.homologyMap p (-n)) (𝟙 _)
```

The added helper context is scoped to a section closed before that theorem:

```lean
section Evaluation
variable {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
  {R : Sheaf S CommRingCat.{u}}

set_option quotPrecheck false in
set_option hygiene false in
local notation "Mod" => SheafOfModules.{u}
  ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

open MonoidalCategory
@[instance_reducible]
private noncomputable def evaluationMonoidal : MonoidalCategory Mod :=
  SheafOfModules.monoidalCategory R
attribute [local instance] evaluationMonoidal

@[instance_reducible]
private noncomputable def evaluationSymmetric : SymmetricCategory Mod :=
  SheafOfModules.symmetricCategory R
attribute [local instance] evaluationSymmetric

@[instance_reducible]
private noncomputable def evaluationClosed : MonoidalClosed Mod :=
  SheafOfModules.monoidalClosed (R := R)
attribute [local instance] evaluationClosed

end Evaluation
```

All declarations in this section are private and proved (or the three private
structures reusing existing source data); no signature refers to private data.
The two added imports are proof-only. Existing importers see the same public
interface, as the module's unchanged public signature and imports confirm.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.HomologyEvaluationRoofNaturality
--uses homologyEvaluation_roof_naturality` finds only the module itself and
RoofComparison as textual uses of the theorem. None requires adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.HomologyEvaluationRoofNaturality | V2 | Private proof context only; same public statement. |
| Sheaf.Algebra.Homology.HomologyEvaluationRoofComparison | unclaimed in local claim snapshot | Calls the unchanged theorem; no edit needed. |

All other transitive importers inherit the same public declarations. In
particular no global notation or instance was registered. The conservative
command-change marker names no changed public declaration, so it produces
no additional textual users requiring adaptation.

## Status

landed 20261013T222421-L-1229357 2026-10-13 (merge of deliver/V2/Sheaf.Algebra.Homology.HomologyEvaluationRoofNaturality)
