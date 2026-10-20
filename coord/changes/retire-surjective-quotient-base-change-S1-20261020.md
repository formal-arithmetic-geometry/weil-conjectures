# Algebra.quotientBaseChange and Algebra.quotientBaseChange_obj_iso

## Reason

Retire the Sheaf copy listed in coord/retire-items.tsv in favor of the adopted upstream
module. The shared tree now has no module importing the copy, and no use of its
existential theorem outside the copy itself. The four consumers listed in the retirement
row have already been retired; their upstream twins import the upstream base-change module.
Keeping the copy duplicates the public functor and its adjoint instance.

## Old

From lean/Sheaf/RingTheory/SurjectiveQuotientBaseChange.lean:

```lean
noncomputable def quotientBaseChange {A B : Type u} [CommRing A] [CommRing B]
    (π : A →+* B) : CommAlgCat.{u} A ⥤ CommAlgCat.{u} B :=
  (commAlgCatEquivUnder (CommRingCat.of A)).functor ⋙
    Under.pushout (CommRingCat.ofHom π) ⋙
      (commAlgCatEquivUnder (CommRingCat.of B)).inverse

noncomputable instance {A B : Type u} [CommRing A] [CommRing B] (π : A →+* B) :
    (quotientBaseChange π).IsLeftAdjoint := by
  unfold quotientBaseChange
  infer_instance

theorem quotientBaseChange_obj_iso
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A C]
    (π : A →+* B) (hπ : Function.Surjective π)
    (I : Ideal A) (hker : RingHom.ker π = I) :
    ∃ (_ : Algebra B (C ⧸ I.map (algebraMap A C))),
      Nonempty ((quotientBaseChange π).obj (CommAlgCat.of A C) ≅
        CommAlgCat.of B (C ⧸ I.map (algebraMap A C)))
```

## New

Withdraw lean/Sheaf/RingTheory/SurjectiveQuotientBaseChange.lean using deleted.txt.
The delivery tool initially empties the module; the maintainer removes the empty file.
Use the existing Algebra.quotientBaseChange and its existing left-adjoint instance from
WeilConjectures.RingTheory.SurjectiveQuotientBaseChange. Attach the DAG node to this
existing explicit quotient isomorphism:

```lean
noncomputable def quotientBaseChangeObjIso
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A C]
    (π : A →+* B) (hπ : Function.Surjective π)
    (I : Ideal A) (hker : RingHom.ker π = I)
    [Algebra B (C ⧸ I.map (algebraMap A C))]
    (hcomp : (algebraMap B (C ⧸ I.map (algebraMap A C))).comp π =
      (Ideal.Quotient.mk _).comp (algebraMap A C)) :
    (quotientBaseChange π).obj (CommAlgCat.of A C) ≅
      CommAlgCat.of B (C ⧸ I.map (algebraMap A C))
```

The node's existential statement stays unchanged. Its B-action is constructed by descending
A -> C/IC along pi with RingHom.liftOfSurjective. The kernel condition is
Ideal.le_comap_map after rewriting ker(pi) = I, and the compatibility equation is
RingHom.liftOfSurjective_comp_apply. The upstream isomorphism then proves exactly the
old conclusion. The complete compiled derivation is included in the report. No public
compatibility module is needed because the old theorem has no consumers.

## Users

The read-only scan `tools/downstream.py Sheaf.RingTheory.SurjectiveQuotientBaseChange
--uses quotientBaseChange_obj_iso` found zero downstream modules and only the declaration
itself as a textual use. A scan of all Lean sources found no import of the copy.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.SurjectiveQuotientBaseChange | S1 | Withdrawn unused duplicate. |
| WeilConjectures.RingTheory.PointedEtaleQuotientFinal | unmodified | Already imports upstream. |
| WeilConjectures.RingTheory.PointedEtaleQuotientFunctor | unmodified | Already imports upstream. |
| WeilConjectures.RingTheory.PointedEtaleQuotientPoint | unmodified | Already imports upstream. |
| WeilConjectures.RingTheory.PointedEtaleQuotientPointBijective | unmodified | Already imports upstream. |

The node lem-sbc-surjective-quotient-base-change now records the upstream explicit
isomorphism and the elementary construction of its compatible action. No source-library
file or target statement is changed; no target definition changes meaning.

## Status

landed 20261020T135424-L-1821639 2026-10-20 (merge of deliver/S1/Sheaf.RingTheory.SurjectiveQuotientBaseChange)
