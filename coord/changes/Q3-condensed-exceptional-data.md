# WeilConjectures.CondensedExceptionalReconstruction data module

## Reason

The raw-counit proof steps use the parent's types. They need a separate data module to
avoid importing the theorem which imports those steps. The original public definitions,
including all normalized unit and shift equations, are moved verbatim. This is a source
organization change, with two new intermediate records. No coefficient object is selected
from an unproved mere-existence theorem.

## Old

The following declarations lived in Sheaf.Paper.CondensedExceptionalReconstruction:

```lean
/-- Naturality of the actual reconstructed comparison for one supplied system map.
Source: current blueprint sk-prop-sp-integral-adjunction and sk-thm-sp-qbar.
(blueprint: lem-pur-condensed-exceptional-reconstruction). -/
def ComparisonNaturality
    (A : RealizationAt l (Field.{u} l) k D P.reduction X Y f c)
    (d e : Datum l k P) (hd : d.Admissible l k) (he : e.Admissible l k)
    (qd : Conclusion l k D d hd A) (qe : Conclusion l k D e he A)
    (b : d.L ⟶ e.L) (a : d.tower ⟶ e.tower) : Prop :=
    d.SystemMap l k b a qd.theta qe.theta →
    (realization l k D X).map (Datum.LimitMap l k a hd.reconstructs he.reconstructs) ≫
      (Conclusion.iso l k D qe).hom = (Conclusion.iso l k D qd).hom ≫
        (CondensedRing.boundedConstructibleUpperShriekOfCompactification
          (Profinite.padicAlgClRingObj l) l (f := X.map Y f) c).map
            ((realization l k D Y).map b)

/-- Same-degree level squares determine actual Brown-system compatibility.
Source: current blueprint sk-prop-sp-integral-adjunction and sk-thm-sp-qbar.
(blueprint: lem-pur-condensed-exceptional-reconstruction). -/
def SingleDegreeCompatibility
    (A : RealizationAt l (Field.{u} l) k D P.reduction X Y f c)
    (d e : Datum l k P) (hd : d.Admissible l k) (he : e.Admissible l k)
    (qd : Conclusion l k D d hd A) (qe : Conclusion l k D e he A)
    (r : ℤ) (b : d.L ⟶ e.L) (a : d.tower ⟶ e.tower) : Prop :=
    (∀ n : ℕ, ((P.source.proEtaleEvaluation.evaluation n).obj d.tower).IsGE r ∧
      ((P.source.proEtaleEvaluation.evaluation n).obj d.tower).IsLE r ∧
      ((P.source.proEtaleEvaluation.evaluation n).obj e.tower).IsGE r ∧
      ((P.source.proEtaleEvaluation.evaluation n).obj e.tower).IsLE r) →
    (∀ n : ℕ, (P.source.proEtaleEvaluation.evaluation n).map a ≫
        (e.toBrown l k n).hom = (d.toBrown l k n).hom ≫
          (P.source.proEtaleEvaluation.evaluation n).map
            (P.source.derived.system.inverse.map (P.brown.right.map ((input l k P).map b)))) →
    d.SystemMap l k b a qd.theta qe.theta

/-- The resulting comparisons are natural for actual compatible derived-system maps.
For systems in one common degree the level-identification squares imply compatibility.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: lem-pur-condensed-exceptional-reconstruction). -/
structure AtCompactification (P : Context l k X Y f c)
    (supportRealization : RealizationAt l (Field.{u} l) k D P.reduction X Y f c) where
  result : ∀ (d : Datum l k P) (h : d.Admissible l k),
    Conclusion l k D d h supportRealization
  naturality : ∀ (d e : Datum l k P) (hd : d.Admissible l k) (he : e.Admissible l k)
    (b : d.L ⟶ e.L) (a : d.tower ⟶ e.tower),
    ComparisonNaturality l k D supportRealization d e hd he (result d hd) (result e he) b a
  singleDegreeMaps : ∀ (d e : Datum l k P) (hd : d.Admissible l k) (he : e.Admissible l k)
    (r : ℤ) (b : d.L ⟶ e.L) (a : d.tower ⟶ e.tower),
    SingleDegreeCompatibility l k D supportRealization d e hd he
      (result d hd) (result e he) r b a

/-- The completed regular coefficient module in degree zero, constructed explicitly.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: lem-pur-condensed-exceptional-reconstruction). -/
abbrev regular (T : Base k) : PbcCompletedDerived T.scheme (pbcIntegralDatum l (Field.{u} l)) :=
  (DerivedCategory.singleFunctor
    (pbcModules T.scheme (pbcAdicCompletion T.scheme (pbcIntegralDatum l (Field.{u} l))))
    0).obj (normalizationRegular l k T)

/-- The integral predicate is stable under the ambient ordinary derived shifts.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: lem-pur-condensed-exceptional-reconstruction). -/
def IntegralShiftClosed (T : Base k) : Prop :=
  ∀ (K : Integral l (Field.{u} l) T.scheme) (n : ℤ),
    PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l (Field.{u} l))
      ((shiftFunctor (PbcCompletedDerived T.scheme (pbcIntegralDatum l (Field.{u} l))) n).obj
        K.obj)

/-- Restriction of the actual ambient shift to the integral full subcategory.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: lem-pur-condensed-exceptional-reconstruction). -/
def integralShift (T : Base k) (h : IntegralShiftClosed l k T) (n : ℤ) :
    Integral l (Field.{u} l) T.scheme ⥤ Integral l (Field.{u} l) T.scheme :=
  ObjectProperty.lift (PbcIsBoundedConstructibleComplete T.scheme
    (pbcIntegralDatum l (Field.{u} l)))
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme
      (pbcIntegralDatum l (Field.{u} l))) ⋙ shiftFunctor _ n) (fun K ↦ h K n)

/-- U sends the completed regular coefficient to the condensed tensor unit and
commutes with all integer shifts via natural isomorphisms.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: lem-pur-condensed-exceptional-reconstruction). -/
structure RealizationProperties where
  regular_mem : ∀ T : Base k, PbcIsBoundedConstructibleComplete T.scheme
    (pbcIntegralDatum l (Field.{u} l)) (regular l k T)
  coefficientInclusion : ∀ T : Base k, normalizationRegular l k T ⟶
    (normalizationOrdinaryRestriction l k D T).obj
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T.scheme))
  coefficientInclusion_normalized : ∀ T : Base k,
    IsCoefficientInclusion l k D T (coefficientInclusion T)
  coefficientUnit : ∀ T : Base k,
    ((realization l k D T).obj ⟨regular l k T, regular_mem T⟩).obj ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T.scheme))
  coefficientUnit_normalized : ∀ T : Base k,
    (normalizationAdjunction l k D T).homEquiv _ _
      ((normalizationComparison l k D T ⟨regular l k T, regular_mem T⟩).hom ≫
        (coefficientUnit T).hom) =
      normalizationDerivedInclusion l k D T (coefficientInclusion T)
  shiftClosed : ∀ T : Base k, IntegralShiftClosed l k T
  shifts : ∀ (T : Base k) (n : ℤ),
    integralShift l k T (shiftClosed T) n ⋙ realization l k D T ⋙
        (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) T.scheme)).ι ≅
      realization l k D T ⋙
        (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) T.scheme)).ι ⋙
          shiftFunctor _ n
  shifts_normalized : ∀ (T : Base k) (n : ℤ) (K : Integral l (Field.{u} l) T.scheme),
    (shifts T n).hom.app K =
      (normalizationComparison l k D T ((integralShift l k T (shiftClosed T) n).obj K)).inv ≫
        ((normalizationModel l k D T).commShiftIso n).hom.app K.obj ≫
          (shiftFunctor _ n).map (normalizationComparison l k D T K).hom

/-- The existing intrinsic proper/open refinement restricted through the recorded
bounded constructible inclusions and their specifying compatibility isomorphisms.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: lem-pur-condensed-exceptional-reconstruction). -/
def condensedRefinement {c d : Compactification f} (r : c.Refinement d) :
    CondensedRing.boundedConstructibleLowerShriekOfCompactification
        (Profinite.padicAlgClRingObj l) l (f := X.map Y f) d ⟶
      CondensedRing.boundedConstructibleLowerShriekOfCompactification
        (Profinite.padicAlgClRingObj l) l (f := X.map Y f) c :=
  ((ObjectProperty.fullyFaithfulι (boundedConstructible
    (condensedRingObj (Profinite.padicAlgClRingObj l) Y.scheme))).whiskeringRight
      (Omega l X.scheme)).preimage
    ((CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility
      (Profinite.padicAlgClRingObj l) l (f := X.map Y f) d).hom ≫
      fieldRefinement (Profinite.padicAlgClRingObj l) r ≫
        (CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility
          (Profinite.padicAlgClRingObj l) l (f := X.map Y f) c).inv)

/-- The canonical counit mate of the actual compact-support refinement, for the
exact chosen right adjoints attached to the two compactifications.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: lem-pur-condensed-exceptional-reconstruction). -/
def exceptionalRefinement {c d : Compactification f} (r : c.Refinement d) :=
  conjugateEquiv
    (CondensedRing.boundedConstructibleUpperShriekOfCompactificationAdjunction
      (Profinite.padicAlgClRingObj l) l (f := X.map Y f) c)
    (CondensedRing.boundedConstructibleUpperShriekOfCompactificationAdjunction
      (Profinite.padicAlgClRingObj l) l (f := X.map Y f) d)
    (condensedRefinement l k r)

/-- The actual whole-system and condensed mate equations for a compactification refinement.
Source: current blueprint sk-prop-sp-unique-adjoint-categorical, ordinary mate pasting.
(blueprint: lem-pur-condensed-exceptional-reconstruction). -/
def RefinementCompatibility
    (X Y : Base k) (f : X.scheme ⟶ Y.scheme) [f.IsOver (Spec (.of k))]
    (c d : Compactification f) (r : c.Refinement d)
    (Pc : Context l k X Y f c) (Pd : Context l k X Y f d)
    (Ac : RealizationAt l (Field.{u} l) k D Pc.reduction X Y f c)
    (Ad : RealizationAt l (Field.{u} l) k D Pd.reduction X Y f d)
    (qc : AtCompactification l k D Pc Ac) (qd : AtCompactification l k D Pd Ad)
    (v : Datum l k Pc) (w : Datum l k Pd)
    (hv : v.Admissible l k) (hw : w.Admissible l k) (b : v.L ≅ w.L) : Prop :=
    ∃ a : Pc.source.sequence.derived.functor.obj v.tower ≅
        Pd.source.sequence.derived.functor.obj w.tower,
      (systemRefinement l (Field.{u} l) k X Y f r).app _ ≫
          v.sequenceCounit l k (qc.result v hv).theta
            (qc.result v hv).originUnit
            (qc.result v hv).originSupport ≫
          ((Pc.reduction Y.scheme).adjunction.leftAdjointUniq
            (Pd.reduction Y.scheme).adjunction).hom.app
              ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj v.L.obj) ≫
          (Pd.reduction Y.scheme).reduction.map
            ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.map b.hom.hom) =
        (systemSupport l (Field.{u} l) d).map a.hom ≫
          w.sequenceCounit l k (qd.result w hw).theta
            (qd.result w hw).originUnit
            (qd.result w hw).originSupport ∧
      (Conclusion.iso l k D (qc.result v hv)).hom ≫
          (exceptionalRefinement l k r).app ((realization l k D Y).obj v.L) ≫
          (CondensedRing.boundedConstructibleUpperShriekOfCompactification
            (Profinite.padicAlgClRingObj l) l (f := X.map Y f) d).map
              ((realization l k D Y).map b.hom) =
        (realization l k D X).map
          ((ObjectProperty.homMk ((purCoefficientModel l (Field.{u} l) X.scheme).inverse.map
            ((coefficientSequenceLimit l (Field.{u} l) X.scheme).map a.hom))) :
              v.integral l k hv.reconstructs ⟶ w.integral l k hw.reconstructs) ≫
          (Conclusion.iso l k D (qd.result w hw)).hom

/-- The supplied compact-support realization, transported only along equality of
its supplied reduction package. No new comparison isomorphism is chosen.
Source: blueprint sk-prop-sp-integral-adjunction, specified reconstruction counit.
(blueprint: lem-pur-condensed-exceptional-reconstruction). -/
def specifiedSupport (C : CompactSupportCondensedRealization.ComparisonFamily l k)
    (P : Context l k X Y f c)
    (h : P.reduction = (C.coefficient (Field.{u} l)).reduction) :
    RealizationAt l (Field.{u} l) k (C.coefficient (Field.{u} l)).realization
      P.reduction X Y f c :=
  h.symm ▸ (C.coefficient (Field.{u} l)).atCompactification X Y f c

/-- All reconstruction comparisons, together with unit/shift compatibility and
compactification refinement compatibility. The refinement system map is specified by
the actual reconstructed tower counit square, and its condensed comparison is the
ordinary adjunction mate of the intrinsic proper/open refinement.
Source: current blueprint sk-prop-sp-integral-adjunction, sk-prop-sp-rational,
sk-thm-sp-qbar and sk-prop-sp-unique-adjoint-categorical.
(blueprint: lem-pur-condensed-exceptional-reconstruction). -/
structure Family
    (C : CompactSupportCondensedRealization.ComparisonFamily l k)
    (context : ∀ (X Y : Base k) (f : X.scheme ⟶ Y.scheme)
      [f.IsOver (Spec (.of k))] (c : Compactification f), Context l k X Y f c)
    (hcontext : ∀ (X Y : Base k) (f : X.scheme ⟶ Y.scheme)
      [f.IsOver (Spec (.of k))] (c : Compactification f),
      (context X Y f c).reduction = (C.coefficient (Field.{u} l)).reduction) where
  properties : RealizationProperties l k (C.coefficient (Field.{u} l)).realization
  comparison : ∀ (X Y : Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c : Compactification f),
      AtCompactification l k (C.coefficient (Field.{u} l)).realization (context X Y f c)
        (specifiedSupport l k C (context X Y f c) (hcontext X Y f c))
  refinement : ∀ (X Y : Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] (c d : Compactification f) (r : c.Refinement d)
    (v : Datum l k (context X Y f c)) (w : Datum l k (context X Y f d))
    (hv : v.Admissible l k) (hw : w.Admissible l k) (b : v.L ≅ w.L),
    RefinementCompatibility l k (C.coefficient (Field.{u} l)).realization X Y f c d r
      (context X Y f c) (context X Y f d)
      (specifiedSupport l k C (context X Y f c) (hcontext X Y f c))
      (specifiedSupport l k C (context X Y f d) (hcontext X Y f d))
      (comparison X Y f c) (comparison X Y f d) v w hv hw b
```

## New

The same declaration block, with only blueprint ownership tags updated, lives in
Sheaf.Paper.CondensedExceptionalReconstructionData and is reexported by the item.
Its old public imports remain public through the data module. The theorem signature is
unchanged. The additional records are:

```lean
/-- The system identification and its bounded-site and reconstruction properties, before
passing to any condensed representing object.
Source: blueprint sk-prop-sp-integral-adjunction, tower reconstruction and counit paragraph.
(blueprint: def-pur-condensed-exceptional-reconstruction-data). -/
structure SystemIdentification (d : Datum l k P) (h : d.Admissible l k) where
  theta : d.tower ≅ brownTower l k P d.L
  supplied : h.alternative.Uses l k theta
  brownBound : ∃ a : ℤ, (brownTower l k P d.L).IsGE a
  levels : ∀ n : ℕ,
    (P.source.proEtaleEvaluation.evaluation n).map theta.hom = (d.toBrown l k n).hom
  reduction : IsIso ((P.reduction Y.scheme).adjunction.unit.app
    ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj d.L.obj))
  originUnit : IsIso (P.source.derived.system.adjunction.unit.app
    (P.brown.right.obj ((input l k P).obj d.L)))
  originSupport : IsIso ((exceptionalSystemOriginComparison P.comparison).app d.tower)

/-- Recognition of the supplied systems, with the shifted-heart uniqueness statement.
There is no condensed adjoint or realization comparison in this record.
Source: blueprint sk-prop-sp-integral-adjunction, tower reconstruction and naturality.
(blueprint: def-pur-condensed-exceptional-reconstruction-data). -/
structure SystemRecognition (P : Context l k X Y f c) where
  result : ∀ (d : Datum l k P) (h : d.Admissible l k), SystemIdentification l k d h
  singleDegree : ∀ (d e : Datum l k P) (hd : d.Admissible l k) (he : e.Admissible l k)
    (r : ℤ) (b : d.L ⟶ e.L) (a : d.tower ⟶ e.tower),
    (∀ n : ℕ, ((P.source.proEtaleEvaluation.evaluation n).obj d.tower).IsGE r ∧
      ((P.source.proEtaleEvaluation.evaluation n).obj d.tower).IsLE r ∧
      ((P.source.proEtaleEvaluation.evaluation n).obj e.tower).IsGE r ∧
      ((P.source.proEtaleEvaluation.evaluation n).obj e.tower).IsLE r) →
    (∀ n : ℕ, (P.source.proEtaleEvaluation.evaluation n).map a ≫
        (e.toBrown l k n).hom = (d.toBrown l k n).hom ≫
          (P.source.proEtaleEvaluation.evaluation n).map
            (P.source.derived.system.inverse.map (P.brown.right.map ((input l k P).map b)))) →
    d.SystemMap l k b a (result d hd).theta (result e he).theta
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedExceptionalReconstruction | Q3 | Publicly reexports the data; assembles its theorem from four proof obligations. |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | Q3 new | Uses the system records. |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | Q3 new | Uses raw counits and system identifications. |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | Q3 new | Uses the regular coefficient and normalization definitions. |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | Q3 new | Uses the raw refinement and specified coherent support comparisons. |

`tools/downstream.py Sheaf.Paper.CondensedExceptionalReconstruction --names` returned
no existing Lean importers. The parent DAG route remains in force. No target meaning,
existing declaration signature, definition body, or visibility changes. No forced
adaptation of another group's module occurs.

## Status

landed 20261025T202804-L-2752468 2026-10-25 (merge of deliver/Q3/Sheaf.Paper.CondensedExceptionalReconstruction)
