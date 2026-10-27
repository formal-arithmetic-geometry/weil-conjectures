# CorePackage: shifts of the specified coefficient comparisons

## Reason

STATEMENT-DISPUTED (repaired): the former `CorePackage.coefficientShifts` field
quantified over **every** `Change`, including tensor comparisons with no shift
compatibility. `Change` requires exact coefficient functors and exceptional
comparisons, but imposes no shift condition on `tensorX` or `tensorY`.

Take the identity morphism of the geometric point over an algebraic closure of
F_2, l=3, E=Q_3, and coefficient level n=1. Its finite-Tor category is
D^b of finite-dimensional F_3-vector spaces. Semisimplicity identifies it with
finite graded vector spaces. Let epsilon_V act by (-1)^j on H^j(V); this is a
natural automorphism of the identity functor. Keep the identity coefficient
functors, the usual shift structures, identity exceptional comparison and
identity pull comparison. Set both tensor comparisons at (P,Q) equal to
epsilon_(P tensor Q). Since f is the identity, the projection equation is the
same tensor comparison on its two sides, so this is a `Change`.

With M the tensor unit in degree zero, the evaluation-transposed Hom comparison
is epsilon_N. But epsilon_(N[1]) = -epsilon_N[1]. At N=F_3 the two sides differ,
so this comparison fails the second Hom shift square. Finite `RingShifts` pins
the Hom shift structures to the actual derived ones; choosing different shift
structures in `Conclusion` cannot remove this counterexample.

The current blueprint requires the specified finite reduction and scalar
extension maps to respect shifts. It does not quantify over arbitrary tensor
natural isomorphisms. The correction attaches `ChangeShifts` evidence to each
of the four actual coefficient witnesses (`ringScalar`, `rationalization`,
`rationalScalar`, `common`), including every allowed reduction/composite in
`Allowed`. The same witness still satisfies its existing exceptional
normalization and invertibility clauses. No canonical coefficient shift claim
is discarded, and no new assumption is put on `tensor_adjunction`.

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-package/fix-lem-tensor-adjunction.md and its proof, coefficient and
shift clauses. This is a correction of the Lean definition to the unchanged
mathematical statement; the node's TeX already states the source correctly.

## Old

```lean
  ringScalar {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) (ha : Allowed l a) :
    ∃ b : Change l Ω (stage (s.stage l)) (stage (t.stage l))
        (S.ring.scalar a ha true).functor (S.ring.scalar a ha false).functor,
      b.exceptional = ⟨S.ring.comparison c a ha⟩
  rationalization (E : FieldStage.{u} l) :
    ∃ b : Change l Ω (stage (.integral E)) (stage (.rational E))
        (ConstructibleExceptionalCoefficients.rationalization l Ω E X)
        (ConstructibleExceptionalCoefficients.rationalization l Ω E Y),
      b.exceptional = S.fields.rationalizationComparison c E ∧
      (∀ M N : C.{u} l Ω X (.integral E), IsIso (b.homX l Ω M N)) ∧
      (∀ M N : C.{u} l Ω Y (.integral E), IsIso (b.homY l Ω M N)) ∧
      (∀ M : C.{u} l Ω X (.integral E), IsIso (b.star l Ω M))
  rationalScalar (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    ∃ b : Change l Ω (stage (.rational E)) (stage (.rational L))
        (ConstructibleExceptionalCoefficients.rationalScalar l Ω E L i X)
        (ConstructibleExceptionalCoefficients.rationalScalar l Ω E L i Y),
      b.exceptional = S.fields.rationalComparison c E L i ∧
      (∀ M N : C.{u} l Ω X (.rational E), IsIso (b.homX l Ω M N)) ∧
      (∀ M N : C.{u} l Ω Y (.rational E), IsIso (b.homY l Ω M N)) ∧
      (∀ M : C.{u} l Ω X (.rational E), IsIso (b.star l Ω M))
  common (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    ∃ b : Change l Ω (stage (.rational (commonField l Ω i))) (stage .closed)
        (commonInclusion l Ω X i) (commonInclusion l Ω Y i),
      b.exceptional = S.common.commonComparison c i ∧
      (∀ M N : C.{u} l Ω X (.rational (commonField l Ω i)), IsIso (b.homX l Ω M N)) ∧
      (∀ M N : C.{u} l Ω Y (.rational (commonField l Ω i)), IsIso (b.homY l Ω M N)) ∧
      (∀ M : C.{u} l Ω X (.rational (commonField l Ω i)), IsIso (b.star l Ω M))
  coefficientShifts {s t : Stage.{u} l}
      (hs : Admissible l Ω D f c s) (ht : Admissible l Ω D f c t)
      {TX : C.{u} l Ω X s ⥤ C.{u} l Ω X t} {TY : C.{u} l Ω Y s ⥤ C.{u} l Ω Y t}
      (a : Change l Ω (stage s) (stage t) TX TY) :
    Nonempty (ChangeShifts l Ω (conclusion s hs) (conclusion t ht) a)

```

## New

```lean
structure CoefficientComparisons
    (stage : ∀ s : Stage.{u} l, Model l Ω s (S.ring.operation c s))
    (conclusion : ∀ (s : Stage.{u} l) (_h : Admissible l Ω D f c s),
      Conclusion l Ω (stage s)) where
  ringScalar {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) (ha : Allowed l a) :
    ∃ b : Change l Ω (stage (s.stage l)) (stage (t.stage l))
        (S.ring.scalar a ha true).functor (S.ring.scalar a ha false).functor,
      b.exceptional = ⟨S.ring.comparison c a ha⟩ ∧
      ∀ (hs : Admissible l Ω D f c (s.stage l))
        (ht : Admissible l Ω D f c (t.stage l)),
        b.ShiftCompatible l Ω (conclusion (s.stage l) hs) (conclusion (t.stage l) ht)
  rationalization (E : FieldStage.{u} l) :
    ∃ b : Change l Ω (stage (.integral E)) (stage (.rational E))
        (ConstructibleExceptionalCoefficients.rationalization l Ω E X)
        (ConstructibleExceptionalCoefficients.rationalization l Ω E Y),
      b.exceptional = S.fields.rationalizationComparison c E ∧
      (∀ M N : C.{u} l Ω X (.integral E), IsIso (b.homX l Ω M N)) ∧
      (∀ M N : C.{u} l Ω Y (.integral E), IsIso (b.homY l Ω M N)) ∧
      (∀ M : C.{u} l Ω X (.integral E), IsIso (b.star l Ω M)) ∧
      ∀ (hs : Admissible l Ω D f c (.integral E))
        (ht : Admissible l Ω D f c (.rational E)),
        b.ShiftCompatible l Ω (conclusion (.integral E) hs) (conclusion (.rational E) ht)
  rationalScalar (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    ∃ b : Change l Ω (stage (.rational E)) (stage (.rational L))
        (ConstructibleExceptionalCoefficients.rationalScalar l Ω E L i X)
        (ConstructibleExceptionalCoefficients.rationalScalar l Ω E L i Y),
      b.exceptional = S.fields.rationalComparison c E L i ∧
      (∀ M N : C.{u} l Ω X (.rational E), IsIso (b.homX l Ω M N)) ∧
      (∀ M N : C.{u} l Ω Y (.rational E), IsIso (b.homY l Ω M N)) ∧
      (∀ M : C.{u} l Ω X (.rational E), IsIso (b.star l Ω M)) ∧
      ∀ (hs : Admissible l Ω D f c (.rational E))
        (ht : Admissible l Ω D f c (.rational L)),
        b.ShiftCompatible l Ω (conclusion (.rational E) hs) (conclusion (.rational L) ht)
  common (i : AlgebraicallyClosedCoefficients.Index l Ω) :
    ∃ b : Change l Ω (stage (.rational (commonField l Ω i))) (stage .closed)
        (commonInclusion l Ω X i) (commonInclusion l Ω Y i),
      b.exceptional = S.common.commonComparison c i ∧
      (∀ M N : C.{u} l Ω X (.rational (commonField l Ω i)), IsIso (b.homX l Ω M N)) ∧
      (∀ M N : C.{u} l Ω Y (.rational (commonField l Ω i)), IsIso (b.homY l Ω M N)) ∧
      (∀ M : C.{u} l Ω X (.rational (commonField l Ω i)), IsIso (b.star l Ω M)) ∧
      ∀ (hs : Admissible l Ω D f c (.rational (commonField l Ω i)))
        (ht : Admissible l Ω D f c .closed),
        b.ShiftCompatible l Ω (conclusion (.rational (commonField l Ω i)) hs)
          (conclusion .closed ht)

-- The revised CorePackage field:
  coefficients : CoefficientComparisons l Ω D hl f S c stage conclusion
```

`Change.ShiftCompatible a cs ct` is exactly
`Nonempty (ChangeShifts l Ω cs ct a)`; it packages no extra data and has no hole.
The independent CoefficientComparisons record avoids the type-checking blow-up
from embedding these dependent existential witnesses in CorePackage.
Explicit existing universe arguments are supplied for C, Operation, System and
FieldComparison; their mathematical types are unchanged. The old common-stage
homogeneous normalization equality is preserved.

## Users

`python3 tools/downstream.py Sheaf.Paper.TensorAdjunctionExchange --uses CorePackage`
reports zero downstream modules and only the defining module as a textual user.
A scan of lean/Sheaf, lean/WeilConjectures and quarantine found no external user
of coefficientShifts, ChangeShifts or CorePackage needing an adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.TensorAdjunctionExchange | S1 | Correct CorePackage; Package uses its corrected coefficient witnesses. The theorem signature and proof hole stay. |

The six DAG citers retain their uses: lem-pod-global-duality-map-identification,
lem-sf-verdier-hom-chain-composition, lem-pod-structure-hom-chain-realization,
lem-trf-proper-direct-image-comparison,
lem-pod-verdier-composition-mate-normalization and
lem-pod-formal-verdier-exchange-equivariance. Each uses the canonical exchange
or its coefficient/shift compatibility; none needs arbitrary tensor comparisons.
The unit statement and five-arrow route are unchanged. Challenge.lean itself
is unchanged. Since this definition occurs below a target, its statement review
must be reopened for the corrected interpretation.

## Status

landed 20261025T123715-L-1891182 2026-10-25 (merge of deliver/S1/Sheaf.Paper.TensorAdjunctionExchange)
