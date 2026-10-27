# CategoryTheory.StageSystem.coefficientPairFunctor

## Reason

The uniquely specified descended functor was obtained as a whole chosen witness.
Its object formula then required expanding the existence proof. Projection of an
unreduced input pair additionally expanded coefficient scalar-action data. Keep
the prescribed stagewise object construction literally in the functor record,
matching the pair before accessing its stage. The representative-object diagnostic
kernel check fell from 19.9 to 2.6 seconds when the pair is matched first.

## Old

```lean
def coefficientPairFunctorObject (P : S.PairCategory) : T.PairCategory :=
  ⟨P.stage, (φ P.stage).obj P.obj⟩

@[irreducible] def coefficientPairFunctor (hb : pairFunctorCoherent S T φ b) :=
  (coefficientPairFunctor_exists S T φ b hb).exists.choose
```

## New

```lean
def coefficientPairFunctorObject (P : S.PairCategory) : T.PairCategory :=
  match P with
  | ⟨i, X⟩ => ⟨i, (φ i).obj X⟩

@[irreducible] def coefficientPairFunctor (hb : pairFunctorCoherent S T φ b) :=
  ((coefficientPairFunctor_exists S T φ b hb).exists.choose).copyObj
    (coefficientPairFunctorObject S T φ)
    (fun P ↦ eqToIso ((coefficientPairFunctor_exists S T φ b hb).exists.choose_spec.1 P))
```

The new fully proved coefficientPairFunctorObject_eq gives the original projection
formula. The new public coefficientPairFunctor_eq_chosen proves equality of the
entire functor to the original body, via the proved private copyObj_eq_of_eq and
Functor.hext. Thus the original maps on all quotient arrows, not just its objects,
are preserved. The public coefficientPairFunctor_obj records the literal object
function. The existing existence/uniqueness theorem keeps its exact signature;
its object proof now destructs the pair, and the representative-map proof stays
HEq.rfl. Its unique-witness specification is unchanged. The construction uses
Functor.copyObj on the same uniquely determined functor, without another choice.

Add public import Mathlib.CategoryTheory.NatIso for the copyObj interface. All old
signatures, universes, attributes and public visibility are preserved. No sorry or
adopted-source change is added. Arbitrary arrows, nonidentity associators, and
repeated stages are covered by equality of the whole functor.

## Users

The use query finds only the definition module and AmbientCompleteCoefficientCategories.
This item additionally uses the explicit object construction in its new proof.
Both support modules were unclaimed on 2026-10-22.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.StageSystemFunctorDescent | unclaimed | use the explicit record object function and prove equality to the old whole functor |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | unclaimed | replace one private proof's delta coefficientPairFunctor by rw [coefficientPairFunctor_eq_chosen], retaining its uniqueness argument |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | M8 | compute the included representative object by the prescribed literal object function |

The original Ambient consumer fails at line 755: choose_spec describes the old
chosen witness, while the expected map formula belongs to the normalized copyObj
witness. This was reproduced by OriginalConsumerDiagnostic (exit 1, 6.5 seconds).
Rewriting by the proved whole-functor equality makes the original uniqueness proof
apply verbatim. No public declaration in that consumer is changed by this proof
adaptation. Final successful compilation is recorded in report.md.
This definition repair is submitted for independent target-meaning review.

## Status

landed 20261022T040208-L-2831428 2026-10-22 (merge of deliver/M8/Sheaf.Paper.QbarCoefficientSmoothBaseChange)
