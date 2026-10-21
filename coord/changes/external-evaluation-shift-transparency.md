# CategoryTheory.ExternalEvaluation tensor and coefficient shift comparisons

## Reason

The assembled proof exceeded the 60-second single-file compilation limit.
The three complex/functor aliases and four shift comparisons were reducible
abbreviations for large Mathlib structures. Use ordinary definitions with the same explicit
isomorphism types, and prove their component formulas in private lemmas.
This controls unfolding during elaboration. Proof-local irreducibility settings
keep the constant functor, section formulas and pairing constructions behind
their proved component lemmas after those lemmas are established. The three complex/functor definitions
are `instance_reducible`; the two functors have explicit shift-commuting instances.
`underlyingCommShift` is public because the original public theorem's shift
comparison uses this instance. It is exactly the mapHomologicalComplex instance,
constructed by unfolding `underlying` and `infer_instance`. `complexHasTensor` and `coefficientHasTensor` expose the existing coproduct
existence instances for these two categories, so public tensor definitions need
no private helper. Their types are propositions and their proofs are direct
instance synthesis. Every construction term and every
public declaration type is unchanged; the old and new constructions are
judgmentally equal. No target statement changes meaning.

## Old

```lean
abbrev constantComplex :=
  (commutativeSiteConstantModuleFunctor S A).mapHomologicalComplex (.up ℤ)

abbrev underlying (R : Type w) [CommRing R] :=
  (forget₂ (ModuleCat.{w} R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)

abbrev tensorComplex (P Q : Complex S A) :=
  CochainComplex.mapBifunctor P Q (curriedTensor (Modules S A))

abbrev tensorShift₁ (E H : Complex S A) (a : ℤ) :
    tensorComplex S A (E⟦a⟧) H ≅ (tensorComplex S A E H)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₁Iso E H (curriedTensor (Modules S A)) a

abbrev tensorShift₂ (E H : Complex S A) (a : ℤ) :
    tensorComplex S A E (H⟦a⟧) ≅ (tensorComplex S A E H)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₂Iso E H (curriedTensor (Modules S A)) a

abbrev coefficientShift₁ (R : Type w) [CommRing R] (U V : Coeff R) (a : ℤ) :
    (U⟦a⟧ ⊗ V) ≅ (U ⊗ V)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₁Iso U V (curriedTensor (ModuleCat.{w} R)) a

abbrev coefficientShift₂ (R : Type w) [CommRing R] (U V : Coeff R) (a : ℤ) :
    (U ⊗ V⟦a⟧) ≅ (U ⊗ V)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₂Iso U V (curriedTensor (ModuleCat.{w} R)) a
```

## New

```lean
@[instance_reducible]
def constantComplex : Coeff A ⥤ Complex S A :=
  (commutativeSiteConstantModuleFunctor S A).mapHomologicalComplex (.up ℤ)

@[instance_reducible]
def underlying (R : Type w) [CommRing R] : Coeff R ⥤ CochainComplex AddCommGrpCat ℤ :=
  (forget₂ (ModuleCat.{w} R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)

@[instance_reducible]
def tensorComplex (P Q : Complex S A) : Complex S A :=
  CochainComplex.mapBifunctor P Q (curriedTensor (Modules S A))

def tensorShift₁ (E H : Complex S A) (a : ℤ) :
    tensorComplex S A (E⟦a⟧) H ≅ (tensorComplex S A E H)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₁Iso E H (curriedTensor (Modules S A)) a

def tensorShift₂ (E H : Complex S A) (a : ℤ) :
    tensorComplex S A E (H⟦a⟧) ≅ (tensorComplex S A E H)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₂Iso E H (curriedTensor (Modules S A)) a

def coefficientShift₁ (R : Type w) [CommRing R] (U V : Coeff R) (a : ℤ) :
    (U⟦a⟧ ⊗ V) ≅ (U ⊗ V)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₁Iso U V (curriedTensor (ModuleCat.{w} R)) a

def coefficientShift₂ (R : Type w) [CommRing R] (U V : Coeff R) (a : ℤ) :
    (U ⊗ V⟦a⟧) ≅ (U ⊗ V)⟦a⟧ :=
  CochainComplex.mapBifunctorShift₂Iso U V (curriedTensor (ModuleCat.{w} R)) a
```

## Users

The required `tools/downstream.py ... --uses` check found zero downstream
modules. Its only declaration-name hits were in this item itself.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.ExternalEvaluationTwoShiftSquares | F3 | Same comparison constructions and types; private proofs use component formulas. |

The target closure may use this item through unfinished parents in the DAG.
Those parents receive exactly the same mathematical comparisons. No consumer
adaptation is necessary. This transparency change introduces no new theorem,
hypothesis, conclusion, construction choice, or proof obligation.

## Status

landed 20261021T203457-L-3778950 2026-10-21 (merge of deliver/F3/Sheaf.Algebra.Homology.ExternalEvaluationTwoShiftSquares)
