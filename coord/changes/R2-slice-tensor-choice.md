# Canonical slice tensor choice and native comparison aliases

## Reason

The original ordinary choice retains the source tensor theorem's entire existential
predicate: units, coherence, acyclicity and flatness, as well as pure tensors and
sum totals. Repeated comparisons of these concrete tensor endpoint types exceeded
the compiler's 60-second limit once the item was proved.

The proved generic `sectionTensorWitness` projects
`internal_section_tensor_comparison` onto its ordinary witness, pure-tensor formula
and total-comparison clause. `sectionOrdinaryTensorIso` chooses from this smaller
predicate before specializing to the actual slice. Pure tensors locally generate
relative tensor sheaves, so that formula determines the ordinary isomorphisms.
The total summand formula determines each complex isomorphism by the coproduct
universal property. These are choices of uniquely normalized data; no arbitrary
witness of an unproved mere existence statement is used.

The two choice aliases infer their original mathematical endpoint types.
Named, fully proved graded-tensor existence and compatibility statements are local
instances; they share proof arguments in the native constructions. The original
native tensor, closed, localization, evaluation and restriction aliases retain their
bodies and explicit types. All original theorem signatures are retained.

The private `nativeMonoidal_eq_localization` proves reflexivity over an abstract
category. The sole consumer repeats this abstract argument privately in `internalMonoidal_eq_localization`, where
its original concrete reflexivity proof timed out. The consumer's signature and
main theorem are unchanged. It is unclaimed; this is not an adaptation of a held
module. The consumer's existing main proof hole is retained.

The unused public import `Sheaf.Paper.InternalSectionDerivedTensorComparison` is
removed from this item. The sole downstream consumer already imports it directly.
The public normalization, graded-tensor and abstract equality helpers are components
of this existing definition node; no additional mathematical obligation is introduced.

## Old

```lean
def sliceOrdinaryTensorIso (M N : SliceInternal Λ X U) :
    (sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U)).functor.obj (M ⊗ N) ≅
    (sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U)).functor.obj M ⊗
    (sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U)).functor.obj N :=
  (internal_section_tensor_comparison ((Scheme.ProEt.topology X).over U)
    (sliceRingObject Λ X U)).2.choose M N

def sliceRawComplexTensorIso (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    ((sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
      (sliceRingObject Λ X U)).functor.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q (curriedTensor (SliceInternal Λ X U))) ≅
    CochainComplex.mapBifunctor
      (((sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
        (sliceRingObject Λ X U)).functor.mapHomologicalComplex (.up ℤ)).obj P)
      (((sectionModuleEquivalence ((Scheme.ProEt.topology X).over U)
        (sliceRingObject Λ X U)).functor.mapHomologicalComplex (.up ℤ)).obj Q)
      (curriedTensor _) :=
  (sliceRawComplexTensorComparison Λ X U P Q).choose
```

## New

```lean
def sliceOrdinaryTensorIso (M N : SliceInternal Λ X U) :=
  sectionOrdinaryTensorIso ((Scheme.ProEt.topology X).over U) (sliceRingObject Λ X U) M N

def sliceRawComplexTensorIso (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :=
  (sliceRawComplexTensorComparison Λ X U P Q).choose
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.InternalSliceDerivedHomComparison | R2 | Canonical choices factored and five holes closed. |
| Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison | unclaimed | Concrete monoidal equality uses the abstract equality; existing main hole retained. |

`tools/downstream.py --uses` reports only the item itself for the ordinary, raw
and transported total comparison names. The sole transitive consumer is listed
above. Its existing comparison predicates still impose the same pure-tensor,
summand, evaluation and restriction equations. Target signatures are untouched;
semantic review of the equivalent choice presentation is requested in the normal
definition-change review.

## Status

landed 20261020T221320-L-4173249 2026-10-20 (merge of deliver/R2/Sheaf.Paper.InternalSliceDerivedHomComparison)
