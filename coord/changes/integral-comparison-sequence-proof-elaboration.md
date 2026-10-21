# Proof elaboration and continuity instances for integral comparison systems

## Reason

Prove the seven existing obligations without repeatedly unfolding chosen left adjoints,
localized functors, scalar models, and tensor sections. Composition of direct images
also requires continuity of the composite base-change functors. The stage-3 syntactic
visibility check requires this record for the added attribute commands and instances.

## Old

All existing declaration signatures, definitions, and public imports are preserved
verbatim. The three private continuity instances below did not previously exist.
There were no local irreducibility commands for the definitions listed below.

## New

The proof adds these proved private continuity instances. Their instance attributes
are registered, but their names are private; their propositions assert continuity
already supplied by composition of the existing continuous base changes.

```lean
private instance sequenceBaseCompContinuous {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ k ⋙
      MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).IsContinuous
      (ProEt.topology V) (ProEt.topology Z) := by
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ k).IsContinuous
      (ProEt.topology V) (ProEt.topology W) := proEtaleBaseChange_isContinuous k
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).IsContinuous
      (ProEt.topology W) (ProEt.topology Z) := proEtaleBaseChange_isContinuous h
  exact Functor.isContinuous_comp _ _ _ (ProEt.topology W) _
```

```lean
private instance sequenceBaseCompContinuous' {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    (proEtaleBaseChange k ⋙ proEtaleBaseChange h).IsContinuous
      (ProEt.topology V) (ProEt.topology Z) := sequenceBaseCompContinuous h k
```

```lean
private instance sequenceSystemCompContinuous {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    (integralComparisonSequenceBaseChange k ⋙
      integralComparisonSequenceBaseChange h).IsContinuous
        (coefficientSequenceTopology (ProEt.topology V))
        (coefficientSequenceTopology (ProEt.topology Z)) :=
  Functor.isContinuous_comp _ _ _ (coefficientSequenceTopology (ProEt.topology W)) _
```

The following commands affect elaboration only within this module; they do not
change the definitions or any theorem statement:

```lean
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] integralComparisonSequenceScalarModel
attribute [local irreducible] integralComparisonSequenceTensorSection
attribute [local irreducible] sequenceScalarPullbackRight
open scoped ChangeOfRings
```

## Users

`tools/downstream.py Sheaf.Paper.IntegralComparisonSequenceSystems --uses
sequenceBaseCompContinuous sequenceSystemCompContinuous` found 572 downstream
modules and zero references to either new helper name in the shared source. The
prime-suffixed instance is also new and private. No existing signature or definition data changes, so none of those consumers needs
adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralComparisonSequenceSystems | K5 | Uses the three proved continuity instances and local elaboration attributes in its proofs. |

No external consumer of these private helper declarations exists. There is no forced
adaptation and no change to a target statement or to data in a target definition.
The three new proved public modules are described by their new DAG nodes and report.

## Status

landed 20261021T214821-L-1860875 2026-10-21 (merge of deliver/K5/Sheaf.Paper.IntegralComparisonSequenceSystems)
