# pathScalarStalk and fibre path interfaces

## Reason

Move the sixteen existing stalk/comparison/record declarations into a lower interface
module so the finite, inverse-limit, rational and algebraic constructions can import the
interfaces without importing the theorem they prove. The original module publicly imports
this interface, preserving its public declarations for every consumer. This is a logical
interface separation for the proof dependencies, not a split of a slow proof.

The definitions pathScalarStalk, pathIntegralScalarLevelIso and the seven large scalar
and evaluation predicates are irreducible with explicit types and proved API lemmas;
record size/injectivity derivation is locally disabled. These changes prevent Lean from
repeatedly unfolding large stalk and scalar expressions while checking the new proofs.
Their data, propositions and the target theorem signature retain their original meanings.

## Old

```lean
def pathScalarStalk {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) {R S : Type (u + 1)} [Ring R] [Ring S] (f : R →+* S)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  letI := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
  ((pointSmallEtale y).ulift.{u + 1}.presheafFiberCompIso
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).symm.app F.obj ≪≫
      ((pointSmallEtale y).ulift.{u + 1}.presheafToSheafCompSheafFiberIso
        (ModuleCat.{u + 1} S)).symm.app
          (F.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} f)
```

The interfaces and fibre_functor_basepoint_transport were declared in
Sheaf.Paper.FibreFunctorBasepointTransport.

## New

```lean
@[irreducible]
def pathScalarStalk {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) {R S : Type (u + 1)} [Ring R] [Ring S] (f : R →+* S)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} f).obj
      (((pointSmallEtale y).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F) ≅
      ((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} S)).obj
        ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f).obj F) :=
  letI := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} f).isLeftAdjoint
  ((pointSmallEtale y).ulift.{u + 1}.presheafFiberCompIso
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).symm.app F.obj ≪≫
      ((pointSmallEtale y).ulift.{u + 1}.presheafToSheafCompSheafFiberIso
        (ModuleCat.{u + 1} S)).symm.app
          (F.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} f)
```

The sixteen interface declarations are in that publicly imported module, with the same
names, binders and data/proposition fields. The original theorem remains in its original
module, with its exact original signature. The interface node is
new-e5-fibre-path-transport-data; the original node now attaches only the theorem.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FibreFunctorBasepointTransport | E5 | Imports its interfaces publicly and the proved construction modules privately. |
| Sheaf.Paper.EtaleWeilFundamentalRepresentation | unclaimed | DAG parent; no current Lean use of the relocated interfaces. Its separate fibre API is unchanged. |

New construction modules depend directly on the lower interface. All existing target
statements and record conditions are preserved. The separate algebraic-functor repair
is documented in E5-canonical-algebraic-fibre-functor.md and reopens its semantic review.

## Status

landed 20261020T230733-L-606316 2026-10-20 (merge of deliver/E5/Sheaf.Paper.FibreFunctorBasepointTransport)
