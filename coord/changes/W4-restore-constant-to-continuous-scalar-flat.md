# AlgebraicGeometry.ProEtale.FiniteConstantModel.constantToContinuous_preservesFiniteLimits

## Reason

The assigned coord/rework.tsv row records removal of the live module after a reverted
cluster restore. Restore the authoritative quarantined module at its original live path.
This repairs the missing source, with no new proof-hole closure claimed.

## Old

The live path lean/Sheaf/Paper/ConstantToContinuousScalarFlat.lean is absent.
The authoritative archive is quarantine/Sheaf/Paper/ConstantToContinuousScalarFlat.lean.
Its existing theorem signature is:

```lean
theorem constantToContinuous_preservesFiniteLimits
    (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    [IsCommMonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))]
    (φ : (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ Profinite.continuousCoefficientRingObj A)
    [IsMonHom φ]
    (hφ : ∀ (S : Profinite.{u}ᵒᵖ) (a : ULift.{u + 1} A),
      (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
        _ _ φ).app S) a = ULift.up (ContinuousMap.const S.unop a.down)) :
    PreservesFiniteLimits (Mod.extendScalars φ)
```

## New

Restore the module byte for byte from the archive, including the complete proof,
public imports, private proof imports, declaration docstring and local options.
The theorem signature above is unchanged. The construction lifts finite scalar
families locally, factors relations using PID flatness of continuous functions,
and transports flatness through the section-module equivalence and the
extension/forgetful tensor comparison.

The existing node lem-sfb-constant-to-continuous-scalar-flat keeps its Lean attachment,
statement, proof steps and all dependencies. No target semantics or definitions change.
No node edits or new nodes are needed.

## Users

The live-source downstream.py --uses check reports an unknown module because its live
source is absent. An exact scan of both lean/ and quarantine/ finds one direct importer
and one use of the restored theorem, in the quarantined consumer below. Scanning DAG
parents also confirms that lem-sfb-finite-constant-model-two-term-free-resolution still
needs this node in its proof. No consumer or parent is withdrawn or changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteConstantModelResolution | no holder in shared claim records | Quarantined consumer; unchanged archive compiles against restored item in sandbox overlay. |

The item compiles independently in 11.2 seconds. An overlay compile with an axiom probe
compiles the item in 13.3 seconds and the unchanged archived consumer in 11.5 seconds.
The theorem uses only propext, Classical.choice and Quot.sound. The temporary probe
and consumer copy are removed from the delivery; only the restored item is delivered.

## Status

landed 20261021T021033-L-2695539 2026-10-21 (merge of deliver/W4/Sheaf.Paper.ConstantToContinuousScalarFlat)
