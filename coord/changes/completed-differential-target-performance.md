# AlgebraicGeometry.completedDifferentialTarget

## Reason

The original `abbrev` exposed the full tensor-product carrier and caused the
completed Jacobian proof to exceed the single-file elaboration limit during
instance comparison. The definition is now a noncomputable named wrapper around
the identical tensor product, with the inherited additive and local-ring module
structures declared explicitly. This preserves the target's mathematical type
while giving elaboration a stable interface. The completion-module instance
now explicitly retains the existing scalar-action field instead of reducing the
entire pulled-back structure to recover it. Private application lemmas avoid unfolding the tensor and differential maps;
no proof or checking is skipped.

## Old

```lean
abbrev completedDifferentialTarget (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime] :=
  TensorProduct (completedLocalRing S p)
    (KaehlerDifferential k (completedLocalRing S p)) (completedRing S p)
```

## New

The declaration is in `@[expose] public noncomputable section`:

```lean
def completedDifferentialTarget (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime] :=
  TensorProduct (completedLocalRing S p)
    (KaehlerDifferential k (completedLocalRing S p)) (completedRing S p)
deriving SMul k, AddCommGroup, Module k, SMul (completedLocalRing S p),
  Module (completedLocalRing S p)
```

The completion-module instance uses the same tensor symmetry, with its domain
annotated by the named target and `smul` explicitly set to
`(completedDifferentialTargetSMul k S p).smul`. Its action and module laws are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.CompletedJacobianDifferentials | X5 | Uses the named wrapper and its explicit instances in the proof. |
| Sheaf.TraceFormula.CompletedConormalDeterminantComparison | unclaimed | Its statements use the target only through imported declarations; no source adaptation needed. |
| Sheaf.RingTheory.SeparableClosedPointFormalPresentation | unclaimed | Its statements use the target only through imported declarations; no source adaptation needed. |
| Sheaf.AlgebraicGeometry.FormalPlaneAdjunctionLattice | unclaimed | Its statements use the target only through imported declarations; no source adaptation needed. |

## Status

landed 20261024T191714-L-470873 2026-10-24 (merge of deliver/X5/Sheaf.TraceFormula.CompletedJacobianDifferentials)
