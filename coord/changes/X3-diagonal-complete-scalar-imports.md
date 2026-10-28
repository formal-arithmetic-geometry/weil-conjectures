# Explicit-localization cores for the diagonal coefficient comparisons

## Reason

The existing complete-scalar-restriction proof is needed by diagonalTower_limit,
but its module publicly imports DiagonalTowerTracePresentations, which lies above
the limit theorem. The coefficient-transport proof has the same import. The proofs
only use the two derived-category localization instances for constant and completed
modules, so they can be reused without the trace localization bundle.

## Old

Both modules publicly imported DiagonalTowerTracePresentations and stated the
following theorems using the unchanged DiagonalTraceLocalizations class.

```lean
theorem diagonalCompletionCoefficientTransport (l : ℕ) [Fact l.Prime] (S : Scheme.{u})
    [DiagonalTraceLocalizations l S] :
    let J := Scheme.proEtaleModelTopology S
    let A := ULift.{u + 1} ℤ_[l]
    let I : Ideal A := Ideal.span {(l : A)}
    ∃ (EB : DerivedCategory (DiagonalCompleted l S) ≌
          ConstantCompletion.D (ConstantCompletion.completed J A I))
      (ER : DerivedCategory (DiagonalMod l S) ≌
          ConstantCompletion.D (ConstantCompletion.constant J A)),
      ER.functor.Additive ∧ ER.inverse.Additive ∧
      Nonempty (diagonalCompletedUnderlying l S ⋙ ER.functor ≅
        EB.functor ⋙ ConstantCompletion.dres (ConstantCompletion.coefficientMap J A I))
```

```lean
theorem diagonalCompleteScalarRestriction (l : ℕ) [Fact l.Prime] (S : Scheme.{u})
    [DiagonalTraceLocalizations l S] :
    let F := diagonalCompletedUnderlying l S
    let P : ObjectProperty (DerivedCategory (DiagonalCompleted l S)) := fun M ↦
      ∀ V : DerivedCategory (DiagonalMod l S),
        IsIso (l • 𝟙 V) → Subsingleton (V ⟶ F.obj M)
    Nonempty (P.ι ⋙ F).FullyFaithful
```


## New

Add DiagonalCompletionCoefficientTransportCore and DiagonalCompleteScalarRestrictionCore.
Each contains the existing proof with a new theorem name ending in Core and the
two explicit HasDerivedCategory instances for DiagonalMod and DiagonalCompleted,
in place of the bundle. Private helpers remain private; the scalar proof calls
the transport core. Their statements need only DiagonalTowerLimitInterface.

The existing modules are restored verbatim from their current quarantine archives,
including their complete original proofs, theorem names, signatures, universes,
visibility and public imports. The original nodes are preserved verbatim.
The localization class, fields, instance attributes and original defining module
are unchanged. There are no source-library changes. The old nodes retain their
Lean attachments and proofs; new nodes own the separately usable core proofs.

## Users

X3 claimed both quarantined comparison modules for this repair. No consumer
source is adapted; the comparison modules are exact archive restorations.
The direct importers are DiagonalCompleteScalarRestriction (restored here),
DiagonalTraceCompletedHomBijection and DiagonalCompletedChernLift (both unclaimed).
Their public interfaces remain identical; direct-consumer compile results appear
in report.md. All unchanged validation copies are removed before delivery.

## Returned delivery repair

Reviewer C-9ce8f passed delivery 9ce8fbdb6ff, but landing was refused after the
comparison modules were quarantined by the upstream-import red build. Both rework
items are now claimed by X3. Both full archived modules and their current nodes
are restored, preserving the original proofs rather than the previous wrappers.
The new core modules remain the independent route used below the limit theorem.
No quarantine archive is deleted. The delivery tool rebases the packet onto the
current sheaf-dag and performs the server compile and preflight before pushing.

## Compile-budget repair

The final packet also names the generic finite heterogeneous-equation predicate
and gives the new finite normalization helpers their coefficient derived-category
instance and finite coefficient Ext instance explicitly. These are new declarations of this delivery. Their actual
objects and equations stay identical. A subsequent delivery check exceeded the
file budget in strict normalization. The packet now also separates strict witness
recovery from finite-equation conversion, using explicit named strict specifications
and a proved generic finite-predicate map. These are all new declarations of this
delivery, with no additional holes. The new full server check covers every caller. A profiled check of the assigned module found the remaining expensive kernel
check in its final combination. This already proved combination is separately
checked in DiagonalLimitTypedAssembly; the assigned theorem applies specification
compatibility to it. No existing shared interface or target signature changes.
The final 18-module check passed below 60 seconds per file; finite input and
conversion took 44.6 and 40.2 seconds, and the assigned module took 31.9 seconds.

## Status

landed 20261028T035013-L-3579330 2026-10-28 (merge of deliver/X3/Sheaf.Paper.DiagonalTowerLimit)
consumers. The item is a decomposition into two strictly smaller obligations; no global hole-count reduction or module withdrawal is claimed.
