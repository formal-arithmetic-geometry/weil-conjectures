## What changed

Filled the proof of `AlgebraicGeometry.affinePullbackModelComparisons_isIso`, preserving
its signature and both comparison definitions. Added proof-only imports of
`Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde`,
`Sheaf.AlgebraicGeometry.TensorPullbackTilde`, and
`Sheaf.AlgebraicGeometry.AffineTildeDerivedSectionsUnitIsIso`.

A proved private equality-transport helper keeps the additive instances in the
right-derived unit aligned when simplifying affine scalar restriction.

The proof follows the existing node's two steps. Generic module K-flatness supplies
the acyclic tensor criterion for `isKFlat_tilde`. The K-flat counit from
`exists_derivedPullback` is compared with the fixed composition counit using the
left-derived lift, its isomorphism criterion, and its factorization equation.
The localization transports then give the first comparison's invertibility.

Full faithfulness of Spec expresses the scheme map as a ring map. The natural
tensor-pullback/tilde isomorphism, applied to complexes, identifies the pullback
with the tilde of the scalar-extended complex. `affineTildeDerivedSectionsUnit_isIso`
and invariance of invertibility of natural-transformation components under object
isomorphisms give the right-derived unit's invertibility. The other three factors
of `affineModelSectionsComparison` are isomorphisms.

No boundedness, flatness of the ring map, nonzero ring, or nonzero complex is used.
The zero-ring and zero-complex cases are covered by the same functorial argument.
The unit's route is preserved; its realized statement and steps are empty in the
unit record, and the node's original two-step route is followed without pruning.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.affinePullbackModelComparisons_isIso`
(node `new-affine-pullback-model-comparisons-isIso`).

No holes added. No `sorry` remains in the delivered module. Existing dependency
lemmas are used as stated; this delivery does not claim to close their dependencies.

## No longer needed

None. All original imports remain necessary for the statements and comparison
constructions. The three added proof imports are used. No node or module of the
original proof plan is bypassed, and no pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface discrepancy found. The proof-dependency imports
were absent from the original module, as anticipated by the worker brief.
The library already provides the needed statements, so no new node is necessary.
Searches used Lean Finder for derived comparison invertibility, Loogle for
`CategoryTheory.Functor.leftDerivedUnique`, and grep for the derived uniqueness
and tilde-pullback interfaces. No theorem directly proving this exact conjunction
was found; Mathlib's derived-lift factorization and natural-transformation
isomorphism transport suffice for the categorical glue.

## Second reading by C1

1. Compared the delivered module with the repository version. Existing declarations and both comparison definitions are byte-for-byte unchanged; only proof-only imports, a private helper, and the target proof were added. Verdict: pass.
2. Compiled the module with `lcompile.py`; it compiles successfully with no errors and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. Verdict: pass.
3. The sole target statement is unchanged and the proof establishes both `IsIso` conclusions directly. No new split-off statements or nodes were added. Verdict: pass.
4. The proof uses the existing K-flatness, pullback/tilde, and affine derived-sections declarations; the three added imports are proof-only and used. No old proof dependency or unit route was bypassed, and no pruning is claimed. Verdict: pass.
5. The node's proof steps and dependencies agree with the implemented route: K-flat transport and derived counit comparison for the first factor, then Spec full faithfulness, tensor-pullback/tilde natural isomorphism, and derived sections-unit transport for the second. Verdict: pass.

Changed only this report section; no Lean or DAG repairs were necessary.
