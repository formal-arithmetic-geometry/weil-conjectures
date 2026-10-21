# ModuleCat.localizedTensorComparisonProperty_closure_retracts

## Reason

Complete the listed retirement of
Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetract in
coord/retire-items.tsv. This module has zero direct sorry holes and duplicates
an already proved source theorem under the same declaration name. The source
statement drops only the unused hypothesis hC that C is flat over A tensor_R B.
Its remaining parameters and conclusion agree with the former declaration.

## Old

With the identical ambient ring, algebra, derived-category, Q, N and t
parameters of the two modules, the former Sheaf signature is:

```lean
theorem localizedTensorComparisonProperty_closure_retracts
    (hC : Module.Flat (A ⊗[R] B) C)
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    ∀ {X Y : DerivedCategory (ModuleCat.{u} A)}, Retract X Y →
      localizedTensorComparisonProperty R A B C Q N t Y →
      localizedTensorComparisonProperty R A B C Q N t X
```

The Sheaf proof already applied the fully proved upstream retract core,
explicitly discarding hC. It contains no direct sorry.

## New

Withdraw lean/Sheaf/Algebra/Homology/LocalizedTensorComparisonClosureRetract.lean
through deleted.txt. Reattach the existing node
lem-pc-localized-tensor-comparison-closure-retracts to the unchanged source module
WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosureRetract.
Its signature, under the same ambient parameters, is:

```lean
theorem localizedTensorComparisonProperty_closure_retracts
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic) :
    ∀ {X Y : DerivedCategory (ModuleCat.{u} A)}, Retract X Y →
      localizedTensorComparisonProperty R A B C Q N t Y →
      localizedTensorComparisonProperty R A B C Q N t X
```

The exact former statement follows by the following proof, checked in
scratchpad/UpstreamRetractProbe.lean:

```lean
  intro X Y hXY hY
  exact (fun (_ : Module.Flat (A ⊗[R] B) C) ↦
    localizedTensorComparisonProperty_closure_retracts R A B C Q N t hQ hXY hY) hC
```

Thus even the original hypotheses prove exactly the original conclusion;
the mathematical node statement needs no change. This works uniformly for
zero rings, zero objects, identity retracts, arbitrary unbounded complexes,
and arbitrary t. The source proof uses the same representative/model
identification and arrow-retract argument as the existing node proof plan.
Only its Lean attachment changes; no source declaration, signature, attribute,
public import, definition, target statement, proof dependency or unit route changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetract | J2 | Retire duplicate and retain node with source attachment. |
| WeilConjectures.Algebra.Homology.LocalizedTensorComparisonClosure | unclaimed | Existing consumer already imports and applies the upstream theorem without hC; unchanged and compile checked. |

The downstream.py query reports zero modules downstream of the Sheaf copy.
Whole-library and quarantine searches find no import of that copy. The old
consumer named in the retirement table,
Sheaf.Algebra.Homology.LocalizedTensorComparisonClosure, is already absent;
its existing node points to the source consumer above. That consumer's final
conjunct is exactly the source retract theorem applied to hQ, and its entire
statement remains unchanged.

Incoming DAG edges were checked by parsing every node's stmt_deps, proof_deps
and proof-step uses. The closure node depends on this retract node in its
proof; the retract-core node refers to it in stmt_deps. Both references remain
valid through the new Lean attachment, with no dependency removed. The unit
sk-thm-picard-semicon has empty realized statement and step lists; it and its
blueprint route are preserved. No rework row names this module, no quarantined
copy is removed, and no current return for J2 requests any other repair.
There are no forced consumer adaptations.

Validation: lcompile.py compiled the original Sheaf module in 2.4 seconds.
The exact former statement was proved from the upstream theorem in a separate
scratch probe. #print axioms for both the upstream theorem and this proof
reported exactly propext, Classical.choice and Quot.sound. The unchanged source
closure consumer was also compiled separately. The delivery adds no theorem,
no hole and no definition; the source theorem is already fully proved.

## Status

landed 20261021T014224-L-2390169 2026-10-21 (merge of deliver/J2/Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetract)
