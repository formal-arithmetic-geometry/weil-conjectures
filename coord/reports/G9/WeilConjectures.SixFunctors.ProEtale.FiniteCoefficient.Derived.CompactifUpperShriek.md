## What changed

Marked the existing instance
`AlgebraicGeometry.ProEtale.CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper`
as `STATEMENT-DISPUTED` without changing any signature, body, attribute, or import.
The existing proper-pushforward node now records its actual namespace and module.
Updated that node and `sk-def-sfb-finite-upper-shriek` to distinguish the present
protected API from the historical F3 withdrawal recorded in their proofs.

The false instance cannot be proved. This is a disputed-statement delivery, not a proof
or decomposition. The source-library boundary and absence of an exception for this module
prevent the historical withdrawal or addition of the missing hypotheses.

## Proved and sorry left

Holes closed: zero. Holes added: zero. One original hole remains:
`AlgebraicGeometry.ProEtale.CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper`
(node `thm-sfb-finite-proper-pushforward-left-adjoint`). No split-off statement was added.

A sandbox-only probe proved the negation of that instance's exact conclusion for the
structure morphism of any positive dimensional abelian variety over an algebraically
closed field with field coefficients. It applies the existing library theorem
`AlgebraicGeometry.ProEtale.not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety`
to the colimit-preservation instance supplied by a hypothetical left adjoint.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
No proof by contradiction from the legacy sorry is used or submitted.

The probe is `scratchpad/Counterexample.lean`; its complete proof is:

```lean
module
public import WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts
@[expose] public section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

theorem assignedProperAdjointCounterexample (Λ : Type (u + 1)) [Field Λ]
    {k : Type u} [Field k] [IsAlgClosed k]
    (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E]
    (hE : 0 < IsAbelianVariety.dim E) :
    ¬ ((E.hom)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor.IsLeftAdjoint := by
  intro h
  let := h
  exact not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety Λ E hE
    inferInstance

#print axioms assignedProperAdjointCounterexample
end AlgebraicGeometry.ProEtale
```

## No longer needed

None: no import, module, node, or declaration is withdrawn. In particular, the previous
withdrawal's pruning claim is not repeated. Brown representability cannot prove the
instance because its coproduct-preservation premise fails. The active constructible
exceptional inverse image remains as before.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the assigned unconditional proper pro-etale left-adjoint assertion
is false, as already documented by the current blueprint's `sk-rem-sf-fullcd-scope`
and the earlier F3 independent review. The exact negation was checked against the current
compiled library rather than inferred only from the historical review. Abelian varieties
are proper, so this is a counterexample satisfying the assigned geometric hypothesis.
The field-coefficient module category satisfies the assigned Grothendieck abelian
hypotheses. A left adjoint preserves countable coproducts, contradicting the cited theorem.

The DAG had recorded the API as withdrawn, while the current adopted source contains
it again with the original sorry. Searching for its actual module in node lean records
therefore initially returned no match. The theorem node is now attached to the actual
`CompactificationUpperShriek` namespace. No mathematical statement was weakened.

No source correction exception lists this module. Maintainer resolution of that conflict
is needed before a corrected positive theorem or retirement can replace the false API.
The unit realized arrays are empty; this delivery bypasses no unit step. No change record
is needed because this delivery changes no definition, statement, visibility, or import.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
