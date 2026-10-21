# CategoryTheory.RingedDerivedNative.complexConstraints

## Reason

The stage-3 static gate classifies added section variables and local elaboration
commands as a possible interface change. This record documents their scope.
The four existing predicates, the structure and all their public signatures are
unchanged. Only the theorem proof and private helpers are added. No definition
used by a target is changed, and no target statement needs renewed semantic review.

The helper `forgetLax` constructs the existing right-adjoint lax monoidal structure.
It is a private definition registered with `[local instance]` only inside its
section. There is no added global instance. The two `backward.isDefEq` options are
also scoped to helper-proof sections. Generic-category variables end at
`end Generic`, before the original public declarations. None of these commands
changes the environment seen by an importing module.

## Old

```lean
theorem complexConstraints : ComplexConstraints.{c, v, u} J R := by
  sorry
```

There were no private helper sections, nor a `forgetLax` helper.

## New

```lean
theorem complexConstraints : ComplexConstraints.{c, v, u} J R := by
  exact ⟨symmetry_formula.{c, v, u} J R, associator_formula.{c, v, u} J R,
    leftUnitor_formula.{c, v, u} J R, rightUnitor_formula.{c, v, u} J R⟩
```

The private proof import `Sheaf.SecSmoothPurity.ModuleTensorGenerators` supplies
proved ordinary module-tensor formulas. All public imports remain verbatim.
The actual private helper and its section-local registration are:

```lean
@[reducible] private noncomputable def forgetLax :
    (forgetModules.{c, v, u} J R).LaxMonoidal :=
  (tensorAdj.{c, v, u} J R).rightAdjointLaxMonoidal

attribute [local instance] forgetLax
```

## Users

`tools/downstream.py` reports 1080 transitive importers; its `--uses
CategoryTheory.RingedDerivedNative.complexConstraints` scan reports exactly the
item itself and `RingedDerivedClosedSymmetricMonoidal`. The direct-import scan
reports the three consumers below. There is no public interface change and no
consumer requires adaptation. Current claim records identify Y8 and Q2 for the two import-only consumers;
the theorem caller has no claim in this checkout.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedTensorComplexConstraints | H2 (this item) | Hole replaced by a complete proof; statements unchanged. |
| Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal | unclaimed | Existing application has exactly the same type. |
| Sheaf.Algebra.Homology.OneKFlatChainTranspose | Y8 | Public import interface unchanged. |
| Sheaf.Algebra.Homology.TotalTensorSignedCoherence | Q2 | Public import interface unchanged. |

No other module is modified or adapted.

## Status

landed 20261021T130030-L-2496645 2026-10-21 (merge of deliver/H2/Sheaf.Algebra.Homology.RingedTensorComplexConstraints)
