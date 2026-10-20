# coefficientSystem_abelian_exists and coefficientEvaluation_exact

## Reason

Prove the two componentwise-category assertions by the declared general
strict-system category theorem. This needs a private equivalence between
successor-transition systems and systems with all iterated transitions.
The concrete constant quotient sheaves make direct kernel normalization slow;
iteration and its semilinearity are therefore proved first for an arbitrary
ring-sheaf diagram and then specialized.

The static preflight scan flags the new commands, even though their scope is
private. All new reducibility attributes and backward-elaboration options lie
inside `section CoefficientSystemBridge` and end before the original public
normalization definition. The section's `omit` commands restrict only individual
private helper theorems. No public statement, definition body, instance body,
attribute or import changes. Two private proof imports are added, and the unused
private `Sheaf.Paper.PbcCompletedPullbackActual` import is removed.

The abelian instance still chooses its value from the same uniquely determining
existence theorem. This delivery changes that theorem's proof. Target statements
and the meanings of their definitions are unchanged; no target review is reopened.

## Old

```lean
theorem coefficientSystem_abelian_exists :
    ∃! a : Abelian (CoefficientSystem (J := J) O ell),
      CoefficientSystem.AbelianNormalized a := by
  sorry

theorem coefficientEvaluation_exact (n : ℕ) :
    PreservesFiniteLimits (coefficientEvaluation (J := J) (O := O) (ell := ell) n) ∧
      PreservesFiniteColimits (coefficientEvaluation (J := J) (O := O) (ell := ell) n) := by
  sorry
```

## New

```lean
theorem coefficientSystem_abelian_exists :
    ∃! a : Abelian (CoefficientSystem (J := J) O ell),
      CoefficientSystem.AbelianNormalized a := by
  let e := coefficientSystemEquivalence (J := J) (O := O) (ell := ell)
  let : Preadditive (CoefficientSystem (J := J) O ell) :=
    Preadditive.ofFullyFaithful e.fullyFaithfulFunctor
  have : e.functor.Additive := e.fullyFaithfulFunctor.additive_ofFullyFaithful
  have : HasFiniteProducts (CoefficientSystem (J := J) O ell) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
  let a : Abelian (CoefficientSystem (J := J) O ell) := abelianOfEquivalence e.functor
  refine ⟨a, ?_, ?_⟩
  · intro n
    change (e.functor ⋙ systemEvaluation _ n).Additive
    infer_instance
  · intro b _
    have hsub : Subsingleton (Preadditive (CoefficientSystem (J := J) O ell)) := by
      let := a
      infer_instance
    cases b
    cases a
    congr 1
    exact hsub.elim _ _

theorem coefficientEvaluation_exact (n : ℕ) :
    PreservesFiniteLimits (coefficientEvaluation (J := J) (O := O) (ell := ell) n) ∧
      PreservesFiniteColimits (coefficientEvaluation (J := J) (O := O) (ell := ell) n) := by
  let e := coefficientSystemEquivalence (J := J) (O := O) (ell := ell)
  constructor
  · change PreservesFiniteLimits (e.functor ⋙ systemEvaluation _ n)
    infer_instance
  · change PreservesFiniteColimits (e.functor ⋙ systemEvaluation _ n)
    infer_instance
```

The private bridge's scoped commands are `set_option
backward.isDefEq.respectTransparency false`, `set_option
backward.isDefEq.respectTransparency.types false`, and `attribute [local
irreducible] coefficientQuotientSheaf coefficientQuotientMap`. Their scope ends
with `end CoefficientSystemBridge`. The old file had no such bridge section.
No existing declaration is removed or renamed.

## Users

`tools/downstream.py` lists one downstream module. Searching with `--uses` for
each changed theorem finds only the item module itself. The shared claim records
have no claim for the downstream module at the time of this inventory.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint | U9 | Two theorem proofs completed; original signatures, definitions and instances preserved. |
| Sheaf.Paper.CoefficientSystemDerivedComparison | unclaimed in shared records | No adaptation: its public import and all used public signatures and data are unchanged; the new local commands do not escape their section. |

The unchanged downstream source was compiled with the prescribed remote compiler
against the updated module: no errors or warnings, 32.4 seconds. No forced adaptation
is included.

## Status

landed 20261020T174909-L-817096 2026-10-20 (merge of deliver/U9/Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint)
