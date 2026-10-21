# AlgebraicGeometry.Scheme.purTwistIntegralLocalModels

## Reason

Close the original local-model theorem using the completed coefficient pushout,
positive uniformizer quotients, and scalar-extension local bases. Private helpers
make the large limit constructions usable without repeated unfolding. The
preflight requires this record because the module adds local commands and a
section of private helper parameters.

## Old

The public signature below was followed by `:= by sorry`:

```lean
theorem purTwistIntegralLocalModels
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [∀ x : S, Invertible (l : S.residueField x)]
    (hL : (purTwistZlModule S l).IsFiniteLocallyFreeOfRank 1) :
    (∃ (I : Type (u + 1)) (U : I → S.ProEt)
      (f : ∀ i, U i ⟶ ProEt.mk (𝟙 S)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
      ∀ i, Nonempty ((purTwistIntegralModule S l E).over (U i) ≅
        (SheafOfModules.unit
          (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E S)).over (U i))) ∧
    ∀ n : ℕ,
      Nonempty (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E S n)
          (purTwistIntegralModule S l E) ≅ purTwistFiniteOne S l E n) ∧
      (∃ (I : Type (u + 1)) (U : I → S.ProEt)
        (f : ∀ i, U i ⟶ ProEt.mk (𝟙 S)),
        Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
        ∀ i, Nonempty ((purTwistFiniteOne S l E n).over (U i) ≅
          (SheafOfModules.unit (WeilConjectures.integralCoefficientSheaf l E S n)).over (U i))) ∧
      (Nonempty S → ¬IsZero (purTwistFiniteOne S l E n)) ```

The module had no private helper section or proof-only imports.

## New

The displayed public signature is byte-for-byte unchanged and has a complete proof.
Every added declaration is private. Added commands are proof elaboration options,
`open scoped ChangeOfRings TensorProduct`, local irreducibility attributes on
private constructions, and variables scoped inside `section QuotientTransport`.
They provide no new public declarations, instances, notation, or attributes.
All existing public imports remain verbatim. Proof-only imports are
`import all Sheaf.Paper.ScalarExtensionDualLocalIso`,
`import all Sheaf.Paper.PurTwistCoefficientTensor`,
`import all Sheaf.Paper.PurInverseImageScalarComparison`,
`import all Mathlib.CategoryTheory.Limits.HasLimits`, and
`import Mathlib.RingTheory.AdicCompletion.Completeness`.
The final `#print axioms` command verifies that the theorem uses exactly
`propext`, `Classical.choice`, and `Quot.sound`; the file compiles without warnings.
No statement or definition used by the target changes.

## Users

`tools/downstream.py Sheaf.Paper.PurTwistIntegralLocalModels --uses
purTwistIntegralLocalModels` found the following declaration users. No consumer
adaptation is needed; the theorem's type and visibility stay unchanged. The other
170 transitive importers do not mention this declaration directly.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PurTwistIntegralLocalModels | B5 | original hole proved; private proof helpers |
| Sheaf.Paper.PurTwistSheafLocallyFree | unclaimed | unchanged consumer of identical signature |

## Status

landed 20261021T155746-L-3437657 2026-10-21 (merge of deliver/B5/Sheaf.Paper.PurTwistIntegralLocalModels)
