# AlgebraicGeometry.Scheme.proEtale_torAmplitude_iff_residue_tensor

## Reason

The stage-3 interface scanner records new section variables, namespace/open commands,
local notation, and scoped elaboration options as a command change. They support the
private proofs added for tensor-homology independence and nilpotent filtration. This
record documents that syntactic change. All helpers and cached local instances are
private. The public theorem statement, visibility and public imports are unchanged.
There is no definition or statement repair and no forced adaptation.

## Old

```lean
theorem proEtale_torAmplitude_iff_residue_tensor
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)]
    (K P : CochainComplex (proEtaleRingModules T
      (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) ℤ)
    (f : P ⟶ K) (hf : QuasiIso f)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)) P)
    (_hK : intrinsicFiniteTorsionConstructible l E n hn T (DerivedCategory.Q.obj K))
    (a b : ℤ) (_hab : a ≤ b) :
    HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E n)
      (DerivedCategory.Q.obj K) a b ↔
      ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor (proEtaleRingModules T
          (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) i).obj
            (derivedTensorRing T (Padic.coefficientExtensionRing l E n)
              (Padic.coefficientExtensionRing l E n ⧸ Ideal.span
                {Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
                  (Padic.coefficientExtensionUniformizer l E)})
              (Ideal.Quotient.mk _) K P f hf hP))
```

The file had only `universe u`, `open CategoryTheory CategoryTheory.Limits`, and the
namespace `AlgebraicGeometry.Scheme` around this declaration.

## New

```lean
theorem proEtale_torAmplitude_iff_residue_tensor
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)]
    (K P : CochainComplex (proEtaleRingModules T
      (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) ℤ)
    (f : P ⟶ K) (hf : QuasiIso f)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)) P)
    (_hK : intrinsicFiniteTorsionConstructible l E n hn T (DerivedCategory.Q.obj K))
    (a b : ℤ) (_hab : a ≤ b) :
    HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E n)
      (DerivedCategory.Q.obj K) a b ↔
      ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor (proEtaleRingModules T
          (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) i).obj
            (derivedTensorRing T (Padic.coefficientExtensionRing l E n)
              (Padic.coefficientExtensionRing l E n ⧸ Ideal.span
                {Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)
                  (Padic.coefficientExtensionUniformizer l E)})
              (Ideal.Quotient.mk _) K P f hf hP))
```

Private proof scaffolding additionally uses universe `v`, the open namespace
`MonoidalCategory`, private helper sections and the local abbreviation for intrinsic
module sheaves. Scoped elaboration options handle the monoidal instance expressions.
The cached sheafification and tensor-preadditive instances are private and local.
No exported instance, notation, definition or signature changes.

## Users

`tools/downstream.py Sheaf.Paper.ProEtaleResidueTorTest --uses
AlgebraicGeometry.Scheme.proEtale_torAmplitude_iff_residue_tensor` reports no downstream
module and only the defining module as a textual user.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProEtaleResidueTorTest | G3 | Complete proof and private helpers; unchanged public signature. |

## Status

landed 20261018T071153-L-1667997 2026-10-18 (merge of deliver/G3/Sheaf.Paper.ProEtaleResidueTorTest)
