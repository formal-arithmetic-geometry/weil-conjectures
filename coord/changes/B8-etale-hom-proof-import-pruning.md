# WeilConjectures.finiteCoefficient_derivedHom_ctf_etale

## Reason

Reuse proved source internal-Hom theorems and remove unused proof imports and redundant public
imports. The remaining public imports are FiniteFieldFiber, FiniteTorAmplitudeSites,
Mathlib.Topology.KrullDimension and the adopted Perfect.SitePerfect module. All symbols in
the statement remain public. The two new imports are private proof dependencies.

## Old

```lean
theorem finiteCoefficient_derivedHom_ctf_etale
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (m : ℕ) (_hm : topologicalKrullDim X ≤ (m : WithBot ℕ∞))
    (a b c d : ℤ) (_hab : a ≤ b) (_hcd : c ≤ d)
    (K M : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X)
    (_hK : finiteTorConstructibleEtale l E n hn X K)
    (_hM : finiteTorConstructibleEtale l E n hn X M)
    (_hKt : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X a b K)
    (_hMt : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X c d M) :
    finiteTorConstructibleEtale l E n hn X
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj M) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X
      (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj M) ∧
    (Etale.DerivedCategory.IsSitePerfect K →
      Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X (c - b) (d - a)
        (((Etale.derivedHom (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj M))
```

## New

```lean
theorem finiteCoefficient_derivedHom_ctf_etale
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (m : ℕ) (_hm : topologicalKrullDim X ≤ (m : WithBot ℕ∞))
    (a b c d : ℤ) (_hab : a ≤ b) (_hcd : c ≤ d)
    (K M : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X)
    (_hK : finiteTorConstructibleEtale l E n hn X K)
    (_hM : finiteTorConstructibleEtale l E n hn X M)
    (_hKt : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X a b K)
    (_hMt : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X c d M) :
    finiteTorConstructibleEtale l E n hn X
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj M) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X
      (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj M) ∧
    (Etale.DerivedCategory.IsSitePerfect K →
      Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X (c - b) (d - a)
        (((Etale.derivedHom (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj M))
```

The signature is identical to Old; its proof is now complete. Public import
exports shrink by the removed lines enumerated in report.md. No definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | B8 | Same signature; completed proof; smaller exports. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Unchanged consumer, checked alone. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Unchanged consumer, checked alone. |
| Sheaf.Paper.TensorExchangeCtfDomains | K9 | Unchanged consumer, checked alone; no adaptation. |

The direct importers above are also the complete downstream set reported by downstream.py.
No consumer needs a signature or proof change. The item is imported privately by all three.
All target statements and their definitions retain their meaning.

## Status

landed 20261025T162014-L-197297 2026-10-25 (merge of deliver/B8/Sheaf.Paper.EtaleHomFiniteTorAmplitude)
