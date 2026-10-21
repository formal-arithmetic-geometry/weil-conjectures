# AlgebraicGeometry.Etale.boundaryAlphaNormalization

## Reason

Name the exact three-conclusion proposition `boundaryNormalizationConclusions`.
The original hypotheses, including both extra admissibility hypotheses on K and on K',
are retained. The named proposition expands to the same isomorphism, independent Hom-chain
identity and naturality equation. `boundaryPFOnFiniteTor` only applies the original
projection-formula hypothesis to the bounded-constructible component of each test object.
No hypothesis is added or dropped and no conclusion is weakened.

The expanded concrete statement caused kernel conversion to unfold the derived inverse
image/internal Hom interfaces for more than 60 seconds. Sharing the proposition between
the arbitrary-ring theorem and its coefficient specialization makes the module compile
in about 10 seconds. This is an intermediate theorem, not a declaration of Challenge.lean;
no target signature changes. Renew its statement-meaning review along with the changed
underlying definitions.

## Old

```lean
theorem boundaryAlphaNormalization
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {Z T : Scheme.{u}} (aT : T ⟶ Spec (.of D.k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (i : Z ⟶ T) [IsClosedImmersion i]
    (hPF : ∀ B : DerivedCategoryModule (boundaryCoefficient l E n) Z,
      DerivedCategory.isBoundedConstructible (boundaryCoefficient l E n) Z B →
      ∀ M : DerivedCategoryModule (boundaryCoefficient l E n) T,
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T M →
      IsIso (boundaryProjection (boundaryCoefficient l E n) i B M))
    (K : DerivedCategoryModule (boundaryCoefficient l E n) T)
    (hK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T K)
    (_hDK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T
      ((boundaryDT (boundaryCoefficient l E n) aT).obj (op K)))
    (_hiK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
      (L(upperStar (ModuleCat.{u + 1} (boundaryCoefficient l E n)) i).obj K))
    (hGDK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
      ((boundaryG (boundaryCoefficient l E n) i).obj
        ((boundaryDT (boundaryCoefficient l E n) aT).obj (op K))))
    (_hdual : ∀ B : DerivedCategoryModule (boundaryCoefficient l E n) Z,
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z B →
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
        ((boundaryDZ (boundaryCoefficient l E n) i aT).obj (op B))) :
    IsIso (boundaryAlpha (boundaryCoefficient l E n) i
      (boundaryOmegaT (boundaryCoefficient l E n) aT) K (hPF _ hGDK.1 K hK)) ∧
    (∀ (B : DerivedCategoryModule (boundaryCoefficient l E n) Z)
      (hB : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z B)
      (b : B ⟶ (boundaryG (boundaryCoefficient l E n) i).obj
        ((boundaryDT (boundaryCoefficient l E n) aT).obj (op K))),
      boundaryAlphaHomChain (boundaryCoefficient l E n) i
        (boundaryOmegaT (boundaryCoefficient l E n) aT) K B (hPF B hB.1 K hK) b =
      b ≫ boundaryAlpha (boundaryCoefficient l E n) i
        (boundaryOmegaT (boundaryCoefficient l E n) aT) K (hPF _ hGDK.1 K hK)) ∧
    (∀ (K' : DerivedCategoryModule (boundaryCoefficient l E n) T)
      (hK' : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T K')
      (_hDK' : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T
        ((boundaryDT (boundaryCoefficient l E n) aT).obj (op K')))
      (_hiK' : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
        (L(upperStar (ModuleCat.{u + 1} (boundaryCoefficient l E n)) i).obj K'))
      (hGDK' : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
        ((boundaryG (boundaryCoefficient l E n) i).obj
          ((boundaryDT (boundaryCoefficient l E n) aT).obj (op K'))))
      (u : K ⟶ K'),
      (boundaryG (boundaryCoefficient l E n) i).map
          ((boundaryDT (boundaryCoefficient l E n) aT).map u.op) ≫
        boundaryAlpha (boundaryCoefficient l E n) i
          (boundaryOmegaT (boundaryCoefficient l E n) aT) K (hPF _ hGDK.1 K hK) =
      boundaryAlpha (boundaryCoefficient l E n) i
          (boundaryOmegaT (boundaryCoefficient l E n) aT) K' (hPF _ hGDK'.1 K' hK') ≫
        (boundaryDZ (boundaryCoefficient l E n) i aT).map
          (L(upperStar (ModuleCat.{u + 1} (boundaryCoefficient l E n)) i).map u).op) := by
  sorry
```

## New

```lean
theorem boundaryAlphaNormalization
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) {Z T : Scheme.{u}} (aT : T ⟶ Spec (.of D.k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (i : Z ⟶ T) [IsClosedImmersion i]
    (hPF : ∀ B : DerivedCategoryModule (boundaryCoefficient l E n) Z,
      DerivedCategory.isBoundedConstructible (boundaryCoefficient l E n) Z B →
      ∀ M : DerivedCategoryModule (boundaryCoefficient l E n) T,
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T M →
      IsIso (boundaryProjection (boundaryCoefficient l E n) i B M))
    (K : DerivedCategoryModule (boundaryCoefficient l E n) T)
    (hK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T K)
    (_hDK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T
      ((boundaryDT (boundaryCoefficient l E n) aT).obj (op K)))
    (_hiK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
      (L(upperStar (ModuleCat.{u + 1} (boundaryCoefficient l E n)) i).obj K))
    (hGDK : WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
      ((boundaryG (boundaryCoefficient l E n) i).obj
        ((boundaryDT (boundaryCoefficient l E n) aT).obj (op K))))
    (_hdual : ∀ B : DerivedCategoryModule (boundaryCoefficient l E n) Z,
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z B →
      WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z
        ((boundaryDZ (boundaryCoefficient l E n) i aT).obj (op B))) :
    boundaryNormalizationConclusions (boundaryCoefficient l E n) i aT
      (WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T)
      (WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z)
      (boundaryPFOnFiniteTor l E n i hPF) K hK hGDK := by
  exact boundaryAlphaNormalizationAllTests (boundaryCoefficient l E n) i aT
    (WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T)
    (WeilConjectures.finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) Z)
    (boundaryPFOnFiniteTor l E n i hPF) K hK _hDK _hiK hGDK _hdual
```

## Users

There are no current downstream textual users of these definitions according to
`tools/downstream.py --uses`. The pending parent is quarantined at
`quarantine/Sheaf/SixFunctors/BoundaryDualityDischarge.lean` (recorded in coord/rework.tsv),
and is unclaimed. It imports this item but does not mention the changed definitions.
Its DAG attachment and proof dependencies remain intact.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.BoundaryAlphaNormalization | C6 | Canonical formulas factored through real categorical constructions. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed; quarantined | Same hypotheses and conclusions; no direct uses of the changed declarations. |

## Status

landed 20261021T005730-L-1886275 2026-10-21 (merge of deliver/C6/Sheaf.SixFunctors.BoundaryAlphaNormalization)
