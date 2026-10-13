# sectionRing_veronese_fraction_core

## Reason

Review #1428 asks for bijectivity of the specified canonical map [n, ξ] ↦ ξ/s^n.
The earlier repair already states bijectivity, but its conclusion does not expose
the forward generator computation. Certify that computation in the same theorem,
using the existing inverse formula. The canonical-map definition is unchanged.

## Old

```lean
theorem sectionRing_veronese_fraction_core
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    Function.Bijective
      (sectionRingVeroneseFractionCanonicalMap X L d s)
```

## New

```lean
theorem sectionRing_veronese_fraction_core
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    Function.Bijective
      (sectionRingVeroneseFractionCanonicalMap X L d s) ∧
    ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
      sectionRingVeroneseFractionCanonicalMap X L d s
        (sectionFraction (L.tensorPow d) (𝟙_ X.Modules) (s.val d) n
          ((eqToIso (congrArg L.tensorPow (by simp [Nat.mul_comm])) ≪≫
            L.tensorPowMulIso d n ≪≫ (λ_ _).symm).hom.app ⊤ (ξ.val (n • d)))) =
      HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
        ξ.val ξ.property
```

## Users

`tools/downstream.py` and a whole-library declaration search find no module
that mentions the changed declaration. The existing Fractions importer uses the
Formula theorem directly; it compiles unchanged against this repair. No existing
consumer or target signature changes, and there are no forced adaptations.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractions` | unclaimed | Direct importer; no use of the changed theorem, no adaptation. |

No DAG node cites this node in its current statement or proof dependencies.
The Formula node mentions it only in historical statement-change metadata.

## Status

landed 20261013T215617-L-903340 2026-10-13 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore)
