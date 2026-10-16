# lem-weil-pbc-lisse-lattice-finite-etale-descent

## Reason

The existing node's Lean attachment names a file absent from this checkout. No declaration
can be imported at that path. This delivery realizes the same finite-etale lattice descent
step directly for internal modules over the continuous coefficients used by its parent.
This is a replacement Lean attachment, not a change to the mathematical node statement.
The given norm is the unique extension of the p-adic norm; its closed unit ball is the
coefficient-extension valuation ring. The internal-module and sectionwise-module versions
therefore express the same lattice theorem. No new descent datum is imposed. No target
signature or meaning changes. The node's existing mathematical statement and detailed sum-of-sheet-lattices argument
are retained. An initial proof step now records the coefficient and module conversion
needed by the internal-module attachment, citing the existing generic equivalence and
continuous coefficient realizations. Their specific compatibilities remain part of
this lower proof obligation.

## Old

```json
{
  "module": "Sheaf.AlgebraicGeometry.LisseLatticeFiniteEtaleDescent",
  "declaration": "AlgebraicGeometry.ProEtale.exists_lisse_lattice_finite_etale_descent",
  "file": "lean/Sheaf/AlgebraicGeometry/LisseLatticeFiniteEtaleDescent.lean",
  "statement": "theorem exists_lisse_lattice_finite_etale_descent (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] (L : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X))) (hL : L.IsFiniteLocallyFree) {Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] [Etale p] [Surjective p] (hM : ∃ M : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheaf l E Y)), M.IsFiniteLocallyFree ∧ Nonempty ((SheafOfModules.changeOfRings.{u, u + 1, u + 1} (lisseIntegerToField l E Y) M).val ≅ (PresheafOfModules.pushforward.{u + 1, u, u, u + 1, u + 1, u + 1} (lisseEtaleCoefficientIdentification l E p)).obj L.val)) : ∃ M₀ : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheaf l E X)), M₀.IsFiniteLocallyFree ∧ Nonempty ((SheafOfModules.changeOfRings.{u, u + 1, u + 1} (lisseIntegerToField l E X) M₀).val ≅ L.val)",
  "branch": "newtargets-dag",
  "by": "NY",
  "date": "2026-10-15",
  "existing": false
}
```

The attached file does not exist, so there is no existing Lean signature to change.

## New

```lean
theorem continuousLisse_finiteEtale_lattice
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod _).obj P))
    {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) U))
    (hM : ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage U, ∀ s : D.I₀,
        Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (D.f s)).obj
          (condensedRingObj (integralCoeff ℓ E) U))
          (((ProEtale.upperStar Ab.{u + 1} (D.f s)).mapMod _).obj M))
    (e : Nonempty ((Mod.extendScalars
      (coefficientMap (integralScalarMap ℓ E) U)).obj M ≅
        (CondensedRing.upperStar (Profinite.continuousMapRingObj E) p).obj P)) :
    ∃ N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X),
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
        Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj
          (condensedRingObj (integralCoeff ℓ E) X))
          (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod _).obj N)) ∧
      Nonempty ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj N ≅ P)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.LisseLatticeFiniteEtaleDescent | unclaimed, file absent | Missing attachment replaced. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | C4 | New proved consumer of this node. |

No existing Lean module imports the absent file; this was checked by text search.

## Status

landed 20261016T064222-L-582225 2026-10-16 (merge of deliver/C4/Sheaf.Paper.ContinuousConstructibleIntegralStratum)
