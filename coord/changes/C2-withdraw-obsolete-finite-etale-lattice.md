# AlgebraicGeometry.ProEtale.exists_lisse_lattice_finite_etale_descent

## Reason

Withdraw the obsolete section-module version under dispatched brief step 8d. Its node,
`lem-weil-pbc-lisse-lattice-finite-etale-descent`, already attaches to
`AlgebraicGeometry.ProEtale.CondensedRing.continuousLisse_finiteEtale_lattice` in
`Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent`. That attachment was changed by C4
in `C4-finite-etale-lattice-attachment.md`, and the active theorem now has a complete
Lean proof from the intersection and kernel-model declarations. The old module was
subsequently present again but its sole declaration has no users. The sole remaining
import is private and unused in `Sheaf.Paper.LisseEConstructibleIntegralLattice`,
which already imports the canonical replacement directly.

The old theorem is retired, not proved. This is a pruning delivery. No target or
surviving statement, definition, visibility, proof, or coefficient construction changes.
The existing node and its canonical attachment remain intact.

## Old

```lean
theorem exists_lisse_lattice_finite_etale_descent
    (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (L : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X)))
    (hL : L.IsFiniteLocallyFree)
    {Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (hM : ∃ M : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheaf l E Y)),
      M.IsFiniteLocallyFree ∧
        Nonempty ((SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (lisseIntegerToField l E Y) M).val ≅
          (PresheafOfModules.pushforward.{u + 1, u, u, u + 1, u + 1, u + 1}
            (lisseEtaleCoefficientIdentification l E p)).obj L.val)) :
    ∃ M₀ : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheaf l E X)),
      M₀.IsFiniteLocallyFree ∧
        Nonempty ((SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (lisseIntegerToField l E X) M₀).val ≅ L.val) := by
  sorry
```

The direct importer also has this unused proof import:

```lean
import Sheaf.AlgebraicGeometry.LisseLatticeFiniteEtaleDescent
```

## New

The retired module is listed in `deleted.txt`; delivery leaves an empty `module` file.
The direct importer drops precisely the import above, with all other text identical.
The retained realization is the existing theorem
`AlgebraicGeometry.ProEtale.CondensedRing.continuousLisse_finiteEtale_lattice`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.LisseLatticeFiniteEtaleDescent | C2 (dispatched item) | Obsolete unused declaration withdrawn. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | H8 | Only the unused private import is removed, as required by brief steps 8b/8d; all declarations and proofs identical. |

`tools/downstream.py Sheaf.AlgebraicGeometry.LisseLatticeFiniteEtaleDescent --uses
AlgebraicGeometry.ProEtale.exists_lisse_lattice_finite_etale_descent` reports 389
transitive import descendants and just one textual declaration use: its own defining
module. An independent `rg` search of both Lean roots confirms no declaration consumers
and precisely the direct importer above. The 389 indirect descendants use no retired
declaration; their signatures cannot change because the removed import was private.

## Status

landed 20261019T093303-L-2289210 2026-10-19 (merge of deliver/C2/Sheaf.AlgebraicGeometry.LisseLatticeFiniteEtaleDescent)
