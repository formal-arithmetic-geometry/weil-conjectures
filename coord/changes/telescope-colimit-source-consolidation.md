# CochainComplex.telescopeShiftColimit

## Reason

The Sheaf module has zero holes and duplicates the complete source-library telescope
construction and comparison proof. It defines `telescopeToColimit` and
`quasiIso_telescopeColimit` with the same fully qualified names as the source module.
Its other public construction `telescopeShiftColimit` differs from the source
`telescopeColimitShift` only in name; their coproduct formulas are identical.
Use the existing proved source declarations and retain the old shift name as an
abbreviation. This removes the duplicate public declarations and private cokernel
construction, and makes importing this module together with the source telescope safe.
No source-library file is changed.

## Old

```lean
noncomputable def telescopeShiftColimit :
    (∐ (fun n : ℕ => E.obj n)) ⟶ (∐ (fun n : ℕ => E.obj n)) :=
  Sigma.desc (fun n : ℕ =>
    Sigma.ι (fun n : ℕ => E.obj n) n -
      E.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι (fun n : ℕ => E.obj n) (n + 1))

noncomputable def telescopeToColimit :
    (∐ (fun n : ℕ => E.obj n)) ⟶ colimit E :=
  Sigma.desc (fun n : ℕ => colimit.ι E n)

theorem quasiIso_telescopeColimit
    : ∃ f : mappingCone (telescopeShiftColimit R E) ⟶ colimit E,
      mappingCone.inr (telescopeShiftColimit R E) ≫ f = telescopeToColimit R E ∧
      (mappingCone.inl (telescopeShiftColimit R E)).comp
        (Cochain.ofHom f) (add_zero _) = 0 ∧
      QuasiIso f
```

The module also contained its own private `telescope_cokernel` universal-property
construction and a complete proof of the comparison theorem. Its public imports were
Mathlib.Algebra.Homology.HomotopyCategory.ShortExact,
Mathlib.Algebra.Homology.HomotopyCategory.HomComplex,
Mathlib.Algebra.Homology.HomologicalComplexLimits,
Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian,
Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits,
Mathlib.Algebra.Category.Grp.FilteredColimits, and Mathlib.Algebra.Category.Ring.Limits.
Its private proof import was WeilConjectures.Algebra.Homology.TelescopeShiftMono.

## New

```lean
public import WeilConjectures.Algebra.Homology.TelescopeColimit

noncomputable abbrev telescopeShiftColimit :
    (∐ (fun n : ℕ => E.obj n)) ⟶ (∐ (fun n : ℕ => E.obj n)) :=
  telescopeColimitShift R E
```

`telescopeToColimit` and `quasiIso_telescopeColimit` are now re-exported from that
source module. The comparison's shift argument is `telescopeColimitShift R E`,
definitionally equal to `telescopeShiftColimit R E`. Both canonicality equations,
the site and ring hypotheses, and all universes stay the same. The seven former
public Mathlib imports remain available through the source module's identical public
imports. The private monicity dependency and the cokernel argument remain in the
source proof. The DAG's Lean attachment now names this source declaration and its
source shift name, without changing the mathematical statement or proof dependencies.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.TelescopeColimit --uses
 telescopeShiftColimit telescopeToColimit quasiIso_telescopeColimit` found the
following three downstream modules and no textual downstream uses of these three
names. The only name uses reported were in the item itself. Source-tree `rg` found
the two direct importers shown below. No consumer needs an adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.TelescopeColimit | M4 | Re-export source comparison; retain shift abbreviation. |
| Sheaf.CategoryTheory.RingedCechKoszulHomLimitComparison | unclaimed in local claim records | Direct proof import retains all existing declarations and instances. |
| Sheaf.CategoryTheory.Sites.ContractibleDerivedSectionsTensor | unclaimed in local claim records | Direct proof import retains all existing declarations; also imports source TruncationTelescope, so consolidation avoids duplicate telescope names. |
| Sheaf.CategoryTheory.RingedCechKoszulComparisonOnSite | unclaimed in local claim records | Transitive consumer; statements and proof interfaces unchanged. |

Verification: the item compiles. A separate non-delivered probe checks the former
shift formula and colimit map by `rfl`, applies the source theorem to the former
existential signature with both canonicality clauses, and imports the source
TruncationTelescope at the same time. `#print axioms` for the comparison reports
only `propext`, `Classical.choice`, and `Quot.sound`. Thus no target's mathematical
statement changes through this definition replacement, including the zero diagram,
zero transition maps, and identity transition maps.

Both unchanged direct importers also compile against the consolidated module:
RingedCechKoszulHomLimitComparison in 3.4 seconds and
Sites.ContractibleDerivedSectionsTensor in 37.2 seconds.

## Status

landed 20261020T150655-L-2567895 2026-10-20 (merge of deliver/M4/Sheaf.Algebra.Homology.TelescopeColimit)
