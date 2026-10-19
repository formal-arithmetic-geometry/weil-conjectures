# CategoryTheory.constantZModRingSheaf

## Reason

The proof of the unique normalized action uses the existing Mathlib
`PresheafOfModules.Sheafify.module` and `SMulCandidate` interface, matching
Stacks Tag 03CY. Its ring sheafification unit must be locally bijective.
Mathlib's concrete sheafification instances for rings apply with the
coefficient universe `max vC uC`. The previous unrelated universe `w`
does not synthesize these instances from `HasSheafify` alone.
Choose the constant ring in the site universe, retaining arbitrary sites
and arbitrary independent abelian-group universe `w`. This is the same
constant sheaf of Z/N, with its size fixed to the standard site universe.
No mathematical hypothesis on the site or on the abelian sheaf is added.
The main proof is fully constructed; no existence axiom or additional
holed theorem supplies the action.

## Old

```lean
variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J RingCat.{w}]

/-- The constant sheaf of rings with value `Z/N`, lifted to the coefficient universe.
Source: Stacks Project, Tag 03CY (blueprint: lem-pur-torsion-sheaf-constant-module). -/
noncomputable abbrev constantZModRingSheaf (N : ℕ) : Sheaf J RingCat.{w} :=
  (constantSheaf J RingCat.{w}).obj (RingCat.of (ULift.{w} (ZMod N)))
```

The remaining signatures are textually unchanged, but inherit the old
constant-ring universe through this abbreviation and section instance.

## New

```lean
variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J RingCat.{max vC uC}]

/-- The constant sheaf of rings with value `Z/N`, lifted to the coefficient universe.
Source: Stacks Project, Tag 03CY (blueprint: lem-pur-torsion-sheaf-constant-module). -/
noncomputable abbrev constantZModRingSheaf (N : ℕ) : Sheaf J RingCat.{max vC uC} :=
  (constantSheaf J RingCat.{max vC uC}).obj (RingCat.of (ULift.{max vC uC} (ZMod N)))
```

The remaining signatures inherit this constant-ring universe. The independent
`w` is still the universe of the groups and module sheaves. This includes
`IsConstantZModSheafModuleStructure`,
`existsUnique_constantZModSheafModuleStructure`,
`torsionSheafModuleStructure`, `torsionSheafModuleStructure_spec`,
`torsionSheafModule`, `constantZModModuleSheaf_nsmul`, and
`torsionSheaf_hom_linear`. Their mathematical assertions and normalization
conditions are unchanged. The existing target declarations are untouched.

The only consumer edit is:

```lean
-- Old
  constantZModRingSheaf.{u + 1} (ProEt.topology S) N
-- New
  constantZModRingSheaf (ProEt.topology S) N
```

Its result annotation remains `Sheaf (ProEt.topology S) RingCat.{u + 1}`.
All explicit module/group universe arguments remain unchanged.

## Users

`tools/downstream.py` reports 715 transitive downstream modules. Its `--uses`
search, supplemented by searches for all declarations of the item, finds
only the following modules that explicitly use this interface. Transitive
users see the same pro-etale coefficient sheaf in universe `u + 1`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.TorsionSheafConstantModule | E4 | Site-sized constant ring; independent group universe retained; last hole proved. |
| Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf | unclaimed | Remove obsolete explicit universe argument on the abbreviation; no signature or visibility edit. Compiles against the new item. |
| Sheaf.Paper.PurTwistSheafLocallyFree | C8 | Uses proEtaleRootsOfUnityCoefficientRing as the unchanged pro-etale ring in universe u + 1; no edit necessary. |
| Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso | unclaimed | No edit needed; compiled unchanged against the new item and its consumer. |

All three modules compiled as a sandbox set, with no errors or warnings.
The latter unchanged consumer is not included in the delivery.
No target uses the changed constant-ring definition in its statement;
`lean/Challenge.lean` refers to the upstream etale sheaf encoding instead.

## Status

landed 20261019T093343-L-2300206 2026-10-19 (merge of deliver/E4/Sheaf.CategoryTheory.TorsionSheafConstantModule)
