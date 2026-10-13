## What changed

Proved `AlgebraicGeometry.Scheme.ideal_power_annihilator_quasicoherent` in
`Sheaf.AlgebraicGeometry.IdealPowerAnnihilatorQuasicoherent`, with its signature,
visibility, existing docstring, and all canonical definitions unchanged.

Added two proved private helpers: `range_ideal_basicOpen` builds the affine ideal-extension
identity for a quasi-coherent module map to the structure module;
`annihilator_quasicoherent_of_affine_fg` converts finitely generated affine ranges to
explicit `IdealSheafData`, proves finite type, establishes the canonical annihilator's
affine image formula by separatedness, and applies the existing annihilator theorem.
The main proof uses the already proved private `Modules.powers_affine_sections` and
`Modules.ideal_qc` from `CoherentSupportVanishingIdealNilpotence`, accessed through a
proof-only `import all`, and `Modules.finite_sections_of_finiteType` from
`QuasicoherentFiniteTypeAffine`, likewise accessed through a proof-only `import all`.
The additional ordinary proof import is `AnnihilatorQuasicoherent`.

Updated the item's DAG proof, dependencies, and proof origin to describe this route.
No new modules, nodes, interface changes, forced adaptations, or change records.
The blueprint unit's statement and realized steps are preserved.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.ideal_power_annihilator_quasicoherent`
(node `lem-weil-pbc-ideal-power-annihilator-quasicoherent`).
Both new private helpers are fully proved. No holes added, none left in the module.
This is a proof from existing declarations, not a decomposition into new holed statements.

The unchanged theorem includes n = 0. The reused power-range calculation explicitly
handles zero and identifies the range with the unit ideal, so the annihilator is zero.
For the zero ideal at positive exponents the affine range is zero, and the argument yields
F itself as the annihilator. Empty schemes are covered by the same affine-cover criterion;
none of the new helpers assumes a nonempty affine open or a nonempty generating family.
Local single-file compilation succeeds without warnings; the delivery dry run also runs
the declaration/axiom probe and the stage-3 static checks.

## No longer needed

No original imports removed and no whole module pruned. The original
`IdealModuleProductStalk` import remains necessary for the recursive power definitions,
but the proof does not use `ideal_module_product_stalk`, its stalk calculation, or its
quotient clauses. Removed `lem-weil-pbc-ideal-module-product-stalk` from this node's
proof dependencies; it remains a statement dependency for the definitions.

No new annihilator-localization, generic ideal-conversion, or power finite-type obligations
are needed. The existing generic power-range helper supplies the power calculation,
and the proved annihilator theorem supplies the finite-generator localization argument.
Exploratory direct imports of `Mathlib.RingTheory.Finiteness.Ideal`,
`WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion`, and
`Sheaf.AlgebraicGeometry.FinitePushforwardCoherent` were removed before the final compile.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically sound, but its sole proof dependency is a stalk
calculation and does not itself provide the required quasi-coherence/localization result.
The earlier search note correctly observed that the existing annihilator theorem takes
`IdealSheafData`; that interface mismatch is bridged here by explicitly taking affine
section ranges and proving their localization identity. No arbitrary existence witness
is used to define any data.

Although the module supplying `powers_affine_sections` has a Noetherian nilpotence theorem
as its main statement, the reused proved private helper is generic: no Noetherian,
coherence, support, or ideal-data hypotheses are added to this item. Likewise `ideal_qc`
is used only to establish quasi-coherence of the constructed ideal's module realization.

## Second reading by T3

1. **Unchanged interface — pass.** Compared the entire delivered module with the
   repository version using `diff` and the declaration parser. Every existing signature,
   visibility, definition body, instance, and docstring is unchanged. The only Lean changes
   are three proof-only imports, two proved private helpers, and the target's proof body.
   There are no statement changes, adapted modules, or change records.
2. **Proof and trust — pass.** Independently compiled the delivered file with `lcompile.py`
   without errors or warnings (8.2 seconds). A scratch copy with `#print axioms` for the
   target and both private helpers compiled and reported exactly `propext`,
   `Classical.choice`, and `Quot.sound` for each; no `sorryAx`. Scanned the delivered Lean
   for holes and forbidden declarations/options: none. Read the affine localization,
   finite-range identification, separatedness, and final power arguments; they prove the
   unchanged statement. Ideal data are explicitly affine ranges, not arbitrary witnesses
   selected from an unproved existence statement.
3. **Split statements — pass, none.** No new public or holed statements and no new nodes
   are introduced. Both private helpers are proved. Checked exponent zero (unit range),
   positive powers of the zero ideal, the empty affine cover, and empty generating
   families: the arguments require no nonemptiness. The reused power helper has only
   quasi-coherence hypotheses, and the finite-section helper has precisely the available
   quasi-coherence and finite-type hypotheses.
4. **Shortest route and pruning — pass.** Read the existing annihilator theorem and the
   reused private power, ideal quasi-coherence, and finite-section proofs. Independent
   Mathlib search for `IsQuasicoherent.*range|range.*IsQuasicoherent|annihilator.*quasicoherent`
   returned no hits; local searches for affine range/localization and annihilator results
   found the existing ideal-data annihilator theorem, which this proof already applies.
   No shorter matching theorem was found. The three added imports are proof-only; each
   supplies a used declaration. Original imports remain needed by canonical definitions
   or the existing sheaf proof. The old proof dependency omitted by the new route is
   fully listed under `## No longer needed`; its definitions remain imported. Checked
   `dag/units/sk-thm-p1.json`: this auxiliary node realizes no unit statement or step,
   and the delivery changes neither the unit nor its realized route.
5. **DAG agreement — pass.** The node differs only in `proof`, `proof_deps`, and
   `proof_origin`. Its three steps describe the actual Lean argument, and their `uses`
   union is exactly `proof_deps`; all four dependencies have the expected Lean modules.
   The nilpotence node is cited specifically for its proved generic private helpers,
   not for its stronger main theorem. Statement dependencies, source, and Lean record
   remain unchanged.

Second reading changed only this report, adding the independent checks and verdicts.
No Lean or DAG repair was necessary. Confirmed holes closed: one, namely
`AlgebraicGeometry.Scheme.ideal_power_annihilator_quasicoherent`; holes added: zero.
