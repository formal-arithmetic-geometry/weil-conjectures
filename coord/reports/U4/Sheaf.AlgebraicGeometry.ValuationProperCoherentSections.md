## What changed

Proved `AlgebraicGeometry.Scheme.Modules.finitePresentation_moduleCohomology_zero_of_valuationRing`
in `Sheaf.AlgebraicGeometry.ValuationProperCoherentSections` without changing its signature.
Added the proof-only import `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`.
Its proved `IsInvertible.sheafOfModules_isInvertible` comparison converts the scheme
invertibility hypothesis to the sheaf-of-modules notion. The proved
`SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one` supplies constant rank one.
The existing `finitePresentation_moduleCohomology_of_valuationRing` then applies with
rank one and cohomological degree zero. This implements the existing two-step DAG plan.

Local single-file compilation passed without warnings (3.6 seconds). No definitions,
existing statements, public imports, or other modules changed. The unit route is unchanged.

## Proved and sorry left

Closed one local hole:
`AlgebraicGeometry.Scheme.Modules.finitePresentation_moduleCohomology_zero_of_valuationRing`
(node `lem-sc-valuation-proper-coherent-sections`). There are no sorries left in the
item and no new holes or intermediate statements added.

The proof uses the existing, still unproved
`AlgebraicGeometry.Scheme.Modules.finitePresentation_moduleCohomology_of_valuationRing`
(node `lem-sc-valuation-proper-coherent-higher-direct-images`) as intended by stage 3.
Thus this delivery closes the item's hole from its stated dependency; it does not claim
that its transitive axiom closure is already sorry-free.

## No longer needed

None. All original imports are retained: the public imports supply the unchanged
statement, and the proof imports supply the higher-cohomology theorem and the
rank-one characterization. No planned dependency node or module is bypassed.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is correct. Its first step needs an explicit bridge between
`Scheme.Modules.IsInvertible` and `SheafOfModules.IsInvertible`, because these are
distinct Lean classes. The source library already proves this bridge in
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula`; no new lemma is needed.
The recorded unit source file is not present on this machine; its full statement,
step and realization record are available in `dag/units/sk-prop-av-cube.json` and
were checked. The proof follows the existing dependency route and does not alter the unit.

## Second reading by U4

1. **Interface preservation: pass.** Compared the only delivered Lean module with the
   repository using `diff -u`. The only differences are one plain proof import and the
   replacement of the theorem's `sorry` by its proof. The declaration signature and
   docstring are byte for byte unchanged; no definitions, public imports, new declarations,
   change records, or other modules are delivered.
2. **Proof and axioms: pass.** Independently compiled the delivered file with `lcompile.py`
   without errors or warnings. A temporary scratch copy with `#print axioms` shows that
   `finitePresentation_moduleCohomology_zero_of_valuationRing` uses exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`, as expected from the existing open
   higher-cohomology theorem. Both comparison lemmas individually use only the three
   permitted standard axioms. The delivered module contains no `sorry`, forbidden
   declaration, or data construction from an unproved existence theorem.
3. **Split statements: pass (none).** No statements or holes are split off. Read the two
   existing comparison proofs: the first converts local structure-sheaf trivializations,
   and the second identifies a singleton basis with rank one. Specializing the existing
   cohomology theorem to `d = 1` and `q = 0` preserves every hypothesis and the exact scalar
   action. Empty schemes and field valuation rings require no exceptional argument.
4. **Shortest route and pruning: pass.** Independent Lean Finder search for finitely
   presented sections of a line bundle over a proper flat scheme over a valuation domain,
   Loogle search for `moduleCohomology`, and `rg` searches of Mathlib, upstream cohomology,
   upstream invertible sections, and `lean/Sheaf` found no shorter applicable theorem.
   Upstream affine-section finiteness requires an affine open, and the proper-direct-image
   finiteness theorem requires a locally noetherian base; neither covers this statement.
   Each proof import supplies a declaration explicitly used. Public imports supply the
   preserved interface. All three old proof dependencies remain used, so `No longer
   needed: None` is complete. The unit's theorem-of-the-cube route is preserved. Its
   `realized.statement` and sole `realized.steps` entry are already empty in the repository;
   this delivery neither fills nor changes those existing records.
5. **DAG agreement: pass.** Read `lem-sc-valuation-proper-coherent-sections` alongside
   the proof. Step one is precisely the invertibility-to-rank-one conversion; step two is
   the degree-zero specialization of `lem-sc-valuation-proper-coherent-higher-direct-images`.
   The existing `proof`, `proof_deps`, and document `proof_origin` therefore need no edit.
   No new nodes are required.

Second reading changed only this report, adding the independent verification and making
explicit the pre-existing empty unit realization entries. The Lean proof is correct as
written and was retained. Holes closed: the one declaration listed above. Holes added: none.
