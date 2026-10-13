## What changed

Completed the formal descent proofs of `moduleCup_coefficient_naturality` and
`moduleCup_pullback_naturality` in `Sheaf.Paper.CechCupPullbackCompat`, without changing
any existing signature, definition, visibility, or statement. The main compatibility
theorem and the four existing Cech naturality proofs are retained.

Added two proof-only imports, `Sheaf.Paper.ModuleCupCoefficientResolutionMaps` and
`Sheaf.Paper.ModuleCupPullbackResolutionMaps`. Each new module states one lower
resolution-construction theorem, with a complete source-based construction proof in
its docstring and a corresponding new node. Updated the parent node's proof and
proof dependencies to record both reductions.

Proved private helpers for surjectivity of the computing resolution class maps,
existence of the cup of two cycles by Leibniz, and transport of cycles through
additive differential-compatible maps. The two naturality proofs lift arbitrary
classes, construct their paired cycle, transport all three cycles, verify the
pairing equation at the cochain level, and apply the two existing
`IsModuleCupProduct` characterizations. The coefficient proof uses actual cochain
maps and the existing `map_cycle` helper; the cross-scheme proof uses additive
global-section maps, avoiding any assumption that the scalar rings agree.

## Proved and sorry left

Closed the two original holes, by complete proofs from the new named statements:

- `AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality`.
- `AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality`.

No `sorry` remains in the assigned module. Added precisely two lower holes:

- `AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_resolution_maps`, node
  `lem-sc-module-cup-coefficient-resolution-maps`, in
  `Sheaf.Paper.ModuleCupCoefficientResolutionMaps`.
- `AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_resolution_maps`, node
  `lem-sc-module-cup-pullback-resolution-maps`, in
  `Sheaf.Paper.ModuleCupPullbackResolutionMaps`.

This is a decomposition: two upper holes closed and two lower construction holes
added, with net zero hole reduction. Both lower statements describe simultaneous
computing resolution maps and their sectionwise tensor equations independently of
any chosen cup products on cohomology. They assert no equality between cup products
and cannot replace either original conclusion without the proved cycle/descent
argument. No arbitrary witness from either existence theorem enters a definition;
the witnesses are eliminated only inside theorem proofs. The new private cycle
construction explicitly builds the kernel element from its prescribed section.

## No longer needed

None. All original imports and proof-dependency nodes are still needed by the
existing compatibility and Cech naturality proofs or by their public signatures.
No unit route is bypassed. No new Godement implementation module is imported into
the assigned module: only the two resolution-construction interfaces are imported.

## Where the brief, the DAG or earlier work was wrong

The earlier abandonment correctly identified missing simultaneous resolution-map
interfaces, but incorrectly treated their absence as an obstacle to delivery.
The current library already proves the main compatibility theorem and all four
Cech naturality declarations; only the two sheaf-cup naturalities were holes.
The two missing interfaces are now precise Lean statements, and the full remaining
passage from cochain pairings to cohomological naturality is compiled Lean.

The new statements were checked on zero maps, zero sheaves, empty schemes,
identity pullback, and degree zero: the functorial Godement construction, additive
maps, and canonical tensor comparison handle these cases without extra hypotheses.
In particular, no flatness of the scheme morphism is needed, and the cross-scheme
statement does not silently identify the rings of global sections.

Mathlib searches found homology functoriality and injective-comparison naturality,
but no simultaneous computing resolution theorem for these pairings. LeanSearch
was unavailable; its failed request and the successful semantic and source searches
are recorded. The local literature tree lacks the cited cohomology.tex, so the
source arguments were read at the official Stacks pages for Tags 0FKU, 0FKV and
01FD. The new nodes name these precise sources.

No forced adaptations and no change record are needed: this delivery changes no
existing public interface and adapts no other held module.

## New nodes

`lem-sc-module-cup-coefficient-resolution-maps` provides compatible coefficient
chain maps between two computing tensor pairings, their class-map equations, and
the section pairing equation for every open and bidegree. Its source is the
functorial Godement construction and the naive cup discussion in Sections 20.30
and 20.31 (Tags 0FKR and 0FKU). Its statement includes no chosen cup product.

`lem-sc-module-cup-pullback-resolution-maps` provides additive global degree maps
between computing tensor pairings on two schemes, with adjacent differential,
class-map, and pairing equations. Its target class equation explicitly includes
the canonical tensor-pullback comparison. Its source is the same Godement/naive
pairing construction, the adjunction description of the relative cup product,
and the resolution comparison over the unit in Tag 01FD. Its statement includes
no chosen cup product. Both inherit the parent's chapter and unit and record the
actual Mathlib searches; blueprint search found no matching imported node.

## Second reading by U1

1. **Declarations and interfaces.** I diffed the delivered `CechCupPullbackCompat` module against the repository version. All pre-existing signatures, definition bodies, visibility, and already completed proofs are unchanged; only the two original theorem proofs changed, with new private helpers and proof-only imports. The two new theorem signatures match their `lean.statement` records byte for byte. The existing node's changed proof and `proof_deps` match the declarations used by the Lean proof.

2. **Compilation and trust.** I compiled all three delivered modules with `lcompile.py --all`; they compile without errors or warnings. There are no `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `sorry` occurrences in the delivered source except the two named split-off theorem proofs. An axiom probe reports only `sorryAx` through those two split-off theorems (and pre-existing imported holes), together with `propext`, `Classical.choice`, and `Quot.sound`.

3. **Statements and reductions.** I checked the new statements on zero maps, zero modules, empty schemes, identity pullback, and degree zero. They assert only resolution-level chain maps, cycle/class equations, and the section pairing equation; they do not assume or restate a cohomological cup product. The two upper proofs genuinely use the lower statements together with explicit surjectivity, Leibniz cycle construction, cycle transport, and the two `IsModuleCupProduct` characterizations. The coefficient and pullback statements are strictly lower than the naturality conclusions.

4. **Sources and shortest route.** I checked the source route against Stacks Tags 0FKR, 0FKU, 01FD, 01FB, 01F8, and 01EZ. The coefficient proof follows functorial Godement resolutions and Alexander--Whitney naturality. The pullback proof uses the adjunction unit and the canonical tensor comparison. I repaired the pullback node's prose to avoid the false claim that pushforward preserves injective modules: it uses flasque pushforward and an injective replacement on the base, as in the Stacks functoriality construction. Mathlib and local searches found no existing simultaneous resolution-map theorem. All original imports remain needed by existing declarations or the new proof; no import or unit-route node was pruned.

5. **DAG and unit route.** The two new node records have complete source, proof, dependency, search, creation, blueprint, chapter, unit, and Lean attachment fields. Their `proof_deps` are exactly the union of their proof-step uses. The parent node records the two new proof steps and dependencies. The unit route remains `sk-prop-av-cube`; no chapter or unit statement was bypassed.

I changed only the new pullback theorem docstring and both new nodes' DAG proof text to correct the cross-scheme injective-resolution explanation, and added this second-reading report. No signatures, definitions, imports, or public visibility were otherwise changed.
