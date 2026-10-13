## What changed

Repair of the landing return: removed the private generic theorem
`AlgebraicGeometry.restriction_naturality`, whose statement duplicated the
private `AlgebraicGeometry.mate_naturality` in
`Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisComparisons`. That existing
theorem is private, so importing its module cannot expose it. Instead,
`mv_comm₂` now assembles the scheme restriction maps as a local natural
transformation and applies Mathlib's existing `NatTrans.naturality` directly
at the two inclusions. No replacement generic naturality theorem is declared.
The component formulas reduce using `Adjunction.homEquiv_unit`. No imports,
public signatures, or other proof bodies changed during this repair.
The previous second reading is superseded by this repair; a new independent
reading is required before delivery.


Proved `AlgebraicGeometry.schemeDerived_mayerVietoris_naturality` in
`Sheaf.AlgebraicGeometry.DerivedMayerVietorisFunctorial` with its existing signature.
The proof constructs the boundary from the concrete Mayer--Vietoris short exact
complex, explicit open-image comparisons, and a K-injective resolution with
injective terms. Every derived morphism is represented by a chain map between
these resolutions. Mathlib's short-exact-sequence boundary naturality supplies
the third square; adjunction naturality supplies the first two. The proof then
constructs the triangle morphism and verifies all three components.

All helpers are private and proved, including the representative boundary
construction. It chooses no arbitrary object from a holed existence statement:
the complex resolution and comparisons are existing explicit constructions.
The four new proof imports are KInjectiveMayerVietorisExact,
OpenImageComplexComparisonUnit, OpenImageComplexComparisonRestriction, and
WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective.
The node's first proof step records the implemented route. The remaining two
steps retain the direct-image proof plan. Public imports, both theorem
signatures, and the unit record are unchanged; no forced adaptations.

## Proved and sorry left

Closed: `AlgebraicGeometry.schemeDerived_mayerVietoris_naturality`
(node `lem-pc-derived-mayer-vietoris-functorial`). This is a completed proof
from existing library declarations, not a decomposition into new holed lemmas.

Remaining: `AlgebraicGeometry.schemeDerived_mayerVietoris_directImage`
(same node). Its body is unchanged, exactly `by sorry`.

Holes closed: 1 of 2. Holes added: 0. New nodes: 0.
The helpers have no local sorry, and no existing signature changes. The axiom audit
shows `sorryAx` in the representative boundary and the closed naturality theorem
through existing imported dependencies; this closes the local hole, not every
upstream obligation. The other private naturality helpers use only `propext`,
`Classical.choice`, and `Quot.sound`. Local compilation
passes without warnings; lines are at most 100 characters. Empty opens, repeated
opens, the zero complex, and non-quasi-coherent objects require no special cases:
the first proof uses no compactness or quasi-coherence assumption. The existing
hypotheses remain in its signature.

## No longer needed

The duplicate private helper `restriction_naturality` is removed entirely;
its two uses are replaced by applications of `NatTrans.naturality`. The
private theorem in `KInjectiveMayerVietorisComparisons` is not re-declared,
renamed, or accessed through its generated private name.


Removed direct proof imports:
- `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageSplitTriangle`
- `Sheaf.AlgebraicGeometry.InjectiveRestrictionSurjective`
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`

The first proof does not use the pointwise existential theorem
`schemeDerived_mayerVietoris_triangle` or the existential presentation theorem
`schemeKInjective_mayerVietoris_presentation`; it uses the concrete sequence
and explicit comparisons. Their modules remain in the public/transitive closure,
so this delivery claims no whole-module removal from the targets' closure.
Old `proof_deps` removed: `lem-pc-derived-mayer-vietoris-triangle` and
`lem-sc-ringed-space-injective-restriction-surjective`. The former existential
triangle theorem is bypassed by the concrete short exact triangle construction;
the latter is used inside the exactness dependency rather than directly here.
Neither removal claims its module is pruned from the targets import closure.
No import was removed from the public interface. The restriction, resolution,
and surjectivity theory remains reachable through the proved dependencies.
The split-triangle and composition theory remains part of the unresolved
second theorem's plan; it is not asserted mathematically unnecessary there.

## Where the brief, the DAG or earlier work was wrong

The first delivery missed the duplicate private mate-naturality statement.
The landing return correctly identified that duplication. Reuse by import
is unavailable because the matching declaration is private; the repair uses
the existing Mathlib naturality API without stating that fact again.


No mathematical statement was changed. The existential comparison theorem
alone does not give simultaneous natural choices; the explicit
`schemeOpenModuleImageComplexComparison` construction does. Its naturality is
proved here from right-derived-unit naturality, rather than assumed for
arbitrary existential witnesses.

The second theorem remains open. Its displayed comparisons are
`Classical.choice` of bare `Nonempty` natural-isomorphism statements. The
current composition proof obtains an isomorphism from a theorem carrying a
right-derived-unit equation, but its exported scheme-level `Nonempty` theorem
forgets that equation. Consequently that equation cannot immediately be
applied to the chosen isomorphism in the second theorem. The same care is
needed for open-restriction compatibility. This is a remaining interface
problem, not a counterexample or a proposed weakening. No replacement
compatibility assertion was postulated.

The local checkout contains literature lists but not the Stacks source files.
The original construction was checked on the public Stacks pages for
[Tag 08BV](https://stacks.math.columbia.edu/tag/08BV),
[Tag 08FE](https://stacks.math.columbia.edu/tag/08FE), and
[Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T).

## Second reading by B2

Independent second reader, 2026-10-13, after the landing-return repair.

1. **Interface preservation: PASS.** Read the complete module and its diff against
   the repository. Compared both existing theorem signatures byte for byte through
   `:= by`; both are identical. The complete direct-image declaration and its
   suffix are identical. All four public imports and existing docstrings are
   unchanged. The added helpers are private; there are no adapted modules,
   public definitions, new public statements, or change records.

2. **Proof and construction: PASS, with existing upstream holes.** Compiled the
   delivered module locally with lcompile.py: exit 0, no warnings, 42.4 seconds.
   Rebuilt a scratch copy of the current repaired module and printed axioms for
   all eleven declarations (the nine private declarations and two public
   theorems). The six helpers derived_map_surjective, computation_naturality,
   open_comparison_naturality, concrete_map, mv_comm₁, and mv_comm₂ use only
   propext, Classical.choice, and Quot.sound. The representative boundary,
   its naturality and distinguishedness proofs, and the public naturality
   theorem additionally use sorryAx through existing imported obligations.
   The direct-image theorem retains its original sorry. There is precisely one
   local sorry, no forbidden declaration mechanism, and no hollow definition.
   Read the K-injective resolution construction: it is the functorial
   factorization construction, not an arbitrary choice from a holed existence
   theorem. Read the open-image comparison definition: it composes the
   K-injective computation, exact-restriction comparison, and the uniquely
   normalized right-adjoint comparison. representativeBoundary uses that
   explicit isomorphism and the concrete triangleOfSESδ. The temporary chain
   map witness is used only to prove the equality for an already defined
   boundary; it supplies no arbitrary data to a definition.

3. **Split-off statements and edge cases: PASS.** No statement was split off,
   no hole was added, and no new node needs a source/search/docstring audit.
   Read every private helper and checked its hypotheses against its uses.
   concrete_map is the actual morphism of short exact complexes, with the
   negative V restriction preserved. Empty opens, U=V, the zero complex, and
   zero or identity morphisms satisfy the same componentwise equations; no
   nonempty-open or disjointness hypothesis is hidden. The intersection
   comparison works for supplied adjunctions, without choosing arbitrary
   existential comparison witnesses. The direct-image interface issue remains
   accurately reported rather than replaced by a new compatibility hole.

4. **Shortest route and pruning: PASS.** Searched the library and Mathlib for
   morphism-lifting, comparison-naturality, and short-exact-triangle APIs,
   including a fresh msearch grep for Q_map_surjective. The proof already uses
   Qh_map_bijective plus homotopy quotient fullness, right-derived-unit
   naturality, and triangleOfSESδ_naturality. The pointwise existential
   triangle/presentation cannot alone provide simultaneous natural boundary
   choices. In particular, mv_comm₂ now assembles a local natural transformation
   and uses NatTrans.naturality; it does not redeclare the private
   mate_naturality in KInjectiveMayerVietorisComparisons. All four added proof
   imports supply used declarations or instances. Checked the six removed
   direct imports and both removed old proof_deps against the report. Their
   transitive roles and the unproved direct-image plan are distinguished from
   actual pruning: no whole module is claimed removed from the target closure.
   Read dag/units/sk-thm-picard-semicon.json: its realized record is unchanged,
   and this lower-level construction bypasses no realized unit step.

5. **DAG agreement: PASS.** Only proof, proof_deps, and proof_origin differ in
   the existing node; its statement and Lean record are unchanged. The union
   of all proof-step uses equals proof_deps exactly. The implemented first
   step describes the explicit boundary, its distinguishedness, lifting of
   derived morphisms, and all three squares. The remaining two steps are
   explicitly retained as the unresolved direct-image plan. No node falsely
   records that second clause as proved.

**Changes by this second reader:** corrected the stale scratch axiom audit by
regenerating it from the repaired module and removing its reference to deleted
restriction_naturality. Added this independent review. No delivered Lean or DAG
repair was needed. Verified local accounting remains one hole closed
(AlgebraicGeometry.schemeDerived_mayerVietoris_naturality), zero holes added,
one original hole left (AlgebraicGeometry.schemeDerived_mayerVietoris_directImage),
and zero split-off statements.
