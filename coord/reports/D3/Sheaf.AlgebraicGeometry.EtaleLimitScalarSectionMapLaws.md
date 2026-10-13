## What changed

Proved `AlgebraicGeometry.Etale.etale_limit_scalar_section_map_laws` in
`Sheaf.AlgebraicGeometry.EtaleLimitScalarSectionMapLaws`, with its existing signature,
visibility and docstring unchanged. All three clauses are proved: identity of the
stage maps, composition of stage maps, and compatibility with the cocone legs.

Seven private, fully proved helpers carry the categorical calculations: transpose
composition, evaluation on sections, uniqueness of pullback pasting, the identity
unit calculation, abstract reflexive functor transport, abstract equality
transport, and the identity calculation for a morphism equal to an identity.
The existing inverse-image unit coherence lemmas and Mathlib pullback uniqueness
suffice. The cocone calculation substitutes `hG` and `L.w` and reuses the section
composition calculation. The proof does not require continuity, finiteness,
directedness, or a limit property. In particular it also covers zero sheaves and
empty etale objects. No data construction, public signature or other module changed.

Updated the existing node's `proof`, `proof_deps` and `proof_origin` to describe the
actual argument. The unit's realized statements and steps are untouched.
The original public import is retained; the experimental proof import of Coherence
was removed because TopologicalInvariance already publicly imports it.

Searches: LeanFinder found pullback-adjunction identity/composition lemmas for over
categories, not this varying-sheaf statement. Loogle did not index the project's
`upperStarComp_hom_app_unit_app`. The launcher grep search found
`MorphismProperty.Over.pullbackComp_left_fst_fst`; local searches and signature reads
found both needed unit coherence equations in the existing Coherence module.

Validation: the complete module compiles without warnings through `lcompile.py`
in about five seconds, with no `sorry` and no increased heartbeat limit.
The delivery dry run performs the declaration/axiom checks and preflight.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.etale_limit_scalar_section_map_laws`
(node `lem-weil-pbc-etale-limit-scalar-section-map-laws`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the item's module, and no
new modules or sorried declarations are added. This is a proof, not a decomposition.
All seven private helpers are proved.

## No longer needed

The node `lem-weil-pbc-cartesian-square-pasting` is not used by this proof: it is
removed from this item's proof dependencies. Direct pullback uniqueness and
`MorphismProperty.Over.pullbackComp_left_fst_fst` supply the needed projection
calculation. This is pruning of the item's route; it does not assert that another
target branch cannot need that node. It is a Mathlib leaf, so there is no separate
Sheaf module to remove.

No original import was removed. The experimental
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence` proof import was removed
as redundant with the original public import. No additional modules are needed.
The fibre-product definition and inverse-image composition node remain needed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The DAG's general cartesian-square pasting
lemma is unnecessary for these particular supplied comparison maps, which are
identified by their two projections.

Direct dependent rewriting of identity scheme morphisms through the inverse-image
construction triggered expensive kernel unfolding of sheafification. The final
proof performs equality elimination with abstract functors and applies the section
expression as a function of the underlying preorder morphism. This preserves every
statement and definition and avoids the expensive unfolding. No compiler/tool
workaround, new axiom, higher heartbeat setting or forced adaptation is used.

## Second reading by D3

1. **Interface preservation — pass.** Read the full module and its repository diff.
   The existing theorem signature is byte-for-byte identical (also checked by
   extracting the text before its proof). Its docstring, visibility, original
   public import and all existing definitions are unchanged. The only Lean changes
   are seven private proved helpers and the replacement of the original `sorry`.
   There are no other delivered modules or change records.
2. **Proof and axioms — pass.** Independently compiled the complete delivered module
   using `lcompile.py`: exit 0, no warnings, 4.8 seconds. Compiled a scratch copy
   with `#print axioms` for the main theorem and each of the seven private helpers:
   every list is exactly `propext`, `Classical.choice`, `Quot.sound`, without
   `sorryAx`. Scanned for forbidden declarations and kernel-check bypasses; none
   occurs. The three local backward elaboration options affect elaboration only.
   No data is selected from an existence theorem and there are no hollow definitions.
3. **Split-off statements — pass, none.** No new hole or public statement is added.
   Read every private helper: transposition uses unit coherence and naturality;
   section evaluation uses contravariant functoriality; geometric pasting compares
   both pullback projections and cancels isomorphisms. Identity transport performs
   equality elimination with abstract functors, then applies the genuine identity
   unit law. None of these helpers restates the full item. Their universal proofs
   do not require a nonempty etale object or a nonzero sheaf. A singleton index
   leaves precisely the proved identity law; no directedness or finiteness enters.
4. **Route, imports and pruning — pass.** Searched the library for related section
   comparison and adjunction-transposition results and searched Mathlib for
   composite hom-equivalence and pullback comparison results. Read
   `PullbackSectionsDiagram`, `AffineFreeEtaleModuleEventualHomLift` and the unit
   coherence equations. The related private results concern fixed sheaves or
   module coefficients and cannot replace the varying-sheaf calculation here.
   The proof uses the existing coherence equations and direct Mathlib pullback
   uniqueness without additional imports. The original public import supplies
   signature dependencies and retains the original module interface. The sole
   old proof dependency omitted is `lem-weil-pbc-cartesian-square-pasting`, already
   recorded under `## No longer needed`; it is a Mathlib leaf, not a removed module.
   Read `dag/units/sk-thm-p1.json`: its realized statement and all four realized
   steps remain unchanged, and this pruning is below the unit level.
5. **DAG agreement — pass.** Compared the existing node JSON with the sandbox:
   only `proof`, `proof_deps` and `proof_origin` differ. The four revised proof
   steps match projection uniqueness, identity, composition and the cocone
   calculation in Lean. The dependency list is exactly the union of their `uses`.
   No new nodes require validation.

Second reading changed only this report, adding the independent checks and
verdicts above. No Lean or DAG repair was necessary. The original hole is closed
without adding any hole: proved 1 of 1, split off 0.
