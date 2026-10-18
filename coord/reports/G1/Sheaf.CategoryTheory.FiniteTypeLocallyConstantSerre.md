## What changed

Repaired every point of return C-8a024 (head 8a0248550). The original theorem
`SheafOfModules.finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions`
now has a complete proof of both clauses. Its signature is unchanged byte-for-byte, and
its original six-step proof-plan docstring is retained. The kernel/cokernel and extension
helpers in the item are private, proved lemmas; neither is a deferred obligation.

Added eight proved modules, each with its own node: exact constant module sheafification;
exact restriction to a slice; exact further restriction between slices; local linearity
of finite constant module maps; simultaneous lifting of finite families of sections;
local lifting from constant finite free sheaves; the categorical cokernel presentation
of an extension; and local constant finite presentations of extensions. The extension
proof uses these constructions and then locally linearizes its finite relation map.

All nine Lean files compile through the prescribed server compiler after import pruning.
No existing definition, target signature, or consumer was changed. The only downstream
module is `Sheaf.Paper.NilpotentReductionLissity`; it imports the same unchanged interface.
Change record: `coord/changes/finiteTypeLocallyConstantSerre.md`.

Repair of the returned delivery removed the duplicate preservation declarations from
`FiniteTypeExtensionLocalPresentation` and the matching duplicates from this item.
The modules now reuse the landed `strictPerfectConstantSheaf_exact` and `overFunctor_exact`
results through local instances, so no statement is redeclared.

## Proved and sorry left

Closed the original single hole:
`SheafOfModules.finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions`
(node `lem-weil-pbc-locally-constant-derived-serre`). The two public clause obligations of
the returned delivery have been replaced by actual private proofs, not renamed holes.

Also proved, with no holes:

- `SheafOfModules.strictPerfectConstantSheaf_exact`.
- `SheafOfModules.overFunctor_exact`.
- `SheafOfModules.overMap_exact`.
- `SheafOfModules.exists_cover_constant_linearMap`.
- `SheafOfModules.exists_cover_lift_finite_sections`.
- `SheafOfModules.exists_cover_lift_constant_finite_free`.
- `CategoryTheory.exists_cokernel_presentation_of_lift`.
- `SheafOfModules.exists_cover_constant_presentation`.

Actual holes left in the item: **0**. Holes added elsewhere: **0**. Split-off
obligations: **0**. This is a proof of the original obligation from existing library
statements, rather than a decomposition into new holes. Existing pending coefficient
package results, including its finite-free comparison, are used as the stage permits;
this delivery does not claim to close those separate obligations.

The proofs cover the empty site, covering by an empty sieve, the zero ring, and rank-zero
finite free modules. The lifting lemma also allows an empty index family. The extension
argument constructs a cokernel presentation and never assumes that the extension splits.

## No longer needed

Discarded the two unlanded relabelling nodes
`lem-weil-pbc-locally-constant-derived-serre-kernel-cokernel` and
`lem-weil-pbc-locally-constant-derived-serre-extension`. Neither file is delivered.

Removed the following direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Sheaf.Paper.ConstantModuleSectionProperties`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`.
- `Mathlib.CategoryTheory.Sites.EpiMono`.
- `Mathlib.CategoryTheory.Sites.CoverLifting`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`.

The ordinary coefficient-valued constant-section exactness theorem
`lem-weil-pbc-constant-module-section-properties` is unnecessary: the new exactness lemma
works directly with the actual ringed module-sheaf functor. The ordinary constant-map
and constant-restriction declarations
`lem-weil-pbc-site-constant-morphism-local` and
`lem-weil-pbc-site-constant-restriction` are also unused; their replacements use the actual
ringed local Hom and successive module-restriction isomorphisms.
The broad theorem `lem-weil-pbc-module-sheaves-colimits-forgetful` is unnecessary; the
finite preservation instances proved in the existing module-sheafification support file
suffice. Its retired alias module is unnecessary as well.

The source module `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`
remains a transitive import of exact slice restriction for its colimit-preservation
instance, not for either pruned constant-map/restriction declaration.
`Mathlib.CategoryTheory.Sites.EpiMono` remains genuinely used by the finite-section
lifting module. The site and sheafification definition nodes remain transitive
mathematical dependencies through the new helpers. No global pruning of those is claimed.

The unused direct `FiniteSectionsEpiLift` import was removed from the item after its
use moved into `ConstantFiniteFreeLocalLift`. New modules likewise retain only needed
imports; for example further restriction imports `Sites.Abelian` directly instead of
obtaining its instance through `ConstantSheafOver`.

## Where the brief, the DAG or earlier work was wrong

The returned conjunction proof only relabelled its two clauses and was not a reduction.
This repair supplies actual proofs of both clauses and of every new supporting theorem.
The old report's claim that the two clause holes were a useful decomposition was wrong.
The original plan has six steps, not five as that report claimed.

The existing generic constant-sheaf map and section lemmas use ordinary coefficient
categories, while the goal uses ringed module sheaves. The proved bridge to the existing
ringed constant-Hom theorem and exactness of module sheafification supply the precise
interfaces required here. No statement was found false and no statement was weakened.

Return point 5 is addressed: neither of its unused proof imports remains in the item;
`Opposite` was removed from its `open` list; the section variables are now used throughout
the actual private proofs. The sheafification support and ringed local-Hom imports are
used inside the new supporting modules where they are needed.

The return point about duplicate statements is therefore resolved; the duplicate check and
the warning-free compilation both pass.

## New nodes

`lem-weil-pbc-finite-type-constant-exact`: exactness of the actual constant module functor.

`lem-weil-pbc-finite-type-restriction-exact`: exactness of restriction to a slice.

`lem-weil-pbc-finite-type-restriction-map-exact`: exactness of further slice restriction.

`lem-weil-pbc-finite-type-constant-local-linear`: local linearity for a finite constant
source over a Noetherian ring, using the existing local-Hom surjectivity theorem.

`lem-weil-pbc-finite-sections-epi-lift`: a common covering on which a finite family lifts.

`lem-weil-pbc-constant-finite-free-local-lift`: morphism lifting from constant finite free
sheaves, via the finite biproduct universal property.

`lem-weil-pbc-extension-cokernel-presentation`: the categorical kernel/cokernel argument
for a lifted quotient presentation, with its signs and uniqueness checked in Lean.

`lem-weil-pbc-finite-type-extension-local-presentation`: construction of a local finite
constant-module presentation before local linearity is applied to its relation map.

All eight nodes have complete proofs, source citations, actual Mathlib search records,
and Lean attachments. None leaves a follow-up proof obligation. The existing parent
node's proof steps and dependencies follow the compiled proof. Change record:
`coord/changes/finiteTypeLocallyConstantSerre.md`.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
