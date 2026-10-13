## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.flatBaseChangeRestrictedLift_section_formula`
with a compiling reduction. The original signature, public imports and definitions
are unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.RestrictionResolutionLiftSections`.

The proof separates the two computations that the old node combined. The new
single-map lemma evaluates the restriction-adjunction lift on an arbitrary open U⊆X, with the
resolution comparisons. The item's `squareSections` calculation is proved directly:
evaluate the pushforward square degreewise, simplify the composition comparisons,
and identify the remaining presheaf restriction with the final equality transport.
The main proof then combines the two identities by composition and cancellation of
the source section isomorphism. There is no augmentation hypothesis on t.

Updated the original node's proof and dependencies. Added one module and its node
for the single-map restriction calculation. The previous attempt's unchanged Core
copy was removed from the delivery tree; Core is not modified. Experiments remain
under scratchpad and are not delivery modules.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.Scheme.Modules.flatBaseChangeRestrictedLift_section_formula`
(node `lem-weil-pbc-restricted-lift-section-formula`). Its proof contains no sorry.

One hole added:
`AlgebraicGeometry.Scheme.Modules.restrictionResolutionLift_sections`
(node `lem-weil-restriction-resolution-lift-sections`), in the new module
`Sheaf.AlgebraicGeometry.RestrictionResolutionLiftSections`.
Its proof is exactly `by sorry`. Its docstring records the source and a complete
restriction/unit/counit/naturality calculation. It has no cartesian square,
flatBaseChangeResolutionQ, or projection-open transport. The direct square
calculation and final cancellation are discharged in the item's proof.

This is a decomposition: one upper hole closed and one strictly smaller argument
part left, not a claim of a net decrease in holes or an axiom-free proof. Both
delivery modules compile cleanly using lcompile.py --all. The deliver3.py --no-push
dry run printed OK: compilation and preflight passed except for the second
reading, which is intentionally left to the next worker. Nothing was pushed. The new statement was
checked on identity maps and the empty open: it reduces respectively to restriction
comparison cancellation and equality of maps between zero section groups.

## No longer needed

No existing import, dependency node, or unit step is pruned. All three original
proof dependencies remain needed. The original Core public import remains.
The rejected component restatement module and proposed node from the earlier
attempt are not included, and no dependency on them remains. No additional
proof-only imports were retained beyond the one new restriction lemma module.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's universally quantified degreewise formula was equivalent to
the complete goal and supplied no proper argument part. It is not reused. The
replacement separates an arbitrary single-map restriction-adjunction computation
from the independently proved base-change-square section evaluation. It does not
simply rename the old theorem or apply complex extensionality to a renamed hole.

The original node's single prose step hides these two calculations and the
categorical cancellation. Its route now records them separately. No definition,
existing statement, target signature, or unit route changes. The cited Stacks
texts are absent from this clone's literature directory; their published Tag 01FB
and 01E4 pages were read directly. The additional detailed restriction calculation
is explicitly recorded as agent-written bookkeeping below those results.

## New nodes

`lem-weil-restriction-resolution-lift-sections`: arbitrary scheme map p:Y→X,
open U⊆X, any complex map of resolutions I→p_*J, and restricted-resolution
comparisons on U and p⁻¹U. The explicit adjoint restriction lift, evaluated on
sections and conjugated by those comparisons, equals t(U). This is precisely the
restriction part of the original proof, with no fibre-product square. It inherits
chapter sec-proper-base-change and unit sk-thm-p1. The node includes its full Lean
signature, provenance, source, proof steps and all three kinds of Mathlib searches
(LeanSearch was unavailable). There are no change records or forced adaptations.

## Second reading by W2

1. **Interfaces: pass.** Compared each delivered module with the repository.
   The only existing module changed is FlatBaseChangeRestrictedLiftSectionsFormula:
   one plain proof import, one private evaluation helper, a local heartbeat option,
   and the theorem proof. Verified the existing theorem signature byte for byte.
   No definition, existing public signature, visibility, target, or change record
   is changed. The new restriction lemma's signature matches its new node verbatim.
2. **Proof and axioms: pass as a decomposition.** Independently compiled both
   modules in import order with lcompile.py --all: no errors or warnings. The only
   delivered sorry is the named restrictionResolutionLift_sections theorem.
   There is no forbidden declaration or hollow definition in either file. A scratch
   copy with #print axioms reports exactly propext, Classical.choice, Quot.sound,
   and sorryAx for both public theorems. The original theorem therefore still
   depends on an open theorem; this is not an axiom-free completion. The private
   openSections_map helper is rfl. Read squareSections degreewise: composition
   comparisons cancel, the congruence comparison gives the projection-open equality
   transport, and the final congrArg calculation cancels the source isomorphism.
3. **Split statement: pass.** Read RestrictedResolutionSections.components and
   flatBaseChangeRestrictedLift in Core against the explicit let-expression.
   The specialization is the actual restriction lift, with no extra augmentation
   assumption. The source and target comparisons are supplied isomorphisms, not
   arbitrary data selected from an unproved existence statement. The component
   hypotheses pin their section identifications. Checked the empty open (zero
   section groups), the full open (restriction identification and comparison
   cancellation), identity p (naturality and the same cancellation), and t=0
   (all maps in the formula are zero). The proposed calculation is true and is a
   proper argument part: it omits the pushforward square and the projection-open
   transport, which the parent proof establishes independently. It is not a
   restatement of the parent's complete equality.

   Independent searches used LeanFinder with “Evaluating the adjoint of a sheaf
   map on sections of an open immersion gives the original map”, Loogle with
   “restrictAppIso”, and rg on lean/Sheaf, the upstream algebraic-geometry sources,
   and Mathlib's Modules/Sheaf.lean. Results give restrictAppIso naturality and
   restriction unit/counit component formulas, but no existing resolution-comparison
   identity that closes this statement. Read those formulas and the induced complex
   adjunction. No immediate shorter proof or few-minute closure was found.
   Read [Stacks 01FB](https://stacks.math.columbia.edu/tag/01FB) and
   [Stacks 01E4](https://stacks.math.columbia.edu/tag/01E4): these support the resolution
   and section framework; the explicit restriction-comparison bookkeeping is the
   agent-written calculation recorded by the new node and its complete docstring.
4. **Route and pruning: pass.** The proof starts with a single-map restriction
   identity and independently proves the square evaluation, then uses categorical
   cancellation. All original dependency nodes still supply definitions actually
   used; Core's public import supplies the public statement. The new plain import
   is proof-only. In the new module, OpenChoices, additive adjunctions, and the
   induced complex adjunction are needed by the signature itself, so their public
   imports are appropriate. No import or old proof dependency can be pruned here.
   Read dag/units/sk-thm-p1.json, including realized: this local computation keeps
   the existing unit route and bypasses none of its statement or step realizations.
5. **DAG and report: pass.** Checked both nodes' Lean signatures against the files
   and checked proof_deps against the union of proof-step uses. The parent node
   records the restriction specialization, directly proved square calculation, and
   cancellation in the order used in Lean. Its only changed fields are proof,
   proof_deps and proof_origin. The new node has provenance, source, full signature,
   search records, chapter/unit, and creation/blueprint records. The report correctly
   records one original hole closed and one new, strictly smaller hole added: net
   zero, a decomposition. No pruning is claimed.

Changes from the second reading: added this independent review and its verification
and search evidence to report.md. No Lean proof, statement, import, or DAG repair
was needed. The axiom-check scratch copy is outside the delivery modules.
