## What changed

Replaced the hole in `CategoryTheory.TwistedActionRingedSite.setRestriction` by an
explicit restriction functor and a proof that this functor is full, faithful and
essentially surjective. The statement and its public import are unchanged.

The restriction functor takes the inverse of the minus-one restriction map as
its fixed-pair structure. The generator is invertible because its composites
with an explicit degree-one arrow are images of base isomorphisms. The proof
also derives the necessary naturality from the supplied arrow-composition and
identity equations; no normalization of `powerComp` is assumed without proof.

Full faithfulness is proved directly. A property of arrows closed under
composition and inversion, containing base arrows and the minus-one generators,
contains every arrow. The proof handles degree one by inversion, combines any
two degrees using `powerComp`, and uses integer induction. Applied to naturality,
this extends an intertwiner uniquely to a morphism on the copied-object site.
Object-copy transports use only `Site.inclusion_obj`.

Essential surjectivity uses two separate new statements: an objectwise
presheaf-extension lemma, with no sheaf condition or functor equivalence, and a
sheaf criterion for an already constructed presheaf, with no extension claim.
The actual Lean proof combines their conclusions, constructs the sheaf and its
pair isomorphism, and finishes with `Functor.asEquivalence`. Forgetting the pair
is definitionally restriction. Its comparison is the identity; the required
generator formula is the inverse identity on sections.

Validation: both new modules compile, and the main module compiles in 7.7 seconds.
Removed unused forward-continuity section-variable bindings from the private
helpers as reported by the delivery linter; the final delivery recompiles them.

## Proved and sorry left

Closed the original textual hole in
`CategoryTheory.TwistedActionRingedSite.setRestriction`
(`lem-sf-twisted-action-set-restriction`) by decomposition. This is not an
unconditional proof or a net decrease of holes: one original hole is replaced
by two strictly narrower holes.

The delivery adds exactly these two holes:

- `CategoryTheory.TwistedActionRingedSite.twistedPresheafExtension`, node
  `lem-sf-twisted-action-presheaf-extension`, in
  `Sheaf.CategoryTheory.TwistedActionPresheafExtension`.
- `CategoryTheory.TwistedActionRingedSite.twistedSheafOfRestriction`, node
  `lem-sf-twisted-action-sheaf-detection`, in
  `Sheaf.CategoryTheory.TwistedActionSheafDetection`.

The item's module has zero remaining holes. All private helpers are proved;
there are no holes in definitions. In particular the restriction functor,
generator invertibility, integer generation, and full faithfulness do not use
either split-off theorem. The two new theorems are used only in the proof of
essential surjectivity. No object is selected by a new definition from either
existence statement; `asEquivalence` supplies the usual inverse of the proved
full, faithful and essentially surjective functor.

## No longer needed

None. No existing import, node, module or unit step is removed. The only original
dependency, `def-sf-twisted-action-presentation-data`, remains necessary. The two
new proof imports are both used. Ringed geometry, the module restriction theorem,
orbit induction, tensor comparisons and internal-Hom comparisons are not needed
by this set restriction proof and were not imported.

## Where the brief, the DAG or earlier work was wrong

There is no statement correction. The sole declared proof dependency originally
provided the data but did not provide either the presheaf extension or the descent
criterion asserted in the prose. The delivery makes these distinct remaining
steps explicit while proving the morphism part and the assembly in Lean. Neither
new theorem restates the requested normalized equivalence.

The empty site, empty section sets, identity equivalence and zero coefficient
ring do not require a new assumption. The presheaf-extension lemma has no
pullback assumption, since it makes no descent assertion; the descent lemma
retains the original pullback assumption. No ring operations enter either
statement or the proved restriction/morphism construction. The unit record
`sk-prop-sf-biduality-general` has no realized statement or step attached to this
support node. Its route is unchanged.

The blueprint-ancestor command reports no imported ancestor for this node.
Searches for twisted action, presheaf extension and twisted sheaf found no
matching blueprint nodes. The new records retain the parent's null ancestor and
its explicit provenance; they do not invent a new reference. Stacks 00W0 remains
motivation for the agent-formulated twisted variant, as in the original item.

## New nodes

`lem-sf-twisted-action-presheaf-extension` states extension of one presheaf with
an invertible translation map to one presheaf on the labelled category, together
with its degree-zero comparison and generator equation. It does not assert
sheaf descent, any functor, any equivalence, or the extension of morphisms.

`lem-sf-twisted-action-sheaf-detection` states that a presheaf on the already
specified labelled category is a sheaf when its degree-zero restriction is a
sheaf. It constructs no presheaf and asserts no action equivalence. Both new
modules contain a single named public theorem with the original step's source,
proof in words, and blueprint tag. The parent node's proof and proof dependencies
are updated to match the Lean argument. No change record is needed because no
existing public interface or other module is changed.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
