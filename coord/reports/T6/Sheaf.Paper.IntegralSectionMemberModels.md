## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.integralSectionMemberModels` by a
complete assembly proof from two separate comparison statements and the existing,
proved `continuousScalarFinitePresentation` classification. No existing statement,
definition, visibility, or public import changed.

Finite presentation transfers across `ULift.ringEquiv` by a proved private helper:
the scalar ring is free of rank one over the other ring, and finite presentation
is transitive along the scalar tower. The private point-pullback compositor uses
`Functor.mapModCompIso`, `upperStarFromPointComp`, and the unit of the coefficient
restriction equivalence. The reverse direction also uses the proved scalar-restriction
round-trip isomorphism.

Private functor wrappers give point models and pullbacks the same declared module
categories. Their predicate, pullback, and comparison APIs are proved. These wrappers
contain the actual functor constructions, with no chosen witnesses or holes. The
continuous scalar functor similarly scopes the normed-field instance inside its
construction, keeping geometric functors on the original field instance. Explicit
composition fixes the middle scheme to S and preserves the morphism U.hom followed
by g. The proof uses literal functor expressions at the comparison interfaces to
avoid expensive kernel normalization of definitionally equal presentations.

Added `IntegralSectionScalarModels` and `IntegralSectionLocalIsomorphisms`, each with
one comparison statement, source, complete proof in words, and matching DAG node.
Updated the item's proof steps, proof dependencies and proof origin to match Lean.
The experimental edits to other modules and all debugging probes were removed.

## Proved and sorry left

Closed the original named hole:
`AlgebraicGeometry.ProEtale.integralSectionMemberModels`
(`lem-sfb-integral-section-member-models`). Its assembly proof and every private
helper are complete. The item's module contains zero `sorry` occurrences.

Added exactly two holes, each a named public theorem in its own new module:

- `AlgebraicGeometry.ProEtale.integralSectionScalarModels`
  (`lem-sfb-integral-section-scalar-models`): comparison of the two realizations of a
  finitely presented ordinary scalar module on X. It has no arbitrary internal
  module, morphism g, slice member U, or local-model existential.
- `AlgebraicGeometry.ProEtale.integralSectionLocalIsomorphisms`
  (`lem-sfb-integral-section-local-isomorphisms`): transport and reflection of local
  isomorphisms between arbitrary pairs of internal modules. It has no scalar-model
  witness or finite-presentation conclusion.

This is a decomposition: one original hole closed and two strictly separate
comparison obligations added. No hole is hidden in a definition or private lemma.
The existing scalar classification is used as proved.

Validation: the final `lcompile.py --all` accepted all three modules without errors or
warnings: local isomorphisms 39.8 s, scalar models 42.7 s, and the item 49.3 s.
Each file is below 60 s. This check used the original shared definitions; the
experimental alias change and all debugging files and options were absent.

## No longer needed

No original import, node, or module is withdrawn. Both comparison dependencies named
by the original DAG plan remain needed. Scalar-matrix classification needs no further
split, since `Sheaf.Paper.ContinuousScalarFinitePresentation` already proves it.

The point compositor needs no new Stalk or Coherence import: its proved components
are available through the original public imports. The new local-isomorphism module
does not need `IntegralStratifiedPerfectModels`, since its statement has no constant
scalar model. No source-library declaration is removed or changed. The unit route is
preserved.

## Where the brief, the DAG or earlier work was wrong

The item's sole proof step cited `lem-sfb-integral-section-scalar-models` and
`lem-sfb-integral-section-local-isomorphisms`, but neither node nor corresponding Lean
declaration existed in the shared repository. This contradicts the brief's assertion
that every assigned proof dependency is already declared. This packet states those
actual comparison steps explicitly and proves the item from them and the existing
finite-presentation classification. Neither new statement renames the original
model-existence equivalence.

`blueprint_refs.py ancestor lem-sfb-integral-section-member-models` reports None:
legacy `created.item` metadata ends at a module identifier. Following the existing
`blueprint.from` links recovers the imported ancestor
`lem-sfb-dc-lower-star-preserves`. Both new nodes record that ancestor, the three
intervening nodes, and the integral paragraph and coefficient-bridge step they serve.
Existing nodes' ancestor metadata is unchanged.

Kernel profiling identified expensive conversion at the concrete point-model
interfaces. The proved private functor APIs and explicit composition avoid those
conversions; no limit was raised and transparency remains enabled. No launcher or
source-library file was modified.

Edge cases were checked: zero modules and zero ranks use empty finite presentations;
torsion is permitted; empty schemes and arbitrary g are allowed. Neither comparison
adds a Noetherian hypothesis on X or S.

## New nodes

`lem-sfb-integral-section-scalar-models`, attached to
`Sheaf.Paper.IntegralSectionScalarModels`, isolates comparison of finite scalar matrix
cokernels under the prescribed section and coefficient functor. Its proof checks
regular scalar maps at every positive quotient, uses joint monicity, and transports
finite biproducts and cokernels. It supplies the comparison for a given scalar module,
not existence or recognition of a scalar model for an arbitrary internal module.

`lem-sfb-integral-section-local-isomorphisms`, attached to
`Sheaf.Paper.IntegralSectionLocalIsomorphisms`, isolates inverse-image and slice-site
transport for arbitrary pairs of modules. Its proof uses section-action reconstruction,
normalized coefficient isomorphisms, and full faithfulness after identifying the
slice site. It neither constructs a scalar module nor proves it finitely presented.

Both nodes carry source places, complete proof outlines, exact Lean attachments,
the inherited chapter and unit, and three recorded kinds of Mathlib search.
No existing definition or statement changed, so no change record is required.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
