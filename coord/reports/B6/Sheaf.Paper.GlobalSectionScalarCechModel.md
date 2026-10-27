## What changed

Replaced the sole proof hole of `CategoryTheory.ringFamilyGlobalExtension_cech` in
`Sheaf.Paper.GlobalSectionScalarCechModel` by a complete proof from two smaller
statements. The original public signature and all existing public imports are unchanged.
No definition, target, source-library module, or other group's module is changed.

The proved private helpers establish that pointwise-flat one-point modules are flat,
that point evaluation detects zero modules, and that the ordered localization
coordinates describe a bounded-above K-flat complex. Finite localization products
are handled through their finite direct-sum linear equivalence. A separate proved
generic helper transports an augmentation-compatible derived isomorphism through
an additive functor preserving quasi-isomorphisms between the designated good
complexes. It refines equality in the derived category to a homotopy after a
quasi-isomorphism, resolves that source, and uses the resulting common good roof.
The two derived-category hom universes remain independent.

The main proof extracts the actual ordered coordinates from `hP`, proves their
K-flatness, invokes the chain-level tensor comparison, transports the given derived
comparison, postcomposes with the explicit unit augmentation, and composes the two
isomorphisms. New imports are private proof imports. Both new theorem modules use
public imports only for their signatures. The original DAG proof now records this
argument and its actual dependencies.

## Proved and sorry left

Original holes: one, `CategoryTheory.ringFamilyGlobalExtension_cech`.
Its proof body is now complete; the assigned module contains zero `sorry`.
All four private helpers have complete proofs.

Two holes are added, each a whole public theorem in a separate new module:

- `CategoryTheory.ringFamilyGlobalExtension_quasiIso_of_kflat`, node
  `lem-weil-pbc-global-section-scalar-kflat-quasi-iso`, module
  `Sheaf.Paper.GlobalSectionScalarKFlatQuasiIso`.
- `CategoryTheory.ringFamilyGlobalExtension_ordered_iso`, node
  `lem-weil-pbc-global-section-ordered-cech-tensor`, module
  `Sheaf.Paper.GlobalSectionOrderedCechTensor`.

This is a decomposition: one upper hole closed and two lower holes added, not a
net hole reduction. The first remaining theorem concerns only preservation of
K-flat quasi-isomorphisms, without Cech models or augmentations. The second concerns
only a chain isomorphism from explicitly given ordered coordinates, without a
replacement P, K-flatness, derived categories, or transport of a derived isomorphism.
Neither is the assigned statement with repackaged hypotheses. The substantive
boundedness, flatness, common-roof, homotopy and augmentation-composition arguments
are proved here and are not left in either hole.

The compile checks all three modules together in import order. Each new statement
has its source, a full proof in words and a matching DAG node. The delivery preflight
supplies the final compile and axiom checks.

## No longer needed

No original import is removed, and no module is withdrawn. No node is claimed to
be globally pruned: the original route still needs both the K-flat scalar-extension
argument and the localization tensor expansion.

The original node no longer directly lists
`lem-pur-change-of-rings-kflat-quasi-iso`,
`lem-weil-pbc-ringed-site-module-sheafification-exact`, or
`lem-weil-pbc-localization-base-change` as proof dependencies. Their work is retained
under the respective new scalar-extension and tensor-comparison nodes. In particular,
this dependency relocation is not reported as pruning those modules.

## Where the brief, the DAG or earlier work was wrong

The stated same-site `SheafOfModules.changeOfRings_kFlat_quasiIso` theorem does not
directly apply to `ringFamilyGlobalExtension`: its domain is a different site (the
one-point site), and the latter is constant presheaf extension followed by a chosen
presheaf pullback and sheafification. The first new theorem isolates this additional
comparison interface rather than treating the two functors as definitionally equal.
The ordered-coordinate to recursive tensor-complex comparison likewise has no
existing matching declaration among the dependencies. The second theorem isolates
exactly that chain-level step of the original node's second proof paragraph.

The mathematical source is the local Stacks text (algebraization, Tags 0996,
099D(d), 099E; cohomology on sites, Tags 06YS and 06YT). The unit route is preserved.
No false statement or target change is proposed. Edge cases checked in the proof
plans are r=0, zero and repeated generators, zero section rings, an empty site,
negative degrees, and ordered subsets larger than r. No nonzero, reduced, distinct,
flat-coefficient-ring or common-derived-universe assumption has been added.

The inherited node's `created.item` is a module name rather than a DAG id, and
`tools/blueprint_refs.py ancestor lem-weil-pbc-global-section-scalar-cech-model`
therefore reports `None`. The new nodes record that computed null ancestor and
explain both the inherited completed-pullback route and the exact original proof
paragraph they serve. Existing provenance fields are preserved.

## New nodes

`lem-weil-pbc-global-section-scalar-kflat-quasi-iso` states the global-section
scalar-extension preservation step. Its proof is the K-flat tensor square after
point evaluation, the adjoint characterization of presheaf pullback, and exact
sheafification. The object is the existing explicitly constructed functor; no
new data is chosen from an unproved existence theorem.

`lem-weil-pbc-global-section-ordered-cech-tensor` states the actual chain-level
localization/tensor comparison. Its proof gives the fraction maps and inverses,
restriction and localization compatibility, finite tensor subset expansion and
signs, and the augmentation equation. It is precisely the original second proof
step, with the unrelated derived replacement removed.

No change record is required: existing statements and definitions are unchanged.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
