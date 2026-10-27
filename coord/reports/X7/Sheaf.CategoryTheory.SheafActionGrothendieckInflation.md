## What changed

Proved both holes of `Sheaf.CategoryTheory.SheafActionGrothendieckInflation`.
The action-restriction naturality equation follows by evaluating naturality of the
group-presheaf morphism. The main theorem uses each group's existing presentation,
Mathlib's abelian and Grothendieck transfer theorems, and the presentation's creation
of kernels and cokernels. All transferred abelian structures retain the specified
sectionwise preadditive structure definitionally.

Proved private helpers establish additivity and faithfulness of forgetting, zero
detection, the ordinary sheafified-cokernel formula, and the exactness packages.
The cokernel formula uses the sheafification adjunction counit and preservation of
cokernels. Inflation is additive by reflexivity; its composite with forgetting is
definitionally the original forgetful functor. Reflection of finite limits and
colimits gives its preservation properties, and detection proves exactness.

Added private proof imports of `Mathlib.CategoryTheory.Abelian.Transfer` and
`Mathlib.CategoryTheory.Preadditive.LeftExact`; updated the existing DAG node's
proof, proof dependencies and proof origin. No public signature, public import,
existing definition body or target changed. No other module was adapted.
The presentation witnesses are eliminated within a theorem proof, never chosen to
supply arbitrary data to a definition. The private abelian constructor takes its
presentation as an explicit argument.

Validation: the whole module compiled through `lcompile.py` in 18.9 seconds with
no warnings or errors. The import-direction check for the exact-family theorem
passed. All newly added helpers are proved. The argument uses no nontriviality of
either group and no nonzero-ring assumption, so the stated edge cases remain.

## Proved and sorry left

Closed 2 of 2 original holes:

- `CategoryTheory.InternalActionSite.restrictLinearAction_naturality`.
- `CategoryTheory.InternalActionSite.sheaf_action_grothendieck_inflation`.

Zero holes remain in this module; zero holes were added; zero results were split
off. The proof intentionally uses the already stated
`CategoryTheory.InternalActionSite.presentation`, whose proof remains a separate
existing obligation. This delivery proves the item from that declaration.

## No longer needed

Removed the private import `Mathlib.Algebra.Homology.ExactSequence`: the proof uses
short complexes directly, rather than the finite composable-arrow API.

The planned dependency `lem-sfb-equivariant-module-sheafification-reflector`
(module `Sheaf.CategoryTheory.EquivariantModuleSheafificationReflector`) is not
needed by this proof and was not imported. The presentation already supplies
creation of cokernels, and reflection through forgetting establishes inflation's
cokernel preservation. The node's proof dependencies now omit that reflector.
This is local dependency pruning, not withdrawal of the reflector or a claim that
no other parent needs it. All remaining declared proof dependencies are retained;
`def-weil-presheaf-modules-sheafification` is explicitly cited for the ordinary
cokernel comparison. No module or declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The plan's separate unique-extension argument for
inflation cokernels is unnecessary once creation and exact-family detection are
available. Mathlib's transfer and reflection APIs implement the same categorical
argument more directly. The blueprint unit route is preserved: its statement and
steps are untouched, and this node is below the unit level. No new nodes or change
records are needed because all additions are private proved helpers and no
existing interface is changed.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
