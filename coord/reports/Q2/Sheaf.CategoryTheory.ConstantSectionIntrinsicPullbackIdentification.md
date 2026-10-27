## What changed

Proved `CategoryTheory.constant_section_intrinsic_pullback_identification` in
`Sheaf.CategoryTheory.ConstantSectionIntrinsicPullbackIdentification`, preserving every
existing public declaration, statement, definition, and public import. Added proved private
helpers for scalar endomorphisms, their adjunction mates, the coefficient equation, and the
normalized direct-image comparison. Updated the existing node's proof, proof dependencies,
proof origin, and obsolete top-level tool-use approvals to match the actual argument.

The key shorter argument recovers direct-image scalar compatibility from inverse-image
compatibility by taking mates under the supplied module adjunction. It recovers additivity
of the given section comparison using Mathlib's fully faithful forgetful equivalence for
left exact functors out of an additive category. Local surjectivity of the constant-ring
sheafification unit upgrades constant-scalar linearity to module linearity. The rest uses
adjunction uniqueness, transport of exactness, and the existing derived comparison API.

Validation: the complete module compiled cleanly through `lcompile.py` in 32.2 seconds,
including the removal of unused imports. There are no `sorry` tokens. Delivery runs the
independent axiom probe and preflight. Edge cases require no exclusions: zero coefficient
ring, empty sites, and the identity geometric morphism are covered. Commutativity is used
only to make multiplication by a constant scalar a module endomorphism after restriction.
The static preflight requests the change record
`coord/changes/Q2-constant-section-intrinsic-private-context.md` for the new helper
`variable` commands. The consumer check reports zero downstream modules; the helper
section closes before the existing public theorem. No target signature, definition,
or consumer changes are required. No source-library file
is changed. The blueprint unit's statement and realized route remain unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.constant_section_intrinsic_pullback_identification`
(node `lem-sfb-constant-section-intrinsic-pullback-identification`).

Added 0 holes. Split off 0 statements. No sorry remains in any delivered declaration.
Every private helper is proved. This is a proof, not a decomposition.

## No longer needed

Removed proof imports:

- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`: the intrinsic adjunction
  already is Mathlib's pullback-pushforward adjunction; no general tensor reconstruction
  is needed. Its node `lem-weil-pbc-ringed-topoi-module-adjunction` is no longer a proof
  dependency of this item.
- `Sheaf.CategoryTheory.ConstantRingModuleSheaves`: direct use of Mathlib's fully faithful
  scalar restriction along a locally surjective ring map supplies the needed linearity.
  The larger equivalence theorem `lem-cbc-constant-ring-module-sheaves` is unnecessary here.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`: the structure asks for the three
  normalized comparison squares, supplied directly by the adopted exact-functor API;
  no additional ordinary-derived characterization theorem is needed. Its node
  `lem-weil-pbc-exact-functor-derived-functor` is no longer used here.
- Explicit Mathlib proof imports `Mathlib.CategoryTheory.Adjunction.Mates` and
  `Mathlib.CategoryTheory.Localization.Predicate`: the narrower invoked APIs are available
  through the retained public exact-functor import and private `Adjunction.Unique` import.

The proof also does not invoke `constant_left_module_inverse_image` or its coherence
conclusions (`lem-pe-constant-left-module-inverse-image`). The existing public import of
`ConstantLeftModuleInverseImage` is preserved, and its underlying lift interface remains
needed. The obsolete top-level `tool_uses` entries for this node and the three project
results above are removed, retaining the relative order of all remaining approvals.

These are dependencies pruned from this item's proof, not withdrawals of the declarations
or claims that other targets no longer need their modules. No file is deleted.

## Where the brief, the DAG or earlier work was wrong

The old plan informally treated the section comparisons as additive and direct-scalar
compatible. The supplied lift records inverse-scalar compatibility but no direct-scalar
field, and its abelian direct underlying comparison is only a set-sheaf isomorphism.
The proof supplies both missing arguments: the module adjunction determines the direct
scalar operation by mates, and left exact functors from the additive module category
have uniquely recoverable abelian structure. Thus no interface strengthening is needed.

The initial proof's reconstruction of the general ringed-topos tensor adjunction and its
ordinary-derived characterization are unnecessary for the actual Lean statement. The
updated route keeps the normalized units and all three derived localization equations.
No mathematical statement or definition was corrected. The two additional existing
Mathlib leaves used are `lem-exc-left-exact-functor-forget-equivalence` and
`lem-cbc-sieve-module-sheafification`; they are exact generic tools, not replacements for
any blueprint unit. No new node is introduced.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
