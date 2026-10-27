## What changed

Replaced the hole in
`AlgebraicGeometry.Scheme.Modules.etaleTensorSections_open_determination` by a complete
Lean reduction to source local generation. Naturality and `h_open` give equality on
all normalized pullbacks of sections on base opens; `LinearMap.eqOn_span` gives equality
on their linear spans. A covering sieve supplied by the new local-generation lemma
then gives equality after every covering restriction. Sheaf separatedness and linear-map
and function extensionality finish the proof.

The target universe `v` stays independent of the scheme universe `u`. The forgetful
functor on abelian groups is corepresented by `ULift ℤ`; its coyoneda isomorphism
transfers the given sheaf condition to the underlying presheaf of types without
any universe inequality. All original theorem binders and the conclusion stay verbatim.
The original docstring retains the valid adjunction argument; an inline proof comment
identifies the section-level route now implemented.

Added `Sheaf.AlgebraicGeometry.EtaleTensorSectionsLocalSpan`, with one named theorem
about local generation of the source tensor-pullback sections only. It has no target
sheaf, no two maps and no equality hypothesis. Its docstring and node spell out the
finite pure-tensor, inverse-image representative and unit-normalization argument.
This is a strictly simpler geometric input, not the original uniqueness assertion
under another name. The item's node now records the actual three-step Lean proof.

Removed the unused public import of TensorPullbackSectionAdjunction and four private
imports; added private imports of LocalSpan and ForgetCorepresentable. The two direct
importers are checked against the pruned public interface and need no edits. Change
record: `coord/changes/etale-tensor-open-determination-imports.md`.

## Proved and sorry left

This is a decomposition, not a net proof-count improvement: one original hole closed,
one hole added, net zero.

Closed: `AlgebraicGeometry.Scheme.Modules.etaleTensorSections_open_determination`
(node `lem-trf-etale-tensor-sections-open-determination`). Its body is complete Lean.

Added and still sorry:
`AlgebraicGeometry.Scheme.Modules.etaleTensorSections_locally_span_open`
(node `lem-trf-etale-tensor-sections-local-span`). It is exactly one public theorem
with proof `:= by sorry`; no other holes are added, and no definition is changed.
The actual hole count is zero in the item and one in its new dependency.

Validation through lcompile.py: the new statement compiles in 3.4 seconds; the
final item with pruned imports compiles in 3.6 seconds. The unchanged direct importers
EtaleExtensionFreePresentationsHom and SchemeEtaleRelativeDifferentialsComparison
compile against the delivery in 34.4 and 23.1 seconds respectively. Neither needs an
adaptation. Their temporary source copies were removed after validation. The item
signature was compared verbatim with the shared source and is unchanged. Both node
proof-dependency lists equal the union of their step uses; every new-node dependency
has an existing Lean declaration or Mathlib record.

## No longer needed

Removed from the item:

- public import `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`;
- private import `Mathlib.CategoryTheory.Adjunction.CompositionIso`;
- private import `WeilConjectures.AlgebraicGeometry.EtaleTensorSections` (already
  publicly available through EtaleTensorOpenSectionsNaturality);
- private import `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction` (likewise
  already provided through EtaleTensorOpenSectionsNaturality);
- private import `Sheaf.CategoryTheory.RingedSiteModules` (the statement uses the
  Mathlib module-presheaf and sheaf-condition types directly).

The old Zariski-map construction and adjunct comparison are not used by the item.
In particular its direct proof no longer needs
`new-etale-tensor-open-section-naturality`,
`lem-sc-left-adjoint-composition-iso-associativity`,
`lem-weil-pbc-open-immersion-module-pullback-restriction`, or
`lem-pc-module-pullback-adjunction`. The latter two remain dependencies of the new
local-generation argument, which uses their normalization equations; they are not
claimed globally unnecessary. Removed the obsolete top-level tool approvals for
`lem-pc-module-pullback-adjunction` and
`new-etale-tensor-open-section-naturality`, retaining the other approvals in order.

No library module or DAG node is withdrawn. No claim is made that an entire module
has left the targets' import closure: other consumers can still require each of these
modules. The unit statement and unit steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original argument is mathematically valid, but its
construction of a Zariski module map cannot directly use the available constructor
`tensorExtensionZariskiRestriction`: that constructor is fixed to the scheme universe,
whereas this theorem has an independent target-module universe. Local generation
avoids constructing that target Zariski module. The standard sheaf-composition lemma
also initially tried to unify the source and target universes, so the final proof uses
the corepresentable forgetful functor directly.

The local-generation statement was checked on empty objects, zero modules, zero
sections and arbitrary non-quasi-coherent modules. On an empty object the empty
cover suffices; span membership is stable under arbitrary further etale restrictions
by their composition law and semilinearity. No extra assumptions or arbitrary
witness-defined data are introduced.

## New nodes

`lem-trf-etale-tensor-sections-local-span` states local generation of a section of
an arbitrary tensor pullback by restrictions from base opens on a covering sieve.
It is sourced to the actual tensor construction (Sheaves 0095 and 0096), the explicit
inverse-image colimit construction, and the omitted small-site proof of Descent 070S(2).
Its complete proof in words handles both finite local representatives and passage to
the generated covering sieve. LeanSearch, Loogle and source searches found no existing
statement with this generality and these canonical restrictions. The new module is
`Sheaf.AlgebraicGeometry.EtaleTensorSectionsLocalSpan`; its single hole is listed above.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
