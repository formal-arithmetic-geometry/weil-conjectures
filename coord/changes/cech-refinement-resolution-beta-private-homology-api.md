# sections_forget_homology_iso

## Reason

The beta proof needs repeated comparisons of the sections and forgetful homology
isomorphisms. Unfolding `ShortComplex.mapHomologyIso` during these comparisons
expands the chosen homology construction and caused a timeout. The new private
wrapper is irreducible and has proved hom/inverse equations with an explicit
scheme sections ring. The preflight treats the file-level options and attribute
as an interface change, so this record documents their scope. No existing public
signature, definition, instance or public import is changed.

## Old

The original module had only this file-level option and no private homology wrapper:

```lean
set_option autoImplicit false
```

The public theorem `cechRefinement_resolution_canonical_beta` had proof `by sorry`.

## New

The existing option remains. These elaboration/linter commands are added:

```lean
set_option linter.privateModule false
attribute [irreducible] sections_forget_homology_iso
```

`sections_forget_homology_iso` is a new private noncomputable definition whose
body is the canonical `ShortComplex.mapHomologyIso` of the global-sections
complex. The private proved equations `sections_forget_homology_iso_hom` and
`sections_forget_homology_iso_inv` expose its hom and inverse. Its data contains
no sorry. The wrapper and its attribute are private to this module. Options
control compilation of this file and do not propagate to importers. The file uses
its package transparency default, without the former theorem-local
`backward.isDefEq.respectTransparency.types false` override. Before the main theorem:

```lean
attribute [local irreducible] HomologicalComplex.homologyMap ShortComplex.mapHomologyIso
attribute [local irreducible] moduleCechComplexAlpha moduleCechComplexBeta
  moduleCechAlpha moduleCechBeta
```

The second reader also keeps the concrete alpha and beta constructions behind
their proved naturality and specialization equations. This keeps the native
homology-map and homology-isomorphism constructions behind
Mathlib's proved equations during elaboration; no definition body changes. The
attributes are local to this file. In particular, importers retain their original
transparency settings. The sole existing public theorem keeps its signature and
now has the diagram-cancellation proof.

## Users

`tools/downstream.py Sheaf.Paper.CechRefinementResolutionBeta --uses
cechRefinement_resolution_canonical_beta` reports the defining module and this
one actual user. The other import descendants do not mention the theorem
and cannot refer to the new private wrapper. No adaptations are required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CechRefinementResolutionBeta | G3 | Private wrapper and proof only. |
| Sheaf.Paper.CechRefinementResolutionDiagram | unclaimed | Unchanged; no adaptation. |

## Status

landed 20261014T034909-L-814412 2026-10-14 (merge of deliver/G3/Sheaf.Paper.CechRefinementResolutionBeta)
