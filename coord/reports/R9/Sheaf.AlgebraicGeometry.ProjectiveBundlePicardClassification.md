## What changed

Reduced `AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_picard_classification`
to three strictly smaller statements in new modules:

- `ProjectiveBundleLocalNormalForm`: local normal forms over the base and the field normal form
  (original plan steps 1–4).
- `ProjectiveBundleLocalTwistDescent`: descent and uniqueness, assuming local normal forms
  (original plan steps 5–8).
- `LocallyConstantLineTwistIdentities`: restriction, addition and pullback of the concrete glued
  integer powers, valid for every invertible sheaf independently of projective bundles.

The original theorem signature and all three original public definitions are unchanged.
The main proof derives quasi-coherence from finite local freeness, uses local normal forms in
coefficient descent, constructs both directions of `local_iff`, and constructs tensor and
base-change decomposition isomorphisms. The tensor proof exchanges the middle two factors and
combines twist and coefficient factors separately. The base-change proof uses the square equality
both on degree functions and between the two composite pullbacks. A proved private helper compares
explicit tensor pullback with ordinary module pullback by uniqueness of left adjoints, establishing
preservation of invertibility without an extra split.

All writes are in the item sandbox. No existing module besides the item is changed, no source-library
file is changed, and no public import is removed. The unit record has empty realized statement and
step lists; this reduction does not bypass or change any unit realization.

## Proved and sorry left

Original holes: 1. The complete proof of
`AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_picard_classification`
closes that hole relative to the three new theorems below. This is a decomposition, not an
unconditional proof or a net reduction in holes: 1 closed, 3 added, net -2.

Every remaining hole is exactly the full body of one public theorem, with its source and proof in
words in its docstring:

- `AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_local_normal_form`
  (`lem-sfb-projective-bundle-local-normal-form`).
- `AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_local_twist_descent`
  (`lem-sfb-projective-bundle-local-twist-descent`).
- `AlgebraicGeometry.Scheme.Modules.locallyConstantLineTwist_identities`
  (`lem-sfb-locally-constant-line-twist-identities`).

The item itself has zero `sorry`; each new module has one. The private helper
`invertible_tensorPullback` is proved. No data definition, anonymous proof, or private declaration
contains a hole.

Validation: `lcompile.py --all` compiled all four modules successfully: twist identities 2.5 s,
local normal forms 13.1 s, local-twist descent 14.5 s, and the main classification 32.3 s.
The final delivery checks recompile after redundant-import removal.

## No longer needed

The tentative explicit `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula` import was
also removed: its public API already comes from the preserved line-twist dependency via Dual.

Removed direct proof imports from the original item:
`Sheaf.AlgebraicGeometry.AffineSpaceInvertibleTrivial`,
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`,
`WeilConjectures.Topology.GlueSheavesOfModules`,
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace`,
`Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`WeilConjectures.AlgebraicGeometry.Cohomology.Serre`,
`Sheaf.AlgebraicGeometry.ProperFlatFibreSectionLifting`,
`Mathlib.AlgebraicGeometry.Morphisms.Proper`,
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`,
`Mathlib.AlgebraicGeometry.Noetherian`,
`WeilConjectures.AlgebraicGeometry.LimitFibreProducts`,
`Sheaf.AlgebraicGeometry.InvertibleAffineLimitDescent`, and
`Mathlib.CategoryTheory.Yoneda`.

The first twelve are prerequisites of the new local-normal-form, descent or twist-identity
statements, rather than direct steps of the assembled main proof. Their mathematics remains needed;
this is not a withdrawal or global pruning claim. Yoneda's representable-uniqueness argument is
unnecessary for the main base-change clause: it already supplies the actual projection maps and a
commuting pullback square. The generic twist identity and composition of module pullbacks suffice.
Accordingly `lem-pc-representable-unique` is no longer a proof dependency of this item or its new
statements. No module is withdrawn.

The item node's proof and proof dependencies now describe the actual combination proof. Its obsolete
direct `tool_uses` entries for gluing, projective-space properness, cohomology, quotient geometry,
Noetherian approximation, limit fibre products and invertible descent were removed; the direct
module-pullback tensor and composition entries are retained in their original order. The removed
tools remain explicitly cited where appropriate by the new statements' proof plans.

## Where the brief, the DAG or earlier work was wrong

The declared dependencies do not directly supply relative local normal forms, descent of arbitrary
local twists, or the API for the concrete product defining a variable twist. These are the gaps
isolated here. In particular one cannot claim that a left-adjoint pullback preserves the infinite
product defining a variable twist. Its comparison is instead constructed locally on the disjoint
degree strata and glued; the new identity statement and proof plan explicitly use this argument.

The existing node has `blueprint.from.node = null` even though its `place` names
`det-thm-sf-ctf-stability-direct-images`, and that record has the corresponding blueprint identity.
The new nodes use that actual ancestor and preserve the intervening chain. The existing provenance
field is left unchanged because it is outside the permitted proof-field edits.

Edge cases checked mathematically: rank two uses the separate projective-line argument, while
rank one is excluded by the original hypothesis; negative powers use the dual and evaluation;
infinitely many strata require local gluing rather than commuting arbitrary products with
pullback; nonreduced and non-quasi-compact bases are covered by affine approximation; on the empty
base local normal forms are vacuous and coefficient descent uses empty-cover gluing. The field
clause assumes a field spectrum and therefore does not assert unique integers on an empty scheme.
No new result excludes any of these cases or assumes a section of the projection.

## New nodes

`lem-sfb-projective-bundle-local-normal-form` is the local and field calculation from steps 1–4.
It contains neither the global coefficient line nor tensor or base-change compatibility.

`lem-sfb-projective-bundle-local-twist-descent` assumes local normal forms for the specific line L
and proves its unique degree/coefficient presentation. It does not assert local normal forms,
the field clause, or either functorial law. Its proof uses the field part of the first new node on
residue-field bundles, the constant-monomial functions calculation, and transition-unit gluing.

`lem-sfb-locally-constant-line-twist-identities` is independent of projective geometry and proves
only the algebra of the fixed concrete line-power construction. It asserts no classification or
coefficient descent. Its three comparisons are used explicitly by the main proof.

Searches: LeanFinder and LeanSearch found general Proj, ring-Picard and free-sheaf pullback results,
with none stating these parts. Mathlib grep found no relevant classification; repository and DAG
searches found the existing P1 field theorem, the item, and its fibrewise-descent consumer. Both
blueprint text searches returned no duplicate. Each new node records the searches and the source
steps it refines. There are no change records because no existing signature or definition changes.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
