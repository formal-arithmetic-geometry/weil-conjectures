## What changed

The item constructs the specified tensor/internal-Hom adjunction from the existing
independent-universe `SiteTensorHom.equiv`. Its unit and counit formulas are proved on
sections, including every HEq transport. The existing line-evaluation theorem makes the
positive tensor functor an equivalence, so upgrading this very adjunction supplies the
required inverse Hom functor and exactness. The explicit left tensor unitor supplies
the coefficient-unit comparison with its multiplication formula.

Scalar extension of the integral root line is handled in Lean, using
`scalarExtensionDual_localIsomorphism` and `c.scalar.model.obj_eq`. The only remaining
geometric step is isolated in `Sheaf.Paper.KummerRootRankOne`: integral rank one for an
arbitrary module system whose specified forgetful image is the roots tower. This lemma
has no coefficient extension E, Chern data, tensor/Hom equivalence, normalization, or
derived arrows. It is a proper part of the original first proof step, not another
existence theorem for Twisting. No existing statement or definition changes.

Validation: both sandbox modules compile through `lcompile.py`; the final item
compile completed with no warnings or errors in 15.9 seconds. The original theorem
signature is verbatim unchanged, all Lean lines are at most 100 characters, and both
node proof-dependency lists equal the union of their proof steps' uses.

The item keeps its public import. All additional imports are private proof imports.
Its DAG proof and proof dependencies now describe the implemented argument. The new
node inherits the original chapter, unit and primitive-root route.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.ProEtale.SpTowerClasses.nonempty_kummerLineTwisting`
(node `lem-sfb-kummer-line-twisting`).

New hole: `AlgebraicGeometry.ProEtale.SpTowerClasses.kummerRoot_rank_one`
(node `lem-sfb-kummer-root-rank-one`, module `Sheaf.Paper.KummerRootRankOne`).

The item has zero remaining sorry occurrences; the new module has one. This is a
one-for-one decomposition, not a net hole closure. The scalar-extension rank argument,
adjunction construction and naturality, equivalence upgrade, section formulas, unit
normalization, and all exactness/additivity fields are complete Lean proofs.

## No longer needed

No original public import is removed and no module is withdrawn. No whole dependency
is claimed pruned. The primitive-root cover and constant-quotient action uniqueness
are now dependencies of the integral rank-one lemma rather than direct steps of the
item. The same generic tensor/Hom construction is used at independent universes via
`SiteTensorHom.equiv`; `lem-pc-sheaf-modules-tensor-closed` is no longer applied directly
in the item's proof, but remains a dependency of the existing line-evaluation module.

The item uses the generic tools `lem-sf-site-tensor-hom-equiv` (currying on this site),
`lem-pur-sheaf-line-evaluation-inverse-pair` (evaluation of a locally trivial line),
`lem-weil-pbc-independent-sheaf-tensor-colimits` (comparison of the explicit and
monoidal tensors), `lem-sp-scalar-extension-dual-local-iso` (ordinary extension
preserves rank one), and `lem-sp-scalar-extension-binary-coherence` (the explicit
coefficient unitor). These are generic constructions, not replacements of the unit's
primitive-root or diagonal-class argument. Any needed route approvals belong to the
maintainer; no tool_uses approvals were added here.

## Where the brief, the DAG or earlier work was wrong

The recorded tensor-closed declaration uses equal site/coefficient universes. The
sequence site has object universe u+1 and morphism universe u, so the actual proof
uses the existing independent-universe currying and monoidal comparison APIs. The
mathematical argument is unchanged. A compatible cover at all levels gives the
required slice trivializations; a slice over level n contains only levels m ≤ n.

Edge cases: at n=0 the quotient is Z/l, not Z/1; l=2 uses the same primitive-root
formulas. Empty charts and zero section rings are allowed by the local free/unit
criterion and the tensor/Hom adjunction. The intermediate theorem requires no
normalization of Chern arrows, matching the original statement.

## New nodes

`lem-sfb-kummer-root-rank-one` states only the integral local-rank-one step. The
coefficient action is identified from the forgetful section, restriction and transition
equations, and compatibility of primitive roots identifies all sequence restrictions.
Its source, complete proof plan, actual Mathlib searches and Lean signature are in the
new node and module. Blueprint and DAG searches found no existing declaration of this
particular root-system assertion. No change record is needed because existing
statements and definitions are unchanged.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
