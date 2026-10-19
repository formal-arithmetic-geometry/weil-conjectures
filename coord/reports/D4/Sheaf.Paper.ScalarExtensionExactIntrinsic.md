## What changed

Proved `WeilConjectures.sfScalarExtension_exact_triangulated` with its original signature.
The proof uses the existing `sfIntegralOrdinaryComparison` to transport exact ordinary
derived tensor to the intrinsic integral restriction, then descends its coherent shift
through scalar localization. The rational scalar functor agrees with the integral
functor followed by localization on integral morphisms, by its existing pure-tensor
specification at scalar one. Distinguished rational triangles are the published
isomorphic integral images; their images are therefore distinguished, including the
connecting arrow. Two proved private helpers identify the raw tensor-Hom localization
with the existing Verdier rationalization so Mathlib's localization API applies.

The added proof dependency `lem-weil-scalar-extension-composition` is used only for its
already published normalized intrinsic ordinary-to-completed comparison. This is a
generic tool from another unit: no result on scalar composition or associativity is
assumed in this proof. The item's unit record has no realized statement or proof step
that this route bypasses. No statement, definition, target or public import was changed.
The proof-local universe, open, option and attribute commands flagged by the static interface
checker are documented in `coord/changes/D4-scalar-extension-exact-proof-commands.md`.
Its consumer audit found four direct importers and no external textual theorem use; no
adaptations are needed.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.sfScalarExtension_exact_triangulated`
(node `lem-weil-scalar-extension-exact-triangulated`). No new holes or split-offs.
The item has zero remaining `sorry`s. The existing imported interface theorems remain
separate obligations; this delivery proves the item from those declarations.

The resumed worker retained the previous attempt's proof and checked its signature,
published comparison, localization interfaces, node dependencies and unit record against
the current shared sources. A fresh single-file `lcompile.py` run compiled without
warnings in 6.2 seconds; no proof changes or new split-offs were needed on resumption.

## No longer needed

The new proof does not redo the Roos cone calculation or construct an ambient left
derived functor from a resolving class. Accordingly its direct proof dependencies
`lem-weil-proetale-countable-products-exact`, `lem-pur-homotopy-category-triangulated`,
`lem-pc-kflat-resolution`, `lem-weil-integral-scalar-extension-well-defined`, and
`lem-pur-left-derived-from-kflat-class` are no longer needed here. Their direct proof
imports are removed: `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`,
`Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`,
`Mathlib.Algebra.Homology.DerivedCategory.Basic`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.Paper.IntegralScalarExtensionWellDefined`, and
`Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`.
The same five obsolete top-level `tool_uses` approvals are removed, preserving the
order of the remaining approvals. This describes direct pruning only; some modules remain transitive dependencies of
the existing comparison or coefficient constructions. No global unreachability is claimed.

## Where the brief, the DAG or earlier work was wrong

The DAG's explicit cone/resolving-class route is longer than necessary now that
`SfScalarExtensionComposition` publishes the normalized comparison on the actual
intrinsic integral predicate. Its declaration is used without identifying that
predicate with the legacy bounded constructible category. The node proof and
proof dependencies are updated to describe this route.

Directly matching the chosen image-triangle characterization was expensive. The final
proof instead uses Mathlib's localization calculus of fractions to supply essential
surjectivity on arrows, then `Functor.isTriangulated_of_precomp`. A local irreducibility
attribute also keeps the rational triangulation datum folded. No construction is changed.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
