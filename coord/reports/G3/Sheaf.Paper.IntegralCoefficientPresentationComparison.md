## What changed

Proved `WeilConjectures.IntegralCoefficientPresentation.comparison` without changing its
statement or any existing definition. Only the item module, its node's proof record and a proof-scope change record
are changed. All new helpers are private and proved in the item; there are no new modules.

The finite quotient comparison uses `Ideal.quotientEquiv` and quotient representatives.
The constants-to-functions comparison reuses the published normalized comparison and its
naturality. The completed comparison is induced by the natural isomorphism of finite
systems and is uniquely determined by its projections.

The shorter derived argument uses adjunctions instead of constructing another K-flat
model. Restriction along a ring isomorphism and its inverse give an ordinary equivalence
by the sectionwise restriction compositors. Exact-functor descent gives the inverse
derived equivalences and preserves and reflects cohomology bounds. The finite extension
comparison is the mate of the normalized restriction square. Its defining adjunction
bijection gives the actual unit equation; its hom bijections prove invertibility.

The proved `mapDerivedCategorySquareIso_comp` and exact restriction composition API
carry the sectionwise quotient coherence to derived categories. A generic adjunction
calculation then gives every quotient transition equation, including equal indices.
Exact countable products give the two derived products. Product projections prove the
augmentation and shift equations, and additivity proves compatibility with the actual
`1-s` maps. No constructibility, completeness, boundedness, nonempty-scheme or flatness
hypothesis is added. The unit route in `sk-thm-properbasechange` is unchanged.

Validation: the complete proof compiled through `lcompile.py` in 14.5 seconds in the
final diagnostic run; kernel checking took under one second. The original theorem
signature was compared verbatim and is unchanged. The updated 390-node dependency
closure was checked acyclic. No delivered line exceeds 100 characters. The final
profiling option was removed before delivery.

The added proof imports are `Sheaf.CategoryTheory.DerivedExactSquareComposition`,
`Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`. The first two
supply generic proved localization coherence, not any proper-base-change conclusion.

## Proved and sorry left

Closed the one original hole, in
`WeilConjectures.IntegralCoefficientPresentation.comparison`
(node `lem-weil-pbc-integral-coefficient-presentation-comparison`).
Holes added: none. Holes left in delivered Lean files: none. No split-off statements.
The proof uses the existing library's published declarations; it does not assert that
all their transitive dependencies have already been proved.

## No longer needed

Removed these unused proof imports:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`.
- `Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`.

The item's separate proof steps no longer need
`lem-weil-l-adic-extension-integers-dvr`, `lem-weil-valued-dvr-finite-quotients`,
`lem-pur-proetale-finite-constant-sections`,
`lem-sfb-ring-isomorphism-tensor-transport`, `lem-pc-kflat-resolution`,
`lem-pur-derived-change-of-rings`, `def-pur-sheaf-tensor-product`, or
`lem-pur-sheaf-ring-derived-coefficient-adjunction`.
Finiteness and the normalized finite sheaf comparison are already part of the
published pbc coefficient datum API. The derived compatibility follows directly from
the existing adjunctions and coherent restriction squares. The corresponding obsolete
proof dependencies and tool approvals are removed from this node's copy.

No module is withdrawn. These removals concern this proof route; declarations and
imports needed by other library consumers remain untouched. In particular, the
quarantined parent `IntegralStratifiedPerfectCharacterization` is preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid but longer than necessary: the published
scalar-extension adjunction uniquely determines the required comparison from the
restriction square. The Yoneda argument proves that mate invertible because both
vertical restrictions are equivalences. This avoids a second chain-level tensor model
and its resolution-independence bookkeeping. The original finite and completed
normalizations, and every derived unit, transition and Roos clause, are retained.

No statement repair, target change, forced adaptation, or new node was needed.
Preflight requested a record for the added `open CategoryTheory.Functor` command;
`coord/changes/integral-coefficient-presentation-proof-scope.md` documents its
file-local proof purpose and unchanged public declarations.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
