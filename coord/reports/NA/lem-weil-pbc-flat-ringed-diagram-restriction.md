## Worker report

The target declaration is already present on the current `newtargets-dag` base as
`CategoryTheory.FlatRingedDiagramInput.flatRingedDiagramRestriction` in
`Sheaf.CategoryTheory.FlatRingedDiagramRestriction`. The module states the target theorem
with proof `sorry`; all input data and all conclusion conjuncts are retained verbatim.
The declaration's docstring records the ten-step proof plan and its Stacks sources (Tags
0FND, 0DVC, and 03D3).

The hypotheses are rendered by the explicit binders `{C D : Type u}`, small categories,
site topologies `K,H`, index category `J`, and the four `HasDerivedCategory.{w}` instances;
`x : FlatRingedDiagramInput K H` supplies the four ring sheaves, coefficient maps,
flatness hypotheses, common ringed-topos adjunction, compatible module inverse/direct
images, and the commuting coefficient square. The theorem then binds `LR,FR,LS,FS`,
the factor isomorphisms `qLR,qLS`, units `ηR,ηS`, adjunctions `aR,aS`, the universal
right-derived predicates `derivedR,derivedS`, K-injective computation clauses
`computesR,computesS`, and both representative transpose equations `transposeR,
transposeS`, exactly as in the node.

The conclusion is the conjunction of finite-limit and finite-colimit preservation for
`restrictU` and `restrictV`; preservation of `CochainComplex.IsKInjective` by their
complex extensions for every input complex; and
`Nonempty (DerivedRestrictionComparison ...)`. The comparison structure carries the
ordinary identity normalizations, localization factors, inverse/direct normalization
identities, and the derived adjunct equation, including every `J` transition map.

Dependency declarations used by the module are:

- `Sheaf.CategoryTheory.FlatRingedDiagramRestrictionComparisonAdjuncts`, providing
  `CategoryTheory.FlatRingedDiagramInput.DerivedRestrictionComparison` and its three
  normalization predicates.
- `Sheaf.CategoryTheory.FlatRingedDiagramRestrictionComparisons`, providing
  `CategoryTheory.FlatRingedDiagramInput.DerivedRestrictionComparisonMaps`.
- `Sheaf.CategoryTheory.FlatRingedDiagramRestrictionDefs`, providing
  `CategoryTheory.FlatRingedDiagramInput`, all four diagram categories and the
  termwise/complex functors.
- `Sheaf.CategoryTheory.RingedToposMorphism`,
  `Sheaf.CategoryTheory.RingedSiteModules`,
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, and Mathlib's
  `SheafOfModules.restrictScalars`, as used by the input structure.
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral` and the listed K-injective,
  derived-category, tensor, and exact-functor modules, which are imported for the
  theorem's proof plan.

Edge cases checked in the landed statement and definitions include empty `J`, terminal
`J`, identity coefficient maps and identity geometric adjunction, zero coefficient
rings, and arbitrary independent localization universe `w`. No inhabitedness,
boundedness, or site-presentation functor is added.

Searches made for a duplicate declaration:

- `msearch.py ... leanfinder "flat coefficient restriction derived module diagram comparison"`:
  only generic flat-module and restriction results; no matching theorem.
- `msearch.py ... loogle "FlatRingedDiagramInput, DerivedRestrictionComparison"`:
  zero hits (identifiers are project declarations).
- `msearch.py ... grep "flatRingedDiagramRestriction" CategoryTheory`:
  zero Mathlib hits.
- `rg -n "flatRingedDiagramRestriction|DerivedRestrictionComparison"` over the source
  checkout and project: only the landed Sheaf modules and their node records.

The current base already contains the reviewed declaration and its supporting modules;
this packet copies those exact files and node record for independent NA delivery
bookkeeping. No statement correction or `STATEMENT-DISPUTED` flag applies.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
