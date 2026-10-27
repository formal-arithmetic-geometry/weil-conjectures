## Worker report

Item: `lem-sfb-flat-lfp-structure-relative-pseudocoherence`, group Q07, 2026-10-24.
The module `Sheaf.AlgebraicGeometry.FlatLfpStructureRelativePseudoCoherent` states
`AlgebraicGeometry.Scheme.isPseudoCoherentRelativeTo_structureSheaf_of_flat_of_locallyOfFinitePresentation`.
Its only theorem has proof `by sorry`. It constructs no new notions.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes Y and S are `{Y S : Scheme.{u}}`, and their named morphism is `(g : Y ⟶ S)`.
- Flatness of g is `[Flat g]`, the recorded Mathlib definition, equivalent to flatness
  on stalk maps by `Flat.iff_flat_stalkMap`.
- Local finite presentation is `[LocallyOfFinitePresentation g]`, the recorded
  Mathlib affine-local definition. Mathlib's instance in FinitePresentation.lean
  derives `LocallyOfFiniteType g`, as required by the relative predicate; it is not
  a further binder or hypothesis.
- The structure sheaf as its own module is
  `SheafOfModules.unit (moduleRings Y.toRingedSpace)`. The source definition is the
  ring sheaf itself with its ordinary self-module action (Sheaf.lean:173 and
  Presheaf.lean:304), so this is O_Y, not an arbitrary rank-one module.
- O_Y[0] in the unbounded derived category is
  `(DerivedCategory.singleFunctor (SheafOfModules.{u}
    (moduleRings Y.toRingedSpace)) 0).obj (SheafOfModules.unit ...)`.
  The docstring and definition of `DerivedCategory.singleFunctor` in
  Mathlib/Algebra/Homology/DerivedCategory/Basic.lean:242 place the module in degree 0.
- Pseudo-coherence relative to S is exactly `IsPseudoCoherentRelativeTo g` applied
  to this object. Its recorded definition quantifies over every integer m and
  permits distinct affine covers, finite dimensions and closed immersions for
  every m, requiring m-pseudo-coherence of the derived image of the restriction.
- The explicit absence of quasi-compactness and Noetherian hypotheses is respected:
  neither, nor any separation condition, occurs in the signature.
- The dependent class binder for every scheme T is precisely the localization-size
  convention required by the recorded relative predicate, with explicit universes
  `u w`. It chooses no new category or abelian structure and imposes no geometric
  condition. All variables and universes are bound; `autoImplicit` is false.

Dependency declarations read and used:

| Node | Module | Declaration |
| --- | --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme; Scheme.Hom |
| def-weil-flat-morphism | Mathlib.AlgebraicGeometry.Morphisms.Flat | AlgebraicGeometry.Flat |
| def-sbc-locally-finite-presentation | Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation | AlgebraicGeometry.LocallyOfFinitePresentation |
| def-pc-derived-category | WeilConjectures.AlgebraicGeometry.DerivedCategory | AlgebraicGeometry.schemeDerivedCategory |
| def-sfb-relative-pseudo-coherent-complex | Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex | AlgebraicGeometry.Scheme.IsPseudoCoherentRelativeTo; IsMPseudoCoherentRelativeTo |

All five statement modules are public imports. Already stated proof-dependency
modules are plain imports (a dependency that is also needed in the statement is
already public). The module imports the Mathlib finite-presentation, finite-type,
affine-space, closed-immersion and tilde interfaces as well as the recorded affine
QCoh equivalence, derived direct image, exact ordinary closed pushforward, affine
pseudo-coherence criterion, absolute pseudo-coherence, m-pseudo-coherence and derived
pullback modules. The polynomial pseudo-coherence lemma
`lem-sfb-flat-fp-polynomial-pseudocoherent` has no recorded declaration or Mathlib
match in the read repository, so has no import; it is not needed to type this statement.
No downstream theorem is imported.

Source checks: read Stacks more-morphisms.tex Tag 09UI
(definition-relative-pseudo-coherence), Tag 067Y (lemma-pseudo-coherent), clause (3),
and Tag 0695 (lemma-flat-finite-presentation-pseudo-coherent), and more-algebra.tex
Tag 067J (lemma-flat-finite-presentation-perfect). They give exactly the assertion
and do not impose a quasi-compactness or Noetherian hypothesis. The theorem docstring
records all six DAG proof steps and their dependencies, including the particular
polynomial presentation, ordinary versus derived closed pushforward, and the
all-integer m conclusion. The DAG statement is unchanged.

Edge cases checked before writing:

- Empty Y: over each base affine open the source-point quantifier in the relative
  definition is vacuous; there is no nonemptiness binder in the theorem.
- Empty S: the base-point quantifier is vacuous; no affine open is required on a
  nonexistent base point. Every possible morphism to S remains covered.
- Identity g and zero-variable presentations are allowed: affine dimensions in
  the relative definition range over all natural numbers, including 0.
- Arbitrary non-Noetherian base rings and every characteristic are permitted.
- Infinite disjoint unions of finitely presented affine charts over the base
  illustrate that no global finite presentation or finite cover is required.
- The assertion is relative pseudo-coherence of O_Y[0], not absolute
  pseudo-coherence of a pushforward along g and not finiteness of g as a module.

Searches actually run with msearch.py (logged in searches.jsonl):

- LeanFinder: `The structure sheaf of a flat locally finitely presented scheme morphism is pseudo coherent relative to the base`.
  Eight hits about flat morphisms and universal openness, including
  `AlgebraicGeometry.UniversallyOpen.of_flat` and `Flat.flat_appLE`; no match.
- Loogle: `AlgebraicGeometry.Flat, AlgebraicGeometry.LocallyOfFinitePresentation`.
  Twelve hits about openness, etaleness, descent, smoothness and rank; no relative
  pseudo-coherence theorem.
- Mathlib grep, AlgebraicGeometry: `PseudoCoherentRelativeTo|[Pp]seudo.?[Cc]oher`.
  Zero hits.
- LeanSearch: `The structure sheaf of a flat locally finitely presented morphism is relatively pseudo coherent`.
  Eight hits about the structure sheaf and finite-presentation/quasi-coherence
  of module sheaves; no match for derived relative pseudo-coherence.
- Direct rg of both project trees `lean/WeilConjectures` and `lean/Sheaf` for
  `PseudoCoherentRelativeTo|flat.*[Pp]seudo|structure.*[Pp]seudo` found the recorded
  relative definition, closed-support equivalence and related absolute/affine
  lemmas, but no statement of this item. Direct grep of the item id in
  `lean/WeilConjectures` found no occurrence. The new full declaration name was
  also searched before final delivery.

Validation: scompile.py compiled the delivered file in sandbox mode (50.9 seconds)
and its actual library module mode (2.5 seconds), with no errors or unexpected
warnings. No statement correction, new node, dependency repair or disputed
statement is needed.

## Second reading by Q07

Author self-check, as required for dispatcher workers; the maintainer performs the
independent delivery review. Reopened the node, all five recorded dependency
signatures and docstrings, and the completed module. Y and S are arbitrary schemes;
g is the given scheme morphism; flatness and local finite presentation are separate
class binders. The relative predicate receives g and exactly the degree-zero object
of the self-module O_Y. The inherited derived-category binder matches the predicate's
universe convention. Local finite type is inferred from local finite presentation,
so it is neither an added hypothesis nor an omitted requirement. The predicate's
all-m quantifier and its arbitrary affine covers match the node, including empty
schemes. No stronger conclusion, finite-cover restriction or absolute substitute
was found, and no statement changes were made. The proof docstring follows the six
node steps in order. Only the node's lean field is changed.
