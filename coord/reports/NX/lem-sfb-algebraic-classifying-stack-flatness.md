## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicClassifyingStackFlatness` states
`AlgebraicGeometry.AlgebraicSpace.algebraic_classifying_stack_flatness`, with `sorry`
as its only proof. The statement is unchanged. There are no disputed statements or
source corrections. Definitions contain real data and no postponed proof obligations.

Hypothesis and conclusion correspondence:

- A scheme S is `{S : Scheme.{u}}`. The universe variables `u v w` are explicit.
  The total stack has morphisms in `max u v` and objects in `max (u + 1) w`, permitting
  the usual large total category over all the chosen test schemes and larger models.
- Algebraic spaces B and G over S are `{B G : AlgebraicSpace S}`; their structure
  morphism is `(p : G ⟶ B)`. No scheme representability of B or G is required.
- The identity, inverse and multiplication are the natural transformations `e`, `i`,
  and `m : Limits.pullback p.hom.hom p.hom.hom ⟶ G.obj.obj`.
  These are maps of the underlying presheaves; full faithfulness of the algebraic-space
  embedding identifies them with the corresponding maps of algebraic spaces. The
  pullback is the actual presheaf fibre product, and is an algebraic space by the
  existing fibre-product theorem. It has both factors over the identical map p.
- All group laws on all test schemes are `presentation.groupoid`, using the existing
  `AlgebraicSpace.IsPresheafGroupoid` with source and target both `p.hom.hom`.
  Its source/target equations assert that e, i and m are over B; its identity,
  inverse and associativity fields are precisely the fibrewise group laws.
- The stackification [B/G] is `(F, a, presentation)`: a category over the big site,
  the functor from discrete B, its original arrow sheaf identified fully faithfully,
  composition identified with m, and fppf-local lifts of all objects. Since B and G
  are fppf sheaves, each arrow presheaf between original objects is already a sheaf.
  These local conditions characterize exactly the stackification of this groupoid,
  rather than an arbitrary stack with a map from B. No existence assertion or arbitrary
  choice of stackification data is hidden in a definition.
- Algebraicity is exactly `(hF : IsAlgebraicModuliStack F)`.
- The conclusion is `MapIsFlat p ∧ MapIsLocallyOfFinitePresentation p`; these are the
  existing universal compatible etale scheme-chart extensions of `Flat` and
  `LocallyOfFinitePresentation`. There is no quasi-compactness conclusion.
- No flatness, local finite type, smoothness, separation or quasi-compactness hypothesis
  is imposed on p. Group laws and the stackification presentation are the only extra
  binders that specify the objects already introduced in the prose statement.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`, with `GrothendieckTopology.over` for the big slice site.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  its representability, etale-map and surjectivity predicates.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `BasedCategory`,
  `BasedFunctor`, `discreteModuli`, `discreteModuliMap`, `ModuliTwoIso`,
  `IsFibredInGroupoids` and `IsModuliStack`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`, which
  uses the existing stack, representable diagonal and smooth-surjective-atlas definitions.
- `Sheaf.CategoryTheory.GroupoidStackificationLocalDescription`:
  `Pseudofunctor.exists_groupoid_stackification_local_description`; its local description
  explains the presentation and is imported publicly as the recorded statement dependency.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- Added already-landed definition dependencies:
  `def-sfb-algebraic-space-groupoid`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceGroupoid`, declaration `IsPresheafGroupoid`;
  `def-sfb-space-morphism-properties`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`, declarations
  `MapIsLocally`, `MapIsFlat`, `MapIsLocallyOfFinitePresentation`;
  `def-sfb-fppf-stackification`, module `Sheaf.CategoryTheory.SiteStackification`,
  declaration `IsFppfModuliStack`.
- Stated proof modules are imported privately: algebraic-space fibre products,
  `StackChartwiseSmoothEtaleCalculus` and `SpaceLocalPropertiesChartTest`.
  Their full declarations and docstrings were read. The remaining proof dependencies
  have no recorded Lean module in the supplied DAG, so no import is invented for them.

Edge cases: empty B forces the group space empty, and both universal chart predicates
still make sense without nonemptiness or quasi-compactness. The identity group over B
is included. Non-affine B, non-schematic G, disconnected groups and non-smooth groups
are included. Source and target are identical, so arrows between unequal B-points are
empty; arrows at one B-point retain the entire group, rather than its orbit set.
The formula for composition takes the second chronological arrow in the first pullback
coordinate and the first chronological arrow in the second, matching c(q,r)=q after r.
The fppf cover condition uses sieves, including empty covering sieves, and does not bound
the number of components by a finite set. No field or characteristic is restricted.

Searches run with `msearch.py NX lem-sfb-algebraic-classifying-stack-flatness`:

- LeanFinder: "Algebraicity of the classifying stack of a group algebraic space implies
  flatness and local finite presentation": 8 scheme-flatness/finiteness hits, no stack theorem.
- Loogle: `"AlgebraicStack", "Flat"`: 0 hits.
- Mathlib grep: `ClassifyingStack|classifyingStack|GroupAlgebraicSpace`: 0 hits.
- Direct rg of `lean/WeilConjectures`, `lean/Sheaf` and the upstream name index found
  no classifying-stack theorem or algebraic-space quotient presentation. The node-id
  search has no upstream declaration. Related scheme-only action and quotient modules
  were opened and their extra scheme/affineness/field assumptions checked.
- New-definition searches are listed below and in its `mathlib_searches`.

The source read is `criteria.tex`, lemma-BG-algebraic, Tag 06PL, including the entire
converse proof; and `spaces-groupoids.tex`, definition-quotient-stack and its following
arrow description, together with lemma-quotient-stack-cocycle. The proof docstring
reproduces all five accepted DAG steps and names their inputs.

## New nodes

`def-sfb-space-groupoid-quotient-presentation` owns
`Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation`. It defines
`CategoryTheory.spaceGroupoidPresentationArrow` by actual equality transport and the
specified natural isomorphism, and `CategoryTheory.SpaceGroupoidQuotientPresentation`
by groupoid laws, fppf descent, the arrow comparison, full faithfulness, local object
lifts, and composition compatibility. Source: Stacks 044Q, 044R, 044T and 02ZP/0436.
It specializes exactly to the classifying groupoid by setting both endpoints equal.
The original scheme-only `SchemeGroupoidQuotientPresentation` cannot accept arbitrary
algebraic spaces, so it is neither duplicated nor weakened. Existing groupoid laws,
stack descent and fibred-category notions are imported and reused.

LeanSearch query "Presentation of the quotient stack of a groupoid in algebraic spaces
by fully faithful arrows and local objects" returned 8 general descent/category results,
none this interface. LeanFinder "Algebraic space groupoid quotient stack presentation"
returned 8 manifold/general-stack results. Mathlib grep
`AlgebraicSpaceGroupoidQuotientPresentation|spaceGroupoidPresentationArrow` returned 0;
direct source/project/name-index rg returned 0. Blueprint search "groupoid quotient
presentation" returned 0; DAG definition inspection found only the scheme presentation,
the algebraic-space laws and the general stackification predicate, none this notion.
The ancestor tool returned `blueprint.from.node = None`; the inherited precise place and
via chain are retained and extended by the item.

## Validation

Every compile and probe uses the prescribed scompile.py wrapper, in module mode.
The first definition module compiled without errors or warnings. The initial main-file
compile found an unqualified `pullback` resolving to the algebraic-space sheaf pullback;
this was repaired to `Limits.pullback`, with no mathematical change.

Both final modules compile cleanly in sandbox and library module modes (about 7 seconds
per file). The first delivery dry run required `import_flags` on the new definition node;
the empty list was added, as there is no imported-source flag. This is metadata only.

The repaired dry run passed preflight and all compilation checks. The recorded
stackification statement dependency is publicly imported, matching module visibility rules.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
