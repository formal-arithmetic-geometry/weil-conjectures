## Worker report

The module `Sheaf.AlgebraicGeometry.RepresentableStackDiagonalCriterion` states
`CategoryTheory.representableStack_diagonal_criterion`, with its sole proof `sorry`.
It introduces no definition. The natural-language statement is unchanged. Two already
landed definition nodes are added to `stmt_deps` to cite the existing relative diagonal,
scheme-test, and algebraic-space separatedness declarations used in the signature.
No dependency module or new node is necessary.

I read the current node, every statement dependency and its recorded Lean declaration,
the helper nodes below, the stage-2 brief, stage document, worker role, delivery-errors
section H, setup/state, tools README, and the CompactObject example (the Sheaf example
is withdrawn, so I also read its recorded upstream replacement). No repair note exists.
The source was checked directly in `literature/stacks-project/stacks-morphisms.tex`,
`lemma-properties-diagonal-representable` (04YQ), parts (1), (3), (5), and
`lemma-representable-separated-diagonal-closed` (04YS), conditions (1)--(3).
The node intentionally specializes the source's algebraic stacks to DM stacks.

Hypothesis and clause correspondence:

- An arbitrary base scheme is `{S : Scheme.{u}}`; `X` and `Y` are independently sized
  `BasedCategory.{v₁, w₁}` and `BasedCategory.{v₂, w₂}` over `Over S`.
- A morphism over S is `f : BasedFunctor X Y`.
- The two DM hypotheses are `hX : IsDeligneMumfordModuliStack X` and
  `hY : IsDeligneMumfordModuliStack Y`. Their existing definition includes stack descent,
  the algebraic-space diagonal and a surjective étale scheme atlas.
- Representability by algebraic spaces is exactly
  `hf : IsRepresentableByAlgebraicSpaces f`. Its `HasSpaceBaseChange` witnesses compare
  the actual first projection by a vertical `ModuliTwoIso`, not an unrelated space map.
- The canonical relative diagonal is `moduliRelativeDiagonal f`, sending x to
  `(x, x, id)` and arrows to their two equal components in `moduliTwoFiberProduct f f`.
- Its scheme representability, monomorphism and local quasi-finiteness are jointly
  `ModuliSchemeTest (fun _ _ p ↦ Mono p ∧ Scheme.Hom.IsLocallyQuasiFinite p)`.
  Here p is a scheme morphism. The definition quantifies over every scheme T and every
  map from its discrete fibred category to the relative self-product, and produces a
  representing scheme and an equivalence compatible with the actual projection.
  `Mono p` is the scheme monomorphism, hence injectivity on all functors of points.
  The recorded `Scheme.Hom.IsLocallyQuasiFinite` includes local finite type, unlike
  Mathlib's weaker bare `LocallyQuasiFinite` predicate.
- Condition (1) is the universally quantified `T` and `t`, with existential algebraic
  space Z and actual projection p, `HasSpaceBaseChange f T t Z p`, followed by
  `AlgebraicSpace.MapToSchemeIsSeparated Z T p`. This existing predicate is precisely
  `IsRepresentableWith (fun _ _ q ↦ IsClosedImmersion q.left) (pullback.diagonal p)`.
  Thus separatedness is tested on every scheme pullback of the space's actual diagonal.
  The existential presentation imposes no extra representability hypothesis: that
  presentation already exists by hf, and separatedness is invariant under presentation.
- Condition (2) is `ModuliSchemeTest @IsClosedImmersion (moduliRelativeDiagonal f)`.
- Condition (3) is `ModuliSchemeTest @IsProper (moduliRelativeDiagonal f)`.
- The conclusion has the form `A ∧ (B ↔ C) ∧ (C ↔ D)`: A gives the three initial
  assertions, while the two iff clauses are exactly the equivalence of all three
  conditions. No universal-closedness fourth condition from 04YS was added.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its category and Hom.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `IsDeligneMumfordModuliStack`,
  `IsRepresentableByAlgebraicSpaces`, `HasSpaceBaseChange`, `discreteModuli`, and the
  `moduliTwoFiberProduct` / `moduliTwoFiberFst` / `ModuliTwoIso` constructions used by
  the recorded scheme-test and diagonal interfaces.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsRepresentableWith` underlying the separatedness predicate.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, its projections and their universal property.
  Separatedness uses the canonical `pullback.diagonal` of the actual presheaf map.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, using IsQuasiFiniteAtPoint.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- Added landed node `def-sfb-dm-stack-morphism-properties`, module
  `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `CategoryTheory.ModuliSchemeTest`
  and `CategoryTheory.moduliRelativeDiagonal`.
- Added landed node `def-sfb-proper-curve-moduli`, module
  `Sheaf.AlgebraicGeometry.ProperCurveModuli`:
  `AlgebraicGeometry.AlgebraicSpace.MapToSchemeIsSeparated`.

Existing proof dependencies are plain imports: SeparatedLocallyQuasiFiniteSpaceRepresentable
(`exists_scheme_of_separated_locally_quasi_finite`), Mathlib ZariskisMainTheorem
(`IsClosedImmersion.iff_isProper_and_mono`), AlgebraicSpaceFibreProductsEtaleCovers
(`fibreProduct_isAlgebraicSpace`), and EtaleSmoothZeroDimensionalFibres
(`smooth_and_fibre_dimension_zero_of_etale`). The recorded statement dependency
StablePointedModuliGroupoids is also a proof dependency. The other four proof nodes have
no current Lean records: space-lft-cancellation, space-lft-monomorphism-separated-lqf,
stack-finite-type-calculus, stack-isom-space-locally-finite-type (all with `lem-sfb-`
prefix). They are not needed to state this theorem and are not imported or restated.
The docstring retains their roles in the six-step natural-language proof.

Edge cases checked mathematically before writing:

- The empty base and empty source are allowed, with empty representing scheme tests;
  no Nonempty or existence-of-points hypothesis is imposed.
- An identity of DM stacks has equivalence relative diagonal, even when the stack has
  automorphisms. We test its scheme pullbacks, rather than incorrectly requiring the
  total-category diagonal to be a categorical monomorphism.
- A scheme atlas `Spec k → BG` for a finite étale group illustrates nontrivial target
  stabilizers: representability gives faithful fibres, not trivial target inertia.
- A nonseparated scheme such as the doubled-origin line over a field illustrates why
  local quasi-finiteness and monomorphism of the relative diagonal do not imply its
  properness or closedness. Those remain equivalent conditions, not unconditional claims.
- No finite-type, quasi-compactness, separation, characteristic or field hypotheses on
  the base or the original map are added. All scheme tests use the base scheme universe;
  the stack object and morphism universes stay independent.

Searches (the msearch wrapper records full results in `searches.jsonl`):

- LeanFinder: "A morphism of Deligne Mumford stacks representable by algebraic spaces
  has a scheme representable monomorphic locally quasi finite diagonal, and is separated
  iff its diagonal is closed or proper". Eight hits, all scheme-level statements such
  as `IsSeparated.isSeparated_eq_diagonal_isClosedImmersion`; no stack theorem.
- Loogle: `AlgebraicGeometry.IsSeparated, CategoryTheory.IsRepresentableByAlgebraicSpaces`.
  Zero hits; the stack predicate is not in Mathlib's search index.
- Mathlib grep via msearch: `IsDeligneMumford|Moduli.*[Dd]iagonal|AlgebraicStack`.
  Zero hits.
- LeanSearch: "Diagonal of a representable morphism of algebraic stacks is representable
  by schemes, a monomorphism and locally quasi finite; separated iff closed immersion or
  proper diagonal". Eight scheme-level hits (IsSeparated, diagonal, quasiSeparated), none
  with the stack statement.
- Direct rg of `lean/WeilConjectures` for the item id, representable-diagonal patterns,
  `moduliRelativeDiagonal`, and the chosen theorem name found no matching declaration.
- Direct rg of `lean/Sheaf` found the existing relative diagonal and scheme-test vocabulary
  in DmStackMorphismProperties and separatedness in ProperCurveModuli. Other diagonal
  results concern Artin representability, inertia or absolute diagonals, not this theorem.
- DAG/name-index searches for ModuliSchemeTest, moduliRelativeDiagonal and separatedness
  confirmed their recorded owners; the existing declarations are reused.

No STATEMENT-DISPUTED issue or statement correction was necessary. All declarations and
universes are explicit, with `set_option autoImplicit false`. There are no helper
constructions, local notation, hidden choices, or postponed definition data.

Validation: prescribed scompile.py on 2026-10-24 compiled the delivered module in sandbox
mode (4.3 seconds) and library mode (3.7 seconds), with no errors or unexpected warnings.

## Second reading by Q138

A separate pass in this worker session reopened the JSON statement and Lean signature,
then unfolded the recorded ModuliSchemeTest, HasSpaceBaseChange, relative diagonal and
MapToSchemeIsSeparated definitions in their source modules. This is a self-check; the
maintainer supplies the independent review, as the dispatcher brief specifies.

The base scheme and two DM hypotheses match literally; independent stack universes are
retained. hf is exactly representability by algebraic spaces. The first conjunct supplies
one genuine representing scheme for each diagonal test with both Mono and the recorded
local-quasi-finite predicate. The first iff compares separated algebraic-space base changes
with closed-immersion scheme tests of the canonical relative diagonal. The second iff
compares those same closed-immersion tests with proper tests. IsSchemeModuliBaseChange and
HasSpaceBaseChange both retain their projection comparisons, so no arbitrary equivalence
or unrelated map replaces the base change. The three conditions are neither assumed nor
asserted unconditionally. No mismatch was found and no correction to the mathematical
statement was made. The two added landed definition-node dependencies make the existing
vocabulary's ownership explicit. Every theorem proof remains sorry.
