## Worker report

The module `Sheaf.AlgebraicGeometry.StackRepresentableUnramifiedDescent` states
`CategoryTheory.stack_representable_unramified_descent`, with its sole proof `sorry`.
It introduces no definitions, axioms, helper theorems or new nodes. The node's
natural-language statement and accepted proof are unchanged. I read the local Stacks
source `stacks-properties.tex`, Section 04XB, especially
`lemma-property-spaces-too` and `lemma-check-property-covering` (04XD), including
the list explicitly containing unramified morphisms. This is its specialization
P = unramified. The source proof's phrase making T x_B V the covering is a typo;
the cover is T x_B W, as the already accepted DAG proof correctly says.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. All scheme tests and spaces are over this
  same S. `A` and `B` are `BasedCategory` objects over `Over S`, with their object
  and morphism universes explicitly and independently declared.
- The hypotheses that A and B are algebraic stacks are `hA` and `hB`, using
  `IsAlgebraicModuliStack`. Its definition is precisely `IsModuliStack`,
  `HasAlgebraicSpaceDiagonal`, and existence of a smooth surjective scheme atlas.
  Thus smooth atlases are retained, with no replacement by etale atlases.
- The morphism f is `f : BasedFunctor A B`. Its representability by algebraic
  spaces is `hf : IsRepresentableByAlgebraicSpaces f`. The recorded definition
  uses every scheme 2-base change and an actual equivalence over its projection.
- W is `W : AlgebraicSpace S`, the existing full subcategory of fppf sheaves with
  representable diagonal and a surjective representable etale scheme atlas.
  `q : BasedFunctor (discreteModuli W.obj.obj) B` is exactly the given map from W.
- Surjectivity after every scheme base change is `hs`. For every scheme T/S and
  every t : T -> B it supplies an algebraic space Z and its actual projection p
  representing T x_B W, using `HasSpaceBaseChange q T t Z p`, together with
  `SpaceMapIsSurjective Z T p`. The latter says every point of T is the image of
  a point on an etale scheme chart of Z. This is surjectivity of the space
  projection, not an unrelated map or mere existence of a nonempty fibre.
  Existence of such a presentation is already implied by representability of
  q, itself a consequence of B's diagonal; it is not an extra hypothesis.
  The existential choice of a presentation changes nothing since the comparison
  is over T and surjectivity is preserved by equivalence.
- Flatness is `hflat : ModuliSpaceTest @Flat q`; local finite presentation is
  `hlfp : ModuliSpaceTest @LocallyOfFinitePresentation q`. `ModuliSpaceTest`
  uses every scheme target base change, a representing algebraic-space
  projection, and every representable etale scheme chart of its source.
- V is the actual existing `moduliTwoFiberProduct q f` and V -> W is its
  `moduliTwoFiberFst q f`. These definitions retain the isomorphism in the
  triple defining the 2-fibre product and the actual first projection.
- The conclusion is the equivalence `ModuliSpaceTest @IsUnramified f ↔
  ModuliSpaceTest @IsUnramified (moduliTwoFiberFst q f)`. Thus both directions,
  all scheme base changes, and all etale scheme charts are retained. For the
  space-to-space projection on the right this is exactly the statement's
  convention of testing properties after scheme base change on etale charts.
  `IsUnramified` is the recorded conjunction of locally finite type and an
  open-immersion scheme diagonal; formal unramifiedness alone is not substituted.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `IsModuliStack`, `HasAlgebraicSpaceDiagonal`, `discreteModuli`,
  `HasSpaceBaseChange`, `IsRepresentableByAlgebraicSpaces`,
  `SpaceMapIsSurjective`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`.
  Their signatures and docstrings specify the existing fibred-groupoid,
  equivalence-over-the-projection and 2-fibre-product conventions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, and its atlas condition.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`, `SpaceMapIsSmooth`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSpaceTest`, which
  is general in both based categories and in the scheme morphism property P;
  despite the module name it assumes neither category is DM.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with the
  recorded stalkwise equivalence `Flat.iff_flat_stalkMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (all affine scheme charts).

Two landed definition nodes are added to `stmt_deps`:
`def-sfb-algebraic-moduli-stack` owns the exact algebraic-stack predicate used;
`def-sfb-dm-stack-morphism-properties` owns the general chartwise test used.
These are existing definitions, not new nodes or dependency repairs.

The declared proof dependencies with usable records are imported privately:
`StackChartwiseSmoothEtaleCalculus` (its base change, composition, implication
and surjectivity-chart theorems), Mathlib `Sites.Fpqc` (`fpqcPrecoverage`),
`Morphisms.UniversallyOpen` (`UniversallyOpen.of_flat`),
`RingTheory.Spectrum.Prime.Topology` (`PrimeSpectrum.compactSpace`,
`iSup_basicOpen_eq_top_iff`), `Limits.Shapes.Pullback.HasPullback`
(`pullback`, its projections and lift),
`AlgebraicSpaceFibreProductsEtaleCovers` (`fibreProduct_isAlgebraicSpace`,
`etaleCover_pullback`, `etale_fibreProduct_isScheme`),
`ChartwiseEtalePermanence` (`chartwise_etale_permanence`), and
`Morphisms.UnramifiedDescent`
(`locallyOfFiniteType_and_openDiagonal_of_fpqcCover`). Their signatures and
proof docstrings were read. Two proof-only nodes currently have no Lean record,
Mathlib match or module: `lem-sfb-stack-diagonal-space-source-representability`
and `lem-sfb-space-unramified-permanence`. Their imports cannot yet be supplied;
the theorem docstring names their precise uses. Neither is needed to state the
item, and no new proof obligation is manufactured to replace them.

Edge cases checked before writing:

- Empty A, W, T, and empty scheme charts remain allowed: no `Nonempty` binder.
  For an empty W, hs can hold only when every test projection is surjective,
  forcing the corresponding target to be empty; the conclusion is consistent.
- Identity covers and covers with empty or disconnected source are included.
- No finite-type assumption on S, A or B; no noetherian, separated, proper,
  quasi-compact or quasi-separated assumption is added. In particular a flat
  lfp surjective cover need not be quasi-compact.
- No unramifiedness, surjectivity or flatness is assumed for f itself; these
  would incorrectly restrict the equivalence.
- Unramifiedness uses locally finite TYPE, not locally finite presentation.
- There is no characteristic restriction, fixed atlas or fixed scheme test.
  Universes u, v₁, w₁, v₂, w₂ are explicitly bound; `autoImplicit false` is set.
- No statement correction or disputed statement was needed.

Searches for an existing statement (2026-10-24):

- `msearch.py` LeanFinder: "A representable morphism of algebraic stacks is
  unramified if and only if its base change along a surjective flat locally
  finitely presented algebraic space cover is unramified" returned eight
  scheme formal-unramified/base-change/composition results, not this statement.
- `msearch.py` Loogle: `"FormallyUnramified", "Surjective"` returned the two
  ring/algebra quotient lemmas and scheme formal-unramified descent along a
  surjective flat quasi-compact morphism. None concerns algebraic stacks or the
  present unramified equivalence along a possibly non-quasi-compact cover.
- `msearch.py` grep: `unramified.*descent|[Aa]lgebraic[Ss]tack|ModuliSpaceTest`
  returned zero Mathlib matches.
- `msearch.py` LeanSearch: "A representable morphism of algebraic stacks is
  unramified if its pullback along a surjective flat locally finitely presented
  map is unramified" returned eight ring and scheme formal-unramified results,
  none stating the stack theorem.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the item ID,
  `unramified.*[Dd]escent`, `ModuliSpaceTest` and `IsAlgebraicModuliStack` found
  the owning definitions, scheme unramified descent, locally quasi-finite stack
  descent, and a reference to this item in `UnramifiedDiagonalEtaleAtlas`.
  There is no existing declaration of this theorem.
- `rg` on `dag/lean_names_upstream.json`, `lean/WeilConjectures` and `lean/Sheaf`
  for the proposed module/name and item ID found only the existing consumer's
  docstring reference; there is no name collision.

Validation: the prescribed `scompile.py Q04
lem-sfb-stack-representable-unramified-descent <module>` completed with exit 0
in both sandbox and library modes, with no errors or unexpected warnings.
Every Lean line has at most 100 characters. The node's `lean.statement` is
extracted verbatim from the theorem keyword through its complete signature.
The dry run and push are performed with the prescribed `deliver2.py` wrapper.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
