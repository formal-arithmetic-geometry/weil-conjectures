## Worker report

The module `Sheaf.CategoryTheory.FirstQuadrantRowCollapse` states
`CategoryTheory.first_quadrant_row_collapse`, with one `sorry` and no new definitions.
It includes both the isomorphism assertion for the actual bottom edge map and the
positive-degree vanishing consequence. The node's mathematical statement is unchanged.
Its statement dependencies gain the existing Mathlib leaf `def-sp-spectral-sequence`,
which carries the spectral-sequence structure used by the module (per STATE's
STMT_DEPS MAY GAIN LANDED NODES rule).

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- An arbitrary abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`.
  The object and morphism universes are independently and explicitly bound.
- The cohomological spectral sequence starting at page two is
  `E : E₂CohomologicalSpectralSequence C`. Its pages are Mathlib homological
  complexes of shape `ComplexShape.up' (r, 1-r)`, so its differential goes from
  `(p,q)` to `(p+r,q-r+1)`, its square is zero, and `E.iso` identifies page
  homology (kernel modulo image) with the next page. No replacement structure is used.
- First-quadrant support on page two is `hfirst`, for all integer `p q`:
  `p < 0 ∨ q < 0 → IsZero ((E.page 2).X (p,q))`.
- The abutment objects indexed by nonnegative degrees are `H : ℕ → C`.
- The decreasing filtrations are `F : ∀ n, DecreasingFiltration (H n)`;
  `antitone_step` supplies the decreasing inclusions. `htop` states `F⁰Hⁿ=Hⁿ`
  as equality to the top subobject; `hbottom` states `Fⁿ⁺¹Hⁿ=0` as equality to
  the bottom subobject. Together these give the specified finite filtration.
- Convergence is `conv n p q hpq`: `grᵖ Hⁿ ≅ E_(n+2)^(p,q)` for `p+q=n`.
  For nonnegative `p,q`, `n+2=p+q+2 > max(p,q+1)`, so this is precisely the
  stable page `E∞` in the node's convention. Choosing this one stable page
  neither adds a degeneration hypothesis nor changes convergence. Graded pieces
  are the dependency's cokernels, not a privately defined quotient.
- Vanishing of all positive rows is `hrow`, again at every integer first index.
- The conclusion constructs the canonical identifications of `E₂^(n,0)` with
  subsequent pages. `a n r` goes from page two to page `r+2`; `a n 0 = 𝟙 _`.
  `b n r` is its lift through the canonical cycle inclusion. The first equation
  `b ≫ iCycles = a` and the second equation
  `b ≫ homologyπ ≫ (E.iso ...).hom = a n (r+1)` enforce the usual passage
  to the next page. Since `iCycles` is monic, the lift is unique; induction
  fixes every `a` from the identity. These are not arbitrarily chosen isomorphisms.
- At the stable page, `a n n` lands in `E_(n+2)^(n,0)`. The inverse of
  `conv n n 0` goes to `grⁿ Hⁿ`. The equation for `f` says that its composite
  with the actual cokernel projection from `Fⁿ Hⁿ` is exactly that map.
  The projection is an isomorphism since `Fⁿ⁺¹=0`, so `f` is uniquely determined.
  Consequently `f ≫ ((F n).step n).arrow` is exactly the node's edge map,
  with its filtration inclusion retained explicitly. `IsIso` asserts that this
  morphism is an isomorphism, not just that its source and target are isomorphic.
  The existential presentation constructs the edge map and states its property
  without a hollow definition or an extra hypothesis assuming page collapse.
- The second conjunct states the particular case verbatim:
  if `IsZero (H n)` for every `0<n`, then `IsZero ((E.page 2).X (n,0))`
  for every `0<n`.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.Basic`, `CategoryTheory.Abelian`
  (`def-sp-abelian`, Mathlib leaf): its full class signature and docstring say
  preadditive, finite products, kernels, cokernels, normal monos and epis;
  the file derives zero objects and finite biproducts.
- `Sheaf.CategoryTheory.Filtration`, `CategoryTheory.DecreasingFiltration`, its
  `step` and `antitone_step`, and `DecreasingFiltration.gradedPiece`
  (`def-sp-filtration`): read the full structure, graded-piece definition and
  their Stacks 0121 docstrings. The latter is the cokernel of the successive inclusion.
- `Mathlib.Algebra.Homology.SpectralSequence.Basic`,
  `CategoryTheory.SpectralSequence`, `E₂CohomologicalSpectralSequence`, `page`,
  `iso` (`def-sp-spectral-sequence`, added existing Mathlib leaf): full structure
  and abbreviation signatures/docstrings read. The maps `iCycles` and `homologyπ`
  come from `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`, which
  was read for their full signatures and docstrings as well.

Edge cases checked before writing: `n=0` has stable page two, `a 0 0` is the
identity, and `F⁰=H⁰`, `F¹=0`, so the edge assertion still applies without a
filtration induction. The vanishing consequence excludes degree zero explicitly.
Zero abutments and the zero category are allowed; `IsZero` means categorical zero
rather than literal equality of chosen representatives. Negative bidegrees are
included in `hfirst`; positive-row vanishing is quantified over all integer first
indices. Infinite horizontal support is permitted: no uniform bound or finiteness
of the whole spectral sequence is imposed. The filtrations may have arbitrary
steps outside `[0,n+1]`; the antitone condition and the endpoints force their
values there as expected. No smallness condition on `C` is imposed beyond its
independent arbitrary Lean universes.

Searches made with the required remote search wrapper (logged in searches.jsonl):

- LeanSearch, `first quadrant spectral sequence concentrated in row zero edge map
  is an isomorphism`: service unavailable (Internal Server Error); no verdict
  inferred from this failure.
- LeanFinder, the same query: eight hits about complexes, cycle/homology maps,
  and individual homology isomorphisms; no row-collapse/abutment theorem.
- Loogle, `CategoryTheory.E₂CohomologicalSpectralSequence`: two hits, the
  spectral-sequence abbreviation and its construction from a spectral object;
  neither is a collapse theorem.
- Mathlib grep, `row_collapse|abutment|convergesTo|edgeMap`, under Algebra/Homology:
  no hits.
- `rg` of `WeilConjectures/` and `lean/Sheaf/` for first-quadrant, collapse,
  abutment and edge-map names: source convergence data exist in
  `WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic`, but no
  matching row-collapse theorem. That module's full contents were read:
  `SpectralSequence.Abutment` stores an ℕ-indexed filtration and nonempty
  graded-piece isomorphisms; it does not assert this node's result. We do not
  redefine it; the theorem uses the recorded ℤ-indexed `DecreasingFiltration`
  directly and spells out the convergence hypotheses in its binders.
  The source spectral-object edge maps concern a spectral object, not an arbitrary
  spectral sequence with its given filtration, so they are not this statement.
- `rg` of the exact item id in `WeilConjectures/`: no hit.
- `rg` of `FirstQuadrantRowCollapse|first_quadrant_row_collapse` in the upstream
  name index, Mathlib, source, and landed Sheaf modules: no hit.
- `tools/blueprint_refs.py search 'first quadrant'`: no blueprint nodes found;
  no new notion or new node is needed, since all data are expressed with the
  existing spectral sequence and filtration structures and their canonical maps.

Source checked at https://stacks.math.columbia.edu/tag/011O,
https://stacks.math.columbia.edu/tag/0132, and
https://stacks.math.columbia.edu/tag/0A4C. The local literature checkout does not
contain homology.tex, so the corresponding Stacks pages were opened directly.
011O defines degeneration/limit, 0132 gives finite-filtration convergence for the
bounded double-complex situation, and the second paragraph of 0A4C uses precisely
the row-collapse vanishing consequence. The node's own four-step proof is
included in the theorem docstring, including the canonical maps involved.

Server compile: `scompile.py M1 lem-weil-pbc-first-quadrant-row-collapse
.../FirstQuadrantRowCollapse.lean` returned exit code zero, compiled in 1.6 seconds,
with no errors or warnings. An initial bidegree presentation `(n,n-n)` needed
transport to `(n,0)`; convergence was instead indexed by `p,q` with `p+q=n`,
which is the same hypothesis and lets the edge map use `(n,0)` directly.

No STATEMENT-DISPUTED issue, statement correction, dependency module, or new node.
The independent second reader will supply its own section; none is fabricated here.

## Second reading by M1

I independently opened the node copy, the complete delivered Lean module, all three
statement dependency nodes, and the declarations below. No mathematical or Lean
mismatch was found, and no module or node signature was changed. This section is
the only change made in the second reading.

Source reading: the local checkout has no `literature/stacks-project` directory.
I read the actual Stacks `homology.tex` and `etale-cohomology.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/homology.tex and
https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex,
including the surrounding paragraphs at `definition-spectral-sequence`,
`definition-limit-spectral-sequence`, `definition-filtered`,
`lemma-first-quadrant-ss`, and `lemma-sandwich`. I also checked the rendered tags
https://stacks.math.columbia.edu/tag/011O,
https://stacks.math.columbia.edu/tag/0132, and
https://stacks.math.columbia.edu/tag/0A4C. The spectral-sequence section explicitly
permits a starting page other than one and given isomorphisms in place of literal
equalities. It assumes an abelian category, without further finiteness or
smallness. Tag 0132 concerns double complexes finite on diagonals; the present
node assumes convergence and finite filtrations explicitly, and does not assert
that every first-quadrant sequence comes from a double complex. Thus its use as
background imposes no hidden double-complex hypothesis. The application in 0A4C
has vanishing higher rows and vanishing positive-degree abutment, exactly the
particular case here; properness and surjectivity are hypotheses of that
application, not hypotheses of this general categorical lemma.

My object/hypothesis/conclusion checklist, with the rendering and verdict:

1. Arbitrary abelian category A: `{C : Type u} [Category.{v} C] [Abelian C]`.
   Matches. I read `Abelian` in Mathlib.CategoryTheory.Abelian.Basic: preadditive,
   normal monos/epis, finite products, kernels and cokernels. Its derived zero
   object and finite biproducts match `def-sp-abelian`; no extra structure is asked.
2. Pages from two, cohomological bidegrees, square-zero differential and next-page
   homology: `E : E₂CohomologicalSpectralSequence C`. Matches. I read
   `SpectralSequence.page`, `.iso`, and both cohomological abbreviations in
   Mathlib.Algebra.Homology.SpectralSequence.Basic, and `ComplexShape.up'`:
   its relation is `i + (r,1-r) = j`. These are precisely the structure carried
   by `def-sp-spectral-sequence`, not a similar-name specialization.
3. First-quadrant support on page two: `hfirst` quantifies over all `p q : ℤ`
   and requires zero if either index is negative. Matches, including negative
   bidegrees rather than merely omitting them by an index restriction.
4. Abutment in every nonnegative degree: `H : ℕ → C`. Matches the node's n ≥ 0.
5. Finite decreasing filtration from H to zero: `F : ∀ n, DecreasingFiltration
   (H n)`, `htop`, `hbottom`. Matches. I read the dependency module's `step :
   ℤ → Subobject A`, `antitone_step : Antitone step`, and `gradedPiece` defined
   as the cokernel of the successive inclusion. The endpoints force top steps
   below zero and bottom steps above n+1; no arbitrary filtration behavior beyond
   the displayed finite chain affects the theorem.
6. Convergence quotients: `conv n p q hpq`, for natural p,q with p+q=n, identifies
   `(F n).gradedPiece p` with page n+2 in bidegree (p,q). Matches. Since
   n+2 > p and n+2 > q+1, this is the node's stable value; both adjacent
   differential objects vanish there by first-quadrant support propagated through
   homology. Specifying an isomorphism makes the convergence data and edge map
   explicit, without imposing a further compatibility condition. All pieces
   0 ≤ p ≤ n are covered; outside this range both filtration graded pieces and
   the corresponding first-quadrant terms are forced zero.
7. Positive-row vanishing: `hrow : ∀ p q : ℤ, 0 < q → IsZero ...`. Matches;
   no hypothesis on the bottom row or uniform horizontal support was added.
8. Canonical bottom edge is an isomorphism for every n: the first conjunct's
   existential `a,b` starts with `a n 0 = 𝟙 _`; `b ≫ iCycles = a` and
   `b ≫ homologyπ ≫ (E.iso ...).hom = a n (r+1)` give precisely successive
   canonical passage to page homology. Matches. I read the actual `cycles`,
   `iCycles`, and `homologyπ` declarations in ShortComplex.HomologicalComplex.
   The cycle inclusion is monic, so each b is unique for a fixed a; the second
   equation then determines the next a. Under the hypotheses these maps are
   isomorphisms, since the adjacent differential objects are zero. The global
   existential family adds no freedom or strength beyond these canonical maps.
   At `a n n` the page is n+2. The equation for `f` uses `(conv n n 0 ...).inv`
   and the actual cokernel projection of the dependency's graded piece.
   Because F^(n+1)=0 that projection is invertible, making f unique.
   `IsIso (f ≫ ((F n).step n).arrow)` therefore asserts invertibility of the
   actual edge composite into H, not merely an unrelated object isomorphism.
9. Particular case: the second conjunct assumes `IsZero (H n)` for every
   positive n and concludes `IsZero ((E.page 2).X (n,0))` for those same n.
   Matches, with degree zero deliberately excluded only from this extra clause.

Edge cases: n=0 uses page two and the identity a; F^0=top and F^1=bottom
make the same quotient/inclusion construction work. Zero objects, zero terms,
and the zero abutment require no nonzero hypotheses. An abelian category already
has an object (a zero object), so an empty category is not a case covered by the
node; there is no arbitrary index set required to be inhabited. Empty schemes
and characteristic restrictions are irrelevant to this categorical lemma, and
any application to their sheaf categories is permitted. Object and morphism
universes u,v are independently declared, with no extra universe inequality or
smallness assumption. All other variables are explicitly bound.

Independent searches used different phrases from the worker:

- LeanFinder via msearch: `cohomological spectral sequence supported on bottom
  row canonical map to filtered cohomology invertible`: eight hits about
  cochain-complex factorizations, K-injectives and connected-complex homology,
  not this theorem.
- LeanSearch via msearch: `A cohomological spectral sequence supported in degree
  q zero has abutment isomorphic to its initial bottom row`: unavailable
  (Internal Server Error), not a negative search verdict.
- Loogle via msearch: the initial quoted-name query was invalid; the corrected
  `CategoryTheory.SpectralSequence` query found its structure/page/iso/category
  API, with no abutment collapse result.
- Independent rg over the entire source WeilConjectures tree, repository
  lean/Sheaf tree, and Mathlib Algebra/Homology for `row.?zero|bottom.?row|
  row.?collapse|spectral.*degenerat|degenerat.*spectral|edge.*isomorphism`:
  specialized Leray applications and unrelated rows, no matching general theorem.
  Further `degenerat|collaps|stationary|edge.*iso|iso.*edge` searches located
  upstream convergence Basic and spectral-object bottomEdge. I opened Basic's
  `pageInfinity`, `Abutment`, `AbutsTo` and the spectral-object module's
  `E₂SpectralSequenceNatAbutment`, `bottomEdge`, and surrounding signatures.
  Those use a natural-indexed spectral sequence or a spectral object with its
  particular image filtration. This module defines none of those notions again:
  it uses the recorded integer-indexed filtration and spectral sequence and
  spells out their hypotheses. No existing general row-collapse declaration
  replaces the delivered statement.
- Exact-name and node-id rg in WeilConjectures, lean/Sheaf and the upstream name
  index had no hits. No new definition node or dependency module is necessary,
  so H12/H13 add no delivery files to review.

Conventions and proof documentation: the sole theorem has `sorry` as its entire
proof; the tiny arithmetic binder transports introduce no proved helper theorem.
There is no new definition, hollow data, private notion, extra instance, statement
correction, or disputed statement. The module and theorem docstrings give the
source and exact blueprint id. I compared all four proof steps with the node:
propagation of zeros, stationary bottom row, collapsed finite filtration, and
canonical edge composite with the vanishing consequence are all present.
The signature recorded in `lean.statement` is unchanged and verified verbatim
against the file; lines are at most 100 characters and both imports are used.

Independent server compile with `scompile.py M1
lem-weil-pbc-first-quadrant-row-collapse` and the delivered module returned exit
code zero in 1.7 seconds, without errors or warnings.
