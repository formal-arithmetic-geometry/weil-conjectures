## Worker report

The module `Sheaf.AlgebraicGeometry.StackUnramifiedLocusBaseChange` states
`CategoryTheory.stack_unramified_locus_baseChange`. Its only proof is `sorry`.
The six-step docstring carries all six DAG proof steps and their named prerequisites.
No definition, helper theorem, or additional node is introduced. The node's statement
and proof are unchanged; four already landed definition nodes are added to stmt_deps
so that all vocabulary used by the statement is recorded.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; `X : AlgebraicSpace S` is the source.
  `discreteModuli X.obj.obj` is exactly its discrete fibred groupoid, retaining the
  actual maps of test schemes, rather than a replacement category of unrelated objects.
- The algebraic stack is `Y : BasedCategory.{v₁, w₁} (Over S)` with
  `hY : IsAlgebraicModuliStack Y`. This predicate includes stack descent, a representable
  diagonal, and a smooth surjective scheme atlas. It does not assume a DM atlas.
- The map is `f : BasedFunctor (discreteModuli X.obj.obj) Y`.
  `hf : IsRepresentableByAlgebraicSpaces f` is precisely its representability.
- Local finite type is `hft : ModuliSpaceTest @LocallyOfFiniteType f`.
  Unfolding the existing definition: every scheme 2-base change has an algebraic-space
  presentation over the test scheme, and all of its representable etale scheme charts
  have locally finite type structural composite. This is the node's specified test.
- `∃ W : OpenModuliSubstack (discreteModuli X.obj.obj)` gives the open subspace.
  A full open substack of this discrete groupoid is precisely an open subspace of X:
  the object predicate gives a subfunctor, and the structure's scheme pullback condition
  says its inclusion is representable by open immersions. The use of this existing
  encoding does not replace an open by a mere point subset.
- The first `ModuliSpaceTest @IsUnramified` applies to the full inclusion followed by f,
  so it asserts exactly that f restricted to W is unramified. The next conjunct quantifies
  over every open Z with the same property and concludes `Z.IsContainedIn W`.
- For arbitrary `Y' : BasedCategory.{v₂, w₂} (Over S)` and `hY'`, the map
  `g : BasedFunctor Y' Y` is required only to be representable by algebraic spaces.
  There is no flatness, smoothness, surjectivity, or finite type assumption on g.
  `moduliTwoFiberProduct g f` is the actual X', with its first projection f' and second
  projection p. Although X' is displayed in its actual 2-fibre-product presentation,
  representable pullback over the space X identifies it with an algebraic space; no
  additional representability or presentation hypothesis on X' is imposed.
- The existential W' is unramified and contains every other unramified open of X'.
  `∀ x, W'.property x ↔ W.property ((moduliTwoFiberSnd g f).obj x)` says that W' is
  exactly p inverse image of W, on all objects, not just field-point classes.
- Scheme specialization is universally quantified separately as T, t, V, c.
  `IsEtaleModuliMap c` requires the chart to be etale, with no surjectivity assumption.
  `r : V ⟶ T` and the displayed `ModuliTwoIso` identify r with the actual composite
  through the first projection. This is a way of naming that composite, not a new
  condition on the chart: any such composite to the discrete representable h_T is
  induced by its unique scheme map, up to the stated isomorphism over schemes.
- The existential E, j, e represents V ×_X W. `IsOpenImmersion j.left` makes it an
  actual open subscheme; `IsSchemeModuliBaseChange e j` retains the representing
  equivalence and its compatibility with the projection to V. Thus `Set.range j.left`
  is exactly c inverse image p inverse image W.
- Its equality with `⋃ U : {U : V.left.Opens // IsUnramified (U.ι ≫ r.left)}, ↑U.val`
  is the specified union of all unramified open subschemes of V. The final quantified
  equivalence identifies membership with an open neighbourhood U containing x and
  unramified restriction `U.ι ≫ r.left`.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, and scheme-test representability.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `discreteModuli`,
  `discreteModuliMap`, `ModuliTwoIso`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`,
  `IsRepresentableByAlgebraicSpaces`, and `HasSpaceBaseChange`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, used
  through the algebraic-stack atlas definition.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`, exactly
  local finite type and an open-immersion scheme diagonal.
- Added landed definition dependency `def-sfb-algebraic-moduli-stack`, module
  `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`.
- Added landed definition dependency `def-sfb-open-moduli-substack`, module
  `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `OpenModuliSubstack`,
  `fullModuliInclusion`, `OpenModuliSubstack.IsContainedIn`, `moduliTwoFiberSnd`.
- Added landed definition dependency `def-sfb-dm-stack-morphism-properties`, module
  `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSpaceTest`. This
  definition quantifies over arbitrary based categories, and implements exactly the
  representable algebraic-space tests required here, even for non-DM target stacks.
- Added landed definition dependency `def-sfb-moduli-chart-normalization`, module
  `Sheaf.AlgebraicGeometry.ModuliChartNormalization`: `IsEtaleModuliMap`,
  `IsSchemeModuliBaseChange`. All four added nodes have usable landed Lean records.
- The stated proof dependencies `lem-sfb-stack-chartwise-smooth-etale-calculus` and
  `lem-a1-space-etale-open-image` are imported privately from
  `StackChartwiseSmoothEtaleCalculus` and `AlgebraicSpaceEtaleOpenImage` respectively.
  The other proof-only prerequisites currently have no Lean record and so have no
  module to import. They remain in proof_deps and are named in the proof docstring.

Sources read: local `stacks-properties.tex`, lemma-local-source (06M3) and
remark-local-source-apply (06M5), especially item (3); local `spaces-morphisms.tex`,
lemma-where-unramified (05W2) and its etale-chart proof. These agree with the node.
No STATEMENT-DISPUTED flag, statement correction, or dependency-interface fault.

Edge cases checked: empty X and empty charts permit the empty open and empty union;
no point is required to exist. If f is unramified everywhere its maximal open is all X;
identity base change and identity scheme charts recover the same locus. Arbitrary
representable g includes nonflat maps. The chart c need not be surjective. Neighbourhoods
are arbitrary opens, not affine or quasicompact opens. No characteristic, Noetherian,
separatedness, finiteness of the atlas, or dimension assumption is imposed. All universes
are explicit, with the scheme tests in the same u as S, and independent object and
morphism universes for both target stacks. `set_option autoImplicit false` is enabled.

Searches made (2026-10-24), before writing:

- msearch leanfinder: “The unramified locus of a representable locally finite type
  morphism of algebraic stacks is open and commutes with arbitrary representable base
  change”. Eight hits, including `Algebra.isOpen_unramifiedLocus` and scheme
  `FormallyUnramified.isOpenImmersion_diagonal`; no stack-locus statement.
- msearch loogle: `AlgebraicGeometry.IsUnramified, CategoryTheory.IsRepresentableByAlgebraicSpaces`.
  No hits; the endpoint does not know these project declarations.
- msearch leansearch: “For a representable morphism of algebraic stacks locally of finite
  type, the largest open on which it is unramified commutes with base change”. Eight
  ring/scheme permanence and diagonal hits, no equivalent stack theorem.
- msearch grep: `unramified.*[Ll]ocus|[Ll]ocus.*unramified` in AlgebraicGeometry: zero hits.
  Direct rg, case-insensitive, in Mathlib AlgebraicGeometry and RingTheory/Unramified
  found the ring unramified-locus API, not this stack theorem.
- rg in `lean/WeilConjectures` for unramified/locus found ring and scheme results;
  search for the item id there found nothing. No existing stack locus theorem.
- rg in `lean/Sheaf` for unramified loci, `SpaceMapIsUnramified`, `ModuliSpaceTest`,
  and open-substack/open-subspace APIs found the reusable definitions listed above
  and the scheme `unramifiedLocus_baseChange`, but no theorem with this statement.
  Searches for `stack_unramified_locus_baseChange` in both project trees and
  `dag/lean_names_upstream.json` found no existing declaration with that name.

Validation: the prescribed scompile.py compiled the file in sandbox and library module
modes successfully, without errors or non-sorry warnings. Dry-run and delivery results
are recorded below after the wrapper completes.

## Second reading by Q119

I reread the node, source excerpts, dependency definitions, and final signature after
compilation. The four major clauses are all present: largest open, representable arbitrary
base change, the exact scheme-chart inverse image union, and its pointwise neighbourhood
criterion. I checked particularly the order of the two fibre-product projections and
that e presents the pullback of this particular W, with projection j. There is no
surjectivity requirement on c and no flatness requirement on g. The only record adjustment
was to cite the four already landed definitions explicitly. No statement mismatch was
found. This is a worker self-check; the maintainer supplies the independent review,
as prescribed in the dispatch brief. No other agent was started.

Dry run: `deliver2.py Q119 lem-sfb-stack-unramified-locus-base-change --no-push`
printed `OK (dry run): commit 0a463e5336d passes the preflight and compiles; nothing pushed`.
