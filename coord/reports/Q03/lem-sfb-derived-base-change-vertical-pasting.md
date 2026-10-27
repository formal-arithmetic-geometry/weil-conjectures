## Worker report

The delivery states `AlgebraicGeometry.schemeDerivedBaseChange_vertical_pasting` in
`Sheaf.AlgebraicGeometry.DerivedBaseChangeVerticalPasting`, with `sorry` as its only proof.
The repair adds one definition node recording an existing construction; there are no
new Lean constructions, dependency modules, or mathematical statement corrections.
The earlier NV merge was a stage-1 split: the current node has `reviewed` but no `lean`.
It remains in `coord/queue.tsv` at stage 2. This delivery supplies the missing Lean
statement rather than resubmitting the accepted stage-1 split.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- All six objects are `Scheme.{u}`; `f : X ⟶ Y`, `g : Y ⟶ Z`, and `m : Z' ⟶ Z`
  are the three given morphisms. Both `f` and `g` have `QuasiCompact` and
  `QuasiSeparated` instances. There is no condition on `m`.
- The projections are `k : X' ⟶ X`, `f' : X' ⟶ Y'`, `l : Y' ⟶ Y`, and
  `g' : Y' ⟶ Z'`. `top : IsPullback k f' f l` and
  `bot : IsPullback l g' g m` express exactly the two fibre-product universal
  properties, including their commutativity equations. Quantifying over fibre
  products with their projections keeps every choice permitted in the node.
  Mathlib's chosen `pullback` and projections provide instances of these data.
- The first conjunct `IsPullback k (f' ≫ g') (f ≫ g) m` states the outer
  fibre-product assertion. `(top.paste_vert bot).w` supplies its commutativity
  equation to the canonical base-change constructor, without a new helper.
- `E : schemeDerivedCategory X` with `hE : schemeDerivedQCohProperty X E`
  is precisely E in D_QCoh(O_X). `hRf` renders the explicit clause that Rf_*E
  has quasi-coherent cohomology. It also follows from qcqs and `hE` by the
  recorded direct-image preservation theorem. It is not a new restriction.
- `schemeDerivedBaseChangeMap f f' l k top.w E` is beta_top;
  `schemeDerivedBaseChangeMap g g' m l bot.w ((schemeDerivedDirectImage f).obj E)`
  is beta_bot at Rf_*E; the constructor at `(f ≫ g), (f' ≫ g'), m, k`
  is beta_out. These are the dependency's existing canonical maps.
- `(schemeNormalizedDirectImageCompIso f g).inv` is rho, and the same inverse
  for `f', g'` is rho'. This existing definition chooses the comparison together
  with its right-derived-unit equation, which determines it uniquely. It does
  not choose an arbitrary element of the bare Nonempty composition theorem.
- Lean's `≫` composes left to right. The second conjunct is therefore exactly
  rho' after beta_out = Rg'_*(beta_top) after beta_bot after Lm^*(rho_E),
  with the order reversed from the conventional right-to-left circle notation.
- The shared `HasDerivedCategory.{w}` family fixes the localizations used by
  the canonical base-change dependency; `u` and `w` are separately quantified.
  There is no boundedness, flatness, Tor-independence, properness, or IsIso
  hypothesis on a base-change map.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`, and the universal property;
  `Mathlib.AlgebraicGeometry.Pullbacks` provides scheme pullbacks.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs/Basic`:
  `IsPullback` and `IsPullback.paste_vert`, for the same universal properties.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `schemeDerivedCategory`, `schemeDerivedQCohProperty` (through the base-change import).
- `WeilConjectures.AlgebraicGeometry.DerivedPullback`: `derivedPullback`
  (through the base-change import).
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage` (through the base-change import).
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap`:
  `schemeDerivedBaseChangeMap`, whose docstring and full signature were read;
  the adjunctions and pullback comparisons are normalized to the same units/counits.
- `WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`:
  `derivedDirectImageComposition`, imported as the recorded statement dependency.
- `WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate`:
  `schemeNormalizedDirectImageCompIso`, the already landed canonical comparison.
  Its definition node `def-sfb-normalized-direct-image-composition-iso` is added
  to stmt_deps. The previously cited theorem node
  `lem-sc-derived-direct-image-square-mate` does not own this definition and is
  removed from the saved packet's added statement dependencies.
  The definition is a choice from
  `RingedSpace.exists_derivedModuleDirectImageComposition`, whose full signature
  and right-derived-unit characterization were read. Nothing is defined twice.
- Proof imports: `WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh`
  (`schemeDerivedDirectImage_preserves_QCoh`),
  `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionAssociativity`
  (`derivedDirectImageComposition_associativity`), and
  `WeilConjectures.AlgebraicGeometry.DerivedAdjoint`
  (`nonempty_derivedPullbackAdjunction`). All recorded proof dependencies are imported
  directly or as the recorded statement dependency modules.

Source read: `literature/stacks-project/cohomology.tex`,
`remark-compose-base-change` (Tag 0ATL), together with the preceding
`remark-base-change`. Its diagram, functor order, and displayed composite agree
with this statement. The theorem docstring records all four accepted proof steps,
including the composition associativity and both final naturality equations.

Edge cases checked semantically: identity f, identity g, and identity m reduce to
unit/composition laws without requiring the chosen functors to be strictly identities;
E=0 and empty schemes are permitted; non-flat m is permitted because the comparison
is only asserted equal to the pasted map, never invertible. There is no restriction
to bounded objects or to a chosen representative complex. The two IsPullback hypotheses
exclude no fibre-product diagram. No node fault or disputed mathematical statement was found.

Searches actually run:

- msearch LeanFinder: `Derived base change morphisms compose for two vertically
  stacked cartesian squares of schemes`: eight hits about ordinary scheme pullback
  projections and `Scheme.Modules.pullbackComp`; no exact derived-map identity.
- msearch Loogle: `CategoryTheory.mateEquiv_vcomp, CategoryTheory.mateEquiv_hcomp`:
  zero hits for that combined query.
- msearch LeanSearch: `Derived base change maps compose for stacked cartesian squares
  of schemes`: eight hits about ordinary ring base change and underlying maps;
  no exact statement.
- msearch grep, CategoryTheory: `schemeDerivedBaseChange|mateEquiv_vcomp|mateEquiv_hcomp`:
  eleven generic mate-pasting hits; these do not state the scheme O-module claim.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for canonical derived base
  change, vertical pasting, and composition found `DerivedBaseChangePasting`
  (upper-left precomposition), `DerivedBaseChangeHorizontalPasting` (horizontal
  squares), and `DerivedSquareVerticalPasting` (pullback comparisons).
  Their signatures/docstrings are different from this vertical direct-image law.
  The search also located the normalized comparison already reused above.
- `grep -rn lem-sfb-derived-base-change-vertical-pasting lean/WeilConjectures`:
  no occurrence. No exact existing declaration was found.

Validation: the delivered file is checked using scompile.py, and delivery preflight
and per-file compilation are run by deliver2.py. Results are recorded below after execution.

`scompile.py` compiled both the sandbox check and actual library module successfully
(2.1 s and 2.0 s respectively), with no reported diagnostics. The first prescribed
`deliver2.py --no-push` passed server preflight and compilation, printing
`OK (dry run): commit dcdd8c5c718 passes the preflight and compiles; nothing pushed`.
Static checks confirm no Lean line exceeds 100 characters, the recorded signature
is verbatim, and only `lean` and the authorized added `stmt_deps` entry differ from
this item's current node. The maintainer performs the independent statement review;
this worker has not represented its own rereading as an independent agent review.

## New nodes

`def-sfb-normalized-direct-image-composition-iso` records the existing
`AlgebraicGeometry.schemeNormalizedDirectImageCompIso` in
`WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate` (line 31),
with `existing: true` and no new Lean module. Its signature is copied verbatim.
Its objects X,Y,Z and maps f,g are exactly the definition's binders; the shared
section binds the derived localizations with independent universes u,w.
The type `schemeDerivedDirectImage f ⋙ schemeDerivedDirectImage g ≅
schemeDerivedDirectImage (f ≫ g)` gives c(f,g), and its inverse gives the
item's rho. The actual body selects the isomorphism from the existential
`RingedSpace.exists_derivedModuleDirectImageComposition`, which also requires
the displayed unit equation for every homotopy-category object. This uniquely
characterizes the comparison by the right-derived universal property. Thus
this is a normalized canonical construction, including identity and zero cases,
without any qcqs, boundedness, or cohomology restrictions.

The new node cites the existing definitions of schemes, their derived categories,
and scheme derived direct image, as well as the actual ringed-space composition
existential needed for its construction. Its source is Tag 0D5T, as read in
`cohomology.tex` at `lemma-derived-pushforward-composition`; Tag 0ATL uses precisely
this canonical comparison. Its blueprint ancestor is null, as returned by
`tools/blueprint_refs.py ancestor`, and its via list prepends the item to the
item's original via list.

New-node searches (2026-10-23): LeanSearch queried canonical normalized composition
isomorphisms for derived direct image (8 hits: ordinary pushforward composition
and generic normalization); LeanFinder queried right-derived-unit-normalized
composition (8 hits: generic right-derived functor uniqueness and comparison).
The msearch Mathlib CategoryTheory grep for
`schemeNormalizedDirectImageCompIso|derivedModuleDirectImageComposition|derivedDirectImageComposition`
returned 0 hits. Project grep found the exact definition in the upstream module;
Sheaf hits only use it. DAG grep and inspection found theorem nodes using it,
but no definition node recording it. Blueprint search returned 0 matches.
The queries and returned declaration names are recorded in `mathlib_searches`.

## Returned-delivery repair

The immutable-head return at `7cde4b1a4ed1` identified H2: the added
`lem-sc-derived-direct-image-square-mate` statement dependency was used only
for an unowned plain definition. It is replaced by the new definition node
above. The Lean module is byte-identical to the saved delivery. Its import of
`DerivedDirectImageSquareMate` is retained, so the square-mate theorem remains
available in the proof route without treating that theorem as the definition
needed to type the item. The accepted natural-language statement, proof and
proof_deps remain unchanged. No statement_change is needed.

Before repair, the required saved-packet dry run passed with commit
`199b58816cf`; this did not push anything. A comparison with the current shared
base found only the saved `lean` and added `stmt_deps` fields differed. The
current server source of `DerivedDirectImageSquareMate`, read using
`scompile.py --source`, agrees with the locally inspected definition.

Self-check: the new node has exactly the H12 fields, real existing data, empty
proof/proof_deps, a definition id in the item's chapter, three kinds of search,
and a citation from the item. The item's original statement/proof fields and
Lean signature are unchanged. The maintainer supplies the independent review.

## Saved-packet retry validation

The required first dry run of the retained repair packet found two mechanical
record defects: the existing declaration signature began with `noncomputable def`
instead of the parser's declaration keyword `def`, and the new node omitted
`import_flags`. The record now starts at `def`, has `import_flags: []`, and uses
`branch: slopmaster2` for the existing WeilConjectures declaration, resolving the
branch advisory as well. No Lean source or mathematical statement changed.
The requested definition-node replacement is retained; the square-mate theorem
is still imported as part of the proof route.

Retry results: `scompile.py` passed both its sandbox check (2.1 s) and the actual
library module (2.0 s), without diagnostics. The corrected
`deliver2.py --no-push` passed preflight and per-file compilation, printing
`OK (dry run): commit 2a225f4d937 passes the preflight and compiles; nothing pushed`.
The final self-check confirms the item differs from the current shared node only
in `lean` and the addition of `def-sfb-normalized-direct-image-composition-iso`
to `stmt_deps`; neither the original statement nor the proof fields changed.
Both recorded signatures match their declaration source verbatim.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
