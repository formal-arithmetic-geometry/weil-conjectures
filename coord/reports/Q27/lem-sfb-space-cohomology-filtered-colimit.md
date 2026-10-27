## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceCohomologyFilteredColimit` states
`AlgebraicGeometry.AlgebraicSpace.isIso_cohomology_filteredColimit`, with its whole proof
postponed by `sorry`. It states Stacks 073E (`spaces-cohomology.tex`, `lemma-colimits`),
whose statement and proof were read in the local Stacks source. No definition is introduced,
no theorem is proved, and the item's natural-language statement and proof remain unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The scheme S is `{S : Scheme.{u}}`, using Mathlib's `AlgebraicGeometry.Scheme`.
- The algebraic space over S is `(X : AlgebraicSpace S)`, using the recorded full
  subcategory of fppf sheaves with representable diagonal and a surjective étale atlas.
- Quasi-compactness is `(hqc : CompactSpace (Point X.obj.obj))`. `Point` consists of
  field-valued point classes; its existing `pointTopologicalSpace` instance is the final
  topology of étale scheme charts, hence the usual atlas topology. `CompactSpace` means
  precisely that every open covering admits a finite subcover.
- Quasi-separatedness is `(hqs : IsAbsolutelyQuasiSeparated X)`. The recorded definition
  uses Stacks 0AHR(3): every fibre product of two affine schemes mapping to X has compact
  point space. This is absolute quasi-separatedness, including over a base S that is
  not quasi-separated. No quasi-compactness or separation of S is imposed.
- The small filtered category is `(D : Type (u + 1)) [SmallCategory D] [IsFiltered D]`.
  `IsFiltered` includes nonemptiness, common receiving objects and equalization of
  parallel arrows, equivalently cocones on finite diagrams.
- The diagram of abelian sheaves is
  `(F : D ⥤ Sheaf X.etaleTopology AddCommGrpCat.{u + 1})`. Both `X.EtaleSite` and
  `X.etaleTopology` are the recorded small scheme-object étale site, not the enlarged site.
- Every nonnegative degree is `(q : ℕ)`, including zero.
- Cohomology is `Sheaf.functorH.{u + 1, u + 1} X.etaleTopology q`, Mathlib's global
  abelian-sheaf cohomology functor (Ext from the constant free rank-one integer sheaf).
  This is the existing global-cohomology implementation of the recorded site/cohomology
  convention and computes the right derived functors of global sections. It does not
  evaluate at a nonexistent terminal scheme chart.
- `[HasExt.{u + 1} (Sheaf X.etaleTopology AddCommGrpCat.{u + 1})]` fixes the usual small
  Ext groups. This is standard enough-injectives infrastructure, not an additional
  geometric restriction or an acyclicity assumption. The scheme-object site has object
  universe u+1 and morphism universe u, and the coefficient/index/Ext universe is u+1.
  These universes are explicit; the site object and morphism universes are not equated.
  Sheafification and both colimits are supplied by Mathlib instances, not assumed.
- The displayed map is exactly `colimit.post F (Sheaf.functorH ... q)`, with source
  `colimit (F ⋙ Sheaf.functorH ... q)` and target
  `(Sheaf.functorH ... q).obj (colimit F)`. Mathlib's `colimit.ι_post` says its composite
  with each group coprojection is the cohomology image of the corresponding sheaf
  coprojection. This determines the canonical map, without an arbitrary-map parameter.
  `colimit F` is taken in the category of abelian sheaves, not presheaves.
- The conclusion `IsIso (...)` asserts exactly that this map is an isomorphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its locally affine
  locally ringed space signature and docstring.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `EtaleSite`, `etalePrecoverage`, `etaleTopology`; the full definitions
  and their docstrings were read.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, whose record explicitly retains
  Mathlib `Sheaf`, `Sheaf.H'` and the cohomology functors for the cohomology components.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `Point` and `schemePointMap`;
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated` (full affine-test definition).
- Mathlib `CategoryTheory.Sheaf.functorH`, `Sheaf.H`, `Sheaf.H.map` in
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`; `Limits.colimit.post` and
  `Limits.colimit.ι_post` in `Mathlib.CategoryTheory.Limits.HasLimits`.

The item's `stmt_deps` gains only the already-landed definition nodes
`def-a1-space-point-topology` and `def-sfb-space-absolute-quasi-separated`, whose precise
interfaces are used above. There are no new nodes or dependency-module repairs.

Available proof dependencies are imported without `public`:
`AlgebraicSpaceAffineEtaleCover`, `ChartwiseEtalePermanence`, Mathlib scheme affine-qcqs
infrastructure, `SiteFiniteCoverCohomologyColimit`, Mathlib enough-injectives and
`EquivalenceDerivedSections`. The full five-step natural-language proof is in the theorem
docstring. The proof-only nodes `lem-trf-space-enlarged-site-scheme-density` and
`lem-sfb-qcqs-space-fibre-product` have no recorded Lean declaration in the read DAG, so
there is no module to import for them. Neither is needed to type the statement.

Edge cases checked before writing:

- X may be empty: compactness and absolute quasi-separatedness allow it; its abelian
  sheaf category has zero global cohomology. No point or nonempty atlas is requested.
- q=0 is included and gives the usual global-section comparison.
- A filtered category is nonempty by definition; the empty index category is correctly
  excluded. No directed-poset restriction or chosen initial object is imposed.
- The zero diagram and a singleton indexing category are allowed. All colimits are sheaf
  colimits, so there is no assumption that sheaf colimits are computed sectionwise.
- S is arbitrary, including a non-qcqs scheme; absolute rather than relative
  quasi-separatedness avoids silently changing that hypothesis.

Searches (all performed for this item; msearch results are in the sandbox search log):

1. `msearch.py leanfinder`: "Etale cohomology of a quasi compact quasi separated algebraic
   space commutes with filtered colimits". Eight hits, involving schemes, scheme global
   sections or basic étale infrastructure; none states the algebraic-space result.
2. `msearch.py loogle`: "CategoryTheory.Sheaf.H, CategoryTheory.Limits.colimit.post".
   Zero hits. The actual declarations were nevertheless located and read in Mathlib.
3. `msearch.py grep`, within Mathlib CategoryTheory:
   `cohomology.*colimit|colimit.*cohomology`. One unrelated nonabelian H1 comment.
4. `msearch.py leansearch`: "Etale cohomology of a quasi compact quasi separated algebraic
   space commutes with filtered colimits of abelian sheaves". Eight hits, including
   `Sheaf.hasFilteredColimitsOfSize`, `Sheaf.ab5ofSize` and `colimitLimitIso`; these are
   infrastructure, not this statement.
5. `rg` in `lean/WeilConjectures` for the item id: no hit. Searching for cohomology/colimit
   found scheme-only results (`Sites.CohomologyFilteredColimit`,
   `EtaleCohomologyFilteredColimit`) and general-site tools, not a statement for spaces.
6. `rg` in `lean/Sheaf` for cohomology/colimit and algebraic-space notions found
   `SiteFiniteCoverCohomologyColimit` (a general criterion with extra site-cover inputs),
   and the consumer `SpaceGradedCohomologyFinite`; neither states this item. Searching
   qcqs interfaces found the two existing definition nodes now cited, avoiding a copy.
7. `rg` in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for the chosen declaration name found no existing name.

Validation: the delivered file compiled cleanly using `scompile.py` in both sandbox
mode and its actual module name, about 2.1 seconds each. An initial uninstantiated
coefficient universe caused a stuck universe constraint; explicitly specifying both
universes of `Sheaf.functorH` repaired it without changing the mathematical statement.
Only the main named theorem has a postponed proof. There is no STATEMENT-DISPUTED flag
and no source-based statement correction.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
