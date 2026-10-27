## Worker report

Stage 2, Q111, 2026-10-23. The inherited BLOCKED ending concerned stage 1.
The live node has Q136's accepted stage-1 split but no Lean record; queue.tsv lists it
at stage 2. coord/brief-stage2.md §0 explicitly authorizes this stage handoff. The sandbox
initially held only dispatcher brief markers; no interrupted delivery existed to repeat.
No statement correction, dependency repair, or change to the accepted proof is made.

The main module is
`Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedStructureFinitePresentation`.
Its sole theorem is `AlgebraicGeometry.AlgebraicSpace.closedImmersion_structure_finitePresentation_iff`.
The proof is `sorry`, and the docstring gives all five accepted proof steps.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- The base scheme is `{S : Scheme.{u}}`; the two algebraic spaces over this same base are
  `{Z X : AlgebraicSpace S}`. The base and spaces need no additional conditions.
- The named immersion is `(i : Z ⟶ X)`. Its hypothesis `hi` is exactly
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`:
  every scheme test is represented by a scheme with closed-immersion projection.
- Small-etale module sheaves are the existing `X.Modules`, using `X.structureSheaf`.
  The structure sheaf as a module is `SheafOfModules.unit X.structureSheaf`.
  The direct image structure module is
  `(moduleDirectImage i).obj (SheafOfModules.unit Z.structureSheaf)`.
- The map of structure modules is `moduleStructureMap i`, defined in the new definition
  node below by its uniquely prescribed regular-function chart projections. The ideal
  module is the categorical `kernel (moduleStructureMap i)`; sheaf-module kernels are
  sectionwise kernels. Its finite-type property is `SheafOfModules.IsFiniteType`.
- Locally of finite presentation is `MapIsLocallyOfFinitePresentation i`, namely
  the existing test on every compatible pair of etale scheme charts with the scheme
  property `LocallyOfFinitePresentation`.
- Finite presentation is written out as local finite presentation, together with
  `MapIsQuasiCompact i.hom.hom` and
  `MapIsQuasiCompact (pullback.diagonal i.hom.hom)`.
- Finite presentation of the quotient module is the existing
  `SheafOfModules.IsFinitePresentation`, whose local finite generators AND relations
  are precisely the finite exact presentation in the node.
- The conclusion is `(A ↔ B) ∧ (A ↔ C) ∧ (C ↔ D)`, for the four conditions in the
  stated order; these three edges express equivalence of all four conditions.
- No Noetherian, quasi-compactness or separation hypothesis on X appears. The module
  universe is u, the site's objects are in u+1 and its arrows in u. There is no independent
  smaller test-scheme universe, coefficient lift or additional universe equality.

Dependency declarations used (full names are in AlgebraicGeometry.AlgebraicSpace unless
qualified otherwise):

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `EtaleSite`, `structureSheaf`, `Modules`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `AlgebraicGeometry.IsClosedImmersion`.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`;
  the transparent abbreviation used by `Modules` gives Mathlib's `SheafOfModules`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: the two existing
  slice sheafification instances needed by the general finite-type and finite-presentation
  predicates. Quasi-coherence is not added as a hypothesis: the closed-immersion lemma
  in the proof establishes it.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: `moduleDirectImage`,
  `moduleDirectImageModel`, `ModuleChart`, `moduleChartScalar`. The direct-image model
  and its entire chart-projection signature and docstrings were read.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  `AlgebraicGeometry.LocallyOfFinitePresentation` and its field `finitePresentation_appLE`.
- Added the already-landed statement dependency `def-sfb-space-morphism-properties`:
  Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties, `MapIsLocallyOfFinitePresentation`.
  Its public import supplies ProperCurveModuli's `MapIsQuasiCompact` as well.
- The metatheoretic size-convention node has no declaration: explicit `universe u`
  and the recorded site/module choices implement it.
- Proof-only imports Mathlib.Algebra.Module.FinitePresentation and
  Mathlib.RingTheory.FinitePresentation supply the recorded Mathlib proof leaves.
  The other five non-Mathlib proof prerequisites currently have no Lean records and
  therefore cannot yet be imported; no downstream proof prerequisite is used to define
  the canonical structure map.

Edge cases checked before writing: Z empty (kernel O_X, quotient zero); Z=X
(kernel zero, quotient O_X); empty X and the zero affine ring; no finitely generated
ideal assumption (e.g. the ideal of all variables in infinitely many polynomial variables,
where the four conditions fail); non-quasi-compact and nonseparated X, and finite charts
with zero generators or zero relations. None is excluded by a binder. In particular the
quotient is R/J, not the conormal J/J².

Searches actually run through msearch.py Q111 on this item:

- leanfinder: "A closed immersion of algebraic spaces is of finite presentation if and
  only if its ideal sheaf is of finite type and its direct image structure sheaf is
  finitely presented": eight scheme-morphism hits, no exact algebraic-space theorem.
- loogle: "AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.LocallyOfFinitePresentation":
  zero hits.
- grep: "IsClosedImmersion.*FinitePresentation|finitePresentation.*ideal|finitePresentation.*quotient":
  17 hits on finite ring/module presentations and smoothness, no exact theorem.
- leansearch: "A closed immersion of algebraic spaces is finitely presented if and only
  if its ideal sheaf is of finite type": eight scheme finite-type and closed-immersion
  results, no exact theorem.
- rg of the item's id and the relevant names in lean/WeilConjectures and lean/Sheaf:
  no existing theorem or canonical structure-module map. Existing morphism properties
  and chart-limit module operations were found and reused.

Both delivered modules compiled cleanly using scompile.py, separately in dependency order,
against the live server. No warnings or errors were printed. No local/global Lake build
was run, and no direct write to the shared repository was made.

## New nodes

`def-sfb-space-module-structure-map` supplies the canonical map O_Y → f_*O_X for any
algebraic-space morphism f. It is needed to name the kernel in the item. No existing
DAG node or module exposes this map: the operation node supplies the direct-image functor
and its chart projections but no structure-module map. The new module states existence
AND uniqueness with every chart projection equal to the actual pullback of regular
functions `moduleChartScalar f V c s`, then selects the unique morphism. This is the
unique-object universal-property construction expressly permitted by AGENTS.md §5,
not selection from mere nonempty unspecified data. The existence/uniqueness theorem
is part of this definition node's stated construction and has a complete proof docstring.
The definition contains no sorry. Source: Stacks 03G8 and 03MB.

Before adding it, searched dag/nodes for the proposed map names and related notions,
and ran tools/blueprint_refs.py search "structure sheaf" (19 blueprint nodes, none matching)
and ancestor on the item (the inherited ancestor is null). Its inherited ancestor/via
chain is retained with the item prepended. The new node records the actual search queries
and results: LeanSearch and LeanFinder returned scheme/locally-ringed-space maps;
Mathlib grep found zero hits. Direct rg in Mathlib, WeilConjectures and Sheaf found no
canonical algebraic-space structure-module map. The new node is cited by the item.

## Second reading by Q111

A separate second pass of the saved node and the two saved modules checked the eight
original dependency records, the extra landed morphism-property node, and the new node
against Stacks 084Q (spaces-morphisms.tex 5666–5683), 03MB (2216–2263), 0610
(spaces-descent.tex 538–556), and 082T (sites-modules.tex 3310–3319).
The dispatcher forbids starting other agents; this section records a second pass by
this worker, and does not claim an independent worker's review. The maintainer's
independent review remains required.

The binders use arbitrary spaces over one base and assume only representable closed
immersion. All four conditions and both global finiteness requirements are present.
The finite-type and presentation predicates use the existing small-etale module category;
there is no accidental Zariski-only substitution. The canonical map is uniquely normalized
by pullback of regular functions, so taking its kernel does not quantify over arbitrary
maps. The helper's uniqueness quantifies over every chart and every regular function,
which determines every section map by limit uniqueness. The three iff clauses connect
all four vertices. The statement preserves all edge cases listed above. No mismatch
requiring a statement correction was found; no proof was supplied. Declaration signatures
are copied verbatim into the respective node records. The accepted stage-1 statement,
proof and review fields are preserved, including Q136's corrected step 4.

The first dry run identified one schema requirement: new nodes must carry
`import_flags`. Added the empty list required by the live preflight and reran it.
