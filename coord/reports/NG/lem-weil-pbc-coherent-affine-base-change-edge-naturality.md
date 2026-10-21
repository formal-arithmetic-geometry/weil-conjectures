## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge` states
`AlgebraicGeometry.coherent_affine_base_change_edge_naturality`. All mathematical
assertions are in that one theorem with proof `sorry`. Its twelve helper declarations
are transparent abbreviations or actual compositions of existing canonical maps.
No data is supplied by a postponed existence assertion introduced in this delivery.

Clause-by-clause rendering:

- Schemes and their morphism: `{X S : Scheme.{u}} (f : X ⟶ S)`; quasi-compact and
  separated are `[QuasiCompact f] [IsSeparated f]`.
- The coefficient is `(G : X.Modules) [G.IsQuasicoherent]`; no finite-type,
  finite-presentation, properness or flatness hypothesis is imposed on it.
- `K = Rf_*(G[0])` is the abbreviation `coherentEdgeK f G`, using
  `schemeDerivedDirectImage` and `DerivedCategory.singleFunctor ... 0`.
- `A = H^0(K)` and `E = H^1(K)` are `coherentEdgeCohomology f G 0` and
  `coherentEdgeCohomology f G 1`, using `DerivedCategory.homologyFunctor`.
  Each has its own `SheafOfModules.IsFiniteLocallyFree` hypothesis; rank may vary.
- `hsplit` says every point `s` lies in an open `U` on which the exact restriction
  of K is isomorphic to the biproduct of the single complex of restricted A in
  degree zero and restricted E in degree one. Single degree one represents E[-1].
  The local isomorphism is existential (`Nonempty`); no splitting is chosen globally.
- `hbc` quantifies every `T : Scheme.{u}` and every `g : T ⟶ S`, and asserts
  `IsIso (coherentEdgeDelta f G g)`. This abbreviation is the existing
  `singleDegreeBaseChangeComposite` at degree zero on the chosen fibre square;
  it uses exactly the composition-pinned counit of the existing base-change mate.
- `X_T`, `f_T`, `j_T` are `pullback f g`, `pullback.snd f g`, `pullback.fst f g`.
  `G_T` is `coherentEdgeCoefficient f G g`, the recorded `tensorPullback` along j_T.
- The conclusion supplies `τ : K ⟶ singleFunctor ... 1 E` and requires its H1 map,
  followed by `singleFunctorCompHomologyFunctorIso`, to be the identity of E.
  Since the splitting hypothesis puts K in D≤1, this normalization uniquely
  specifies the canonical truncation projection. In particular τ is neither
  an arbitrary chosen projection of a local splitting nor an extra hypothesis:
  its existence and normalization are conclusions of the theorem.
- `coherentEdgeGamma g K τ` applies H1 to Lg*(τ) followed by the existing
  `pinnedSingleDegreeTensorComparison` at degree one and the canonical single
  homology isomorphism. This writes out the identification H1(Lg*(E[-1])) = g*E.
  Its `IsIso` conclusion is for every scheme base g, including nonflat g.
- A simultaneous family `β T g` of module isomorphisms has source g*E and target
  H1(Rf_T*(G_T[0])). The equation `gamma ≫ beta.hom = H1(delta)` forces exactly
  beta = H1(delta) gamma inverse; it does not quantify unrelated isomorphisms.
- `coherentEdgeEpsilon` uses the chosen cocycle-characterized Leray edge from
  `exists_lerayEdge_isIso_of_vanishing`, followed by sections of the inverse of
  `homologyRightDerivedFunctorObjSingleFunctorIso`. Thus its target is the same
  H1(Rf_T*(G_T[0])) used by beta, rather than a freely chosen identification
  between total and classical higher direct images. The cocycle formula in the
  existing theorem determines its chosen edge uniquely, independently of resolutions.
- For each affine `T`, the conclusion asserts `IsIso` of this canonical epsilon.
  The family `e T g hT` consists of linear equivalences over `Γ(T, ⊤)`.
  `coherentEdgeH` restricts the scalars on H1(X_T,G_T) along f_T.appTop, which
  supplies precisely its Γ(T,O_T)-module structure. The target is global
  sections of g*E. The equation for every x fixes e to Γ(beta inverse) epsilon.
- One existential family e precedes the quantification of every T,T',g,h, so
  the maps work simultaneously. The last equation quantifies every
  `h : T' ⟶ T`, with structure map of T' equal to `h ≫ g`, and every class x.
  It is exactly e_(gh)(h_X*(x)) = rho_h(e_g(x)). No étale, open or flat
  restriction is placed on h.
- `coherentEdgeXMap` is a transparent specialization of the existing
  `baseChangeMap f` to the Over-morphism with underlying arrow h.
  `coherentEdgeCoefficientIso` is the inverse normalized pullback composition
  followed by the equality of the first fibre-product projection.
  `coherentEdgePullback` uses the recorded `moduleCohomologyFMap` of the
  normalized pullback-adjoint transpose of exactly that coefficient isomorphism.
- `coherentEdgeRho` is section pullback through the normalized ordinary unit,
  including restriction along h inverse top = top, followed by the inverse
  normalized tensor-pullback composition at E. This is the rho in the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: its public Mathlib
  `SheafOfModules.IsQuasicoherent`; the finite-type conjunction is not required.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` is transparently
  `SheafOfModules`; the scheme specialization is `X.Modules`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage`, `schemeModuleHigherDirectImage` (the latter's
  defining composite is abbreviated by coherentEdgeCohomology).
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`.
- `WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap`:
  `IsDerivedModuleBaseChangeMap` and `IsDerivedModulePullbackComparison`
  were read. Their landed record is preserved. The specific composition-pinned
  representative used by delta is supplied by the new definition nodes below.
- `WeilConjectures.AlgebraicGeometry.PinnedSingleBaseChangeShift`:
  `singleDegreeBaseChangeComposite` and its source and target functors.
- `WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeSquare`:
  `pinnedSingleDegreeTensorComparison`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the chosen pullback
  and projections; `baseChangeMap` from the imported Picard interface is reused.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullbackSectionAdjunction`, `tensorPullbackSectionComp`, with the
  existing `Scheme.Modules.tensorPullback` functor retained.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`:
  `exists_tensorPullbackAdjunction`; this is the unit normalization from which
  the section-normalized adjunction is constructed.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`:
  `nonempty_tensorPullbackId`, `nonempty_tensorPullbackComp` are the recorded
  identity/composition interface; the normalized comparisons from the recorded
  pullback-definition module supply the particular maps needed here.
- `WeilConjectures.AlgebraicGeometry.DerivedPullback`: `derivedPullback`.
- `WeilConjectures.AlgebraicGeometry.LerayDegenerateSections`:
  `exists_lerayEdge_isIso_of_vanishing`, including its full cocycle condition.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `sheafCohomologyAndHigherDirectImages`; its canonical comparison construction
  is already named `Functor.homologyRightDerivedFunctorObjSingleFunctorIso` in
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`:
  `Scheme.Modules.moduleCohomologyFMap` and its resolution-based definition.
- `WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps`:
  `schemeOpenRestriction` with its exactness/additivity instances. Its landed
  node is added to stmt_deps. The two new definition nodes below now own the
  existing pinned single-degree comparison and base-change composite.
- `DerivedPullbackComposition.exists_derivedPullbackComposition` supplies
  additivity witnesses inside definitions. These are proof data and introduce
  no additive or size hypothesis in the statement.

All already-stated proof-dependency modules are imported. The two proof nodes
`lem-weil-pbc-derived-pullback-top-cohomology` and
`lem-weil-pbc-top-base-change-presheaf` have no Lean records in the read clone;
no import was invented for them. They are only proof prerequisites, not needed
to type the present statement. Their use is explained in the theorem docstring.

Edge cases checked before drafting: empty X, empty S and empty affine T; zero G;
rank-zero A or E; varying ranks on disconnected opens; identity g and identity h;
composition of arbitrary nonflat affine base arrows; and a nonaffine original S.
The local hypothesis quantifies points, so on empty S it is vacuous as it should be.
Zero cohomology gives the zero equivalences and the same canonical equations.
No nonempty cover/index assumption is imposed. Scheme, coefficient and sheaf
universes are the existing scheme-module convention u; w is an arbitrary common
localization universe. No equality of site object/morphism universes is imposed.

Searches (2026-10-21):

- msearch leanfinder, "Canonical affine Leray H1 edge isomorphisms for a locally
  split two degree derived direct image commute with arbitrary base change":
  eight hits, including pullback of free modules and open-cover pullback
  isomorphisms. None states the affine cohomology/derived-image assertion.
- msearch loogle, `"cohomology", "baseChange"`: zero hits.
- msearch grep, `Leray|leray|edge.*baseChange|baseChange.*edge`, subdirectory
  AlgebraicGeometry: zero Mathlib hits.
- msearch leansearch, "Canonical Leray edge isomorphism H1 of a module on a scheme
  to sections of higher direct image is natural for base change": eight hits
  on Kaehler differentials, free pullback, open restriction and exterior-power
  naturality; no match.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `affine.*[Ee]dge|[Ee]dge.*[Nn]atural`: affine pushforward edge and flat-base-change
  files, with different hypotheses/conclusions; no matching theorem.
- Searches for `singleDegreeBaseChangeComposite` and
  `pinnedSingleDegreeTensorComparison` found the existing pinned constructions;
  their complete definitions/docstrings were read and reused. A draft duplicate
  helper module was removed before delivery.
- Searches for `baseChangeMap`, `schemeOpenRestriction` and the canonical
  single-homology comparison found the existing declarations used here.

Source text was read directly in `literature/stacks-project/cohomology.tex`,
including `lemma-Leray`, `remark-explain-arrow` and
`remark-compose-base-change-horizontal`, with the module-structure remark
following Leray. No statement correction or disputed mathematical claim is made.

## New nodes

- `def-weil-pbc-pinned-single-degree-tensor-comparison` records the unchanged
  `AlgebraicGeometry.pinnedSingleDegreeTensorComparison` in
  `WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeSquare` with
  `existing: true`. Its source is Lk* of the module single complex in degree n;
  its target is the single complex of k*M in that same degree. Its data is the
  composition-pinned counit at the homotopy single complex followed by the
  localized termwise single-complex comparison. It asserts no open-square
  theorem and quantifies no arbitrary comparison. All integer degrees, zero
  modules and empty schemes are included; no flatness condition is used.
- `def-weil-pbc-single-degree-module-base-change-composite` records the unchanged
  `AlgebraicGeometry.singleDegreeBaseChangeComposite` in
  `WeilConjectures.AlgebraicGeometry.PinnedSingleBaseChangeShift` with
  `existing: true`, also listing its source and target functors. For every
  commuting scheme square, coefficient G and integer n, it composes the
  recorded derived mate with Rf' of the pinned single-module counit from the
  preceding definition node. It uses the same selected counit as the mate.
  No cartesianness or flatness is imposed. The chosen fibre square and n=0
  specialize this definition to coherentEdgeDelta; n=1 in the preceding
  definition gives the comparison used by coherentEdgeGamma.

These are definition ownership records for existing real constructions; neither
upstream module nor any theorem-node record is modified. Their signatures were
copied verbatim from the source declarations. Both records use the item's chapter
and unit and the blueprint ancestor `thm-weil-pbc-direct-image-finiteness-proper`.
The statement-dependency lists cite the existing categorical, module, derived
functor and composition interfaces from which the constructions are formed.

Searches for both new ownership records (2026-10-21):

- msearch LeanSearch and LeanFinder, query `composition pinned tensor counit on
  single complexes and derived module base change composite`: eight hits each;
  LeanSearch returns algebraic IsBaseChange compositions, coalgebra counits and
  scalar-change comparisons; LeanFinder returns representation resolutions and
  monoidal-complex comparisons. None is either sheaf-derived construction.
- msearch grep `pinnedSingleDegreeTensorComparison|singleDegreeBaseChangeComposite`:
  zero Mathlib hits.
- rg with the same names in WeilConjectures and Sheaf finds their original
  definitions at OpenPinnedSingleDegreeSquare:32 and PinnedSingleBaseChangeShift:53,
  with source and target functors at lines 28 and 41; no Sheaf duplicate.
- rg in dag/nodes finds their theorem-node attachments and consumers, with no
  definition node for either construction. This is precisely the ownership
  defect identified by the maintainer. The existing theorem attachments remain
  intact; the consumer now cites the new definition owners.
- `blueprint_refs.py search 'pinned single'` and `search 'single complex'`:
  zero blueprint matches each. `ancestor` identifies the ancestor recorded above.

The exact search queries, service outputs and dates are recorded in both new
nodes and the sandbox search log. The Stacks source read for these definitions is
Cohomology Tag 08HY (`remark-base-change`) and Tag 0ATM
(`remark-compose-base-change-horizontal`), together with the source definitions'
full docstrings and the composition-counit interface they select.

## Repair of the maintainer return on c19c2cada59d

1. H2: the saved item cited theorem node
   `lem-pc-open-pinned-single-degree-square` to obtain a plain definition.
   That added citation has been replaced by the two new definition nodes above.
   They own the plain definitions needed by gamma and delta with `existing: true`
   over the unchanged upstream modules. No theorem statement or proof is used
   as a substitute for its internal definition, and no definition is duplicated.
2. H13: the rejected sandbox override of
   `def-pc-derived-module-base-change-map` has been removed from the packet.
   Thus the live node and its record of `IsDerivedModuleBaseChangeMap` and
   `IsDerivedModulePullbackComparison` are preserved byte for byte. The original
   statement-dependency citation is retained. The pinned delta is obtained from
   the second new definition node, with no reassignment of the existing node.
   The 21 landed consumers need no interface changes or recompilation.

The item statement, proof plan, Lean file, theorem signature, canonical maps and
all mathematical quantifiers are unchanged from the reviewed delivery. Only the
ownership records, the added statement dependencies and this report are repaired.
No statement correction or disputed mathematical claim is introduced.

## Second reading by NG

This dispatcher brief assigns a single worker, explicitly prohibits starting
other agents, and assigns independent delivery review to the maintainer.
Accordingly this section records a self-audit, not a claimed independent reading.
The audit checked every clause listed above with the node and module open. It
removed duplicate draft constructions after finding the existing pinned single
comparison and base-change composite, and replaced a new fibre-product lift by
the existing baseChangeMap. It checked the direction of all three composition
inverses (beta inverse on sections, ordinary h/g composition inverse, coefficient
pullback composition inverse), the degree-one sign convention, and the scalar
restriction along f_T. Maintainer independent review remains required.

## Validation

The required initial dry run of the saved packet passed mechanically as commit
956436f165c. The independent maintainer return still required the two ownership
repairs above; passing a mechanical check does not resolve those findings.

The repair self-check reread the unchanged Lean file and the complete source
signatures and docstrings of both pinned definitions, the original module-base-change
predicates, the selected composition-counit theorem and the derived-base-change
construction. The new node statements match those definitions, including every
scheme, module, degree, commutativity and additivity parameter. Their dependency
lists agree exactly with their bracketed node citations. The new nodes depend
only on prerequisites, with no path back to this item. No theorem or definition
has been added to the Lean source. The one existing theorem still has its sole
whole-proof `sorry`; every helper still has real data. All previously reviewed
edge cases and clause-by-clause checks above continue to apply.

The repaired theorem file passed the prescribed scompile.py call with exit code
zero, with no errors or warnings (sandbox 36.3 s, library 47.7 s). Static checks
confirmed exact signatures for the theorem and both existing definitions, the
required JSON layout, and exact agreement between both new nodes' citations and
statement dependencies. The first repaired dry run compiled successfully and reported only the new-node
citation formatting: the two grouped dependencies had to be separate bracketed
citations. They were separated without changing either definition, its dependency
list, or any Lean source. The final repaired dry run passed compilation and server preflight with exit code
zero: `OK (dry run): commit 668a92503da passes the preflight and compiles; nothing
pushed`. The packet contains exactly the item, its unchanged Lean module, the two
new definition ownership nodes and this report; no dependency override is staged.
The prescribed deliver2.py command submits this repaired packet.
