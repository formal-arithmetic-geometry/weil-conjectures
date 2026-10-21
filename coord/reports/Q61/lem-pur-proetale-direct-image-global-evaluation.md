## Worker report

Q61 states `lem-pur-proetale-direct-image-global-evaluation` in
`Sheaf.AlgebraicGeometry.ProEtaleDirectImageGlobalEvaluation`. The six property
theorems have `sorry` proofs; each has its source and a complete proof plan in its
docstring. The comparison itself is a real natural isomorphism constructed by the
published universal right-derived compositor. No data is postponed.

### Hypotheses and clauses

- Finite coefficient conventions: `P : WeilConjectures.PurityFiniteSetting.{u}`;
  `P.Ring` is literally the published quotient at `P.level`, with `P.level_pos`.
  `purityGlobalEvaluation_finiteRing` uses the proved finiteness theorem for that
  quotient. This adds no hypothesis on the coefficient datum.
- Schemes over the fixed field: `T Y W : Scheme.{u}`, their `Over` instances over
  `Spec (.of P.field.k)`, and `f.IsOver` / `g.IsOver`. An open source `U` has the
  same `Over` instance; `j.IsOver` and `IsOpenImmersion j` are explicit.
- Ordinary module categories: every source category is
  `proEtaleRingModules T (proEtaleConstantRing T P.Ring)`. The small site is the
  original `T.ProEt`, with object universe u+1 and Hom universe u. The published
  intrinsic module equivalence identifies its sections with the fixed-scalar
  presentation, including the coefficient action. There is no completed,
  constructible, torsion-bounded, or arbitrary substitute category.
- Bounded-below derived domain: `proEtaleGlobalEvaluationPlus` is the actual
  natural isomorphism whiskered with `DerivedCategory.Plus.ι`; the shift,
  composition, identity, and triangle clauses quantify over `DerivedCategory.Plus`.
  The underlying construction is available unbounded, allowing its value at
  `Rf_*L` to be written without an extra closure assumption.
- Finite derived direct image: `proEtaleConstantDerivedDirectImage f P.Ring` is
  the published right derived functor of `proEtaleConstantModuleDirectImage`.
  This is exactly the finite ordinary functor used by `sfFiniteDerivedDirectImage`;
  no integral tower or derived completion occurs.
- Derived final-object evaluation: `proEtaleGlobalEvaluationSections` is the
  right derived `proEtaleUnitLeraySections`, whose actual definition is intrinsic
  scalar realization followed by `Sheaf.Γ`. Its source localization is the
  published standard localization; its module target is the published small
  Grothendieck localization. The explicit universes merely choose these existing
  constructions and impose no equality of the site and coefficient universes.
- Canonical natural isomorphism: `proEtaleGlobalEvaluation` uses
  `rightDerivedFunctorCompIso'` with `proEtaleGlobalEvaluationTerminal`.
  The latter is the published terminal-object comparison transported through
  `proEtaleUnitLerayDirectImageIso` to the actual sectionwise finite direct image.
  Its `Iso` type includes invertibility and naturality for every derived morphism,
  including roofs; the D+ restriction is `proEtaleGlobalEvaluationPlus`.
- K-injective normalization: `proEtaleDirectImageGlobalEvaluation` quantifies
  over `J`, `[J.IsKInjective]`, and `∃ a : ℤ, J.IsStrictlyGE a`. Its equation is
  the final-object chain isomorphism bracketed by the three canonical
  `rightDerivedFunctorObjQIso` identifications. The terminal comparison
  identifies the actual coefficient actions and differentials, rather than
  inserting an arbitrary automorphism of global sections.
- Shift compatibility: `proEtaleDirectImageGlobalEvaluation_shift` gives the
  commuting square for every `n : ℤ` using the existing `commShiftIso n` on both
  functors. It uses the same comparison, with no newly chosen shift structure.
- Composition: `proEtaleDirectImageGlobalEvaluation_comp` is exactly the node's
  formula, in Lean's left-to-right composition order: global sections of
  `proEtaleOrdinaryDirectImageComposition`, then ell_g, then ell_f.
- Identity: `proEtaleDirectImageGlobalEvaluation_id` compares ell_id with global
  sections of the canonical identity direct-image isomorphism. This is the mate
  of the published section-normalized identity inverse image. Thus "identity"
  is stated after the canonical identity identifications, as required.
- Open restriction: `proEtaleDirectImageGlobalEvaluation_open` uses the actual
  unit of `proEtaleOrdinaryDerivedAdjunction`. Its right side is termwise
  `proEtaleUnitLeraySectionUnit` followed by the map of an arbitrary resolution
  `v : j^*I ⟶ H` with `[QuasiIso v]`, and the canonical localization
  identifications. The published open-unit evaluation identifies precisely this
  termwise map with restriction. Using arbitrary bounded-below K-injective
  representatives and resolution maps expresses the canonical derived
  restriction, without assuming j^* preserves K-injectives. The displayed
  `mapDerivedCategoryFactors` is the canonical identification of j^*QI with
  Q(j^*I), not a supplementary assumption.
- Support-localization triangles: `proEtaleDirectImageGlobalEvaluation_third`
  quantifies over the actual morphism `d : D.obj ⟶ B.obj⟦1⟧` and states the last
  square using the existing shift comparisons and ell_B[1]. The first two squares
  are already naturality of the natural isomorphism. Applying these to the three
  vertices of the given support-localization triangle therefore preserves its
  given third arrow and sign. No replacement connecting morphism is chosen.

### Dependency declarations used

Names in the first rows are in namespace `AlgebraicGeometry.Scheme` unless qualified.

| Module | Declarations / role |
| --- | --- |
| `Sheaf.Paper.PurityFiniteSetting` | `WeilConjectures.PurityFiniteSetting`, `.Ring`, `.field`, `.level_pos` |
| `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` | `Padic.finite_coefficientExtensionRing` |
| `Mathlib.AlgebraicGeometry.Scheme` | `Scheme`, `Scheme.Over`, `Scheme.Hom.IsOver` |
| `Mathlib.AlgebraicGeometry.OpenImmersion` | `IsOpenImmersion` |
| `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` | ordinary finite coefficient presentation, reexported by operations |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` | `proEtaleConstantRing`, `proEtaleConstantModuleDirectImage` |
| `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` | `proEtaleConstantRingPullback`, `proEtaleConstantRingAdjunction`, `proEtaleConstantRingDerivedPullback` |
| `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage` | `proEtaleConstantDerivedDirectImage` |
| `Sheaf.AlgebraicGeometry.ProEtaleOperations` | `proEtaleRingModules`, `proEtaleRingModules_hasDerivedCategory`, `proEtaleRingModules_hasKInjectiveResolutions` |
| `Sheaf.Paper.SfDerivedDirectImage` | `sfFiniteDerivedDirectImage`, the owning finite functor, imported for its recorded interface |
| `Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula` | `proEtaleUnitLeraySections`, `proEtaleUnitLerayDirectImageIso`, `proEtaleUnitLerayTerminalIso`, `proEtaleUnitLeraySectionUnit` |
| `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison` | `proEtaleConstantRingPullbackComposition` |
| `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity` | `proEtaleDerivedPullback_identity`, including its section and localization normalizations |
| `Sheaf.Paper.FiniteDirectImageComposition` | `AlgebraicGeometry.ProEtale.finiteDirectImageComposition`, imported unchanged for the recorded interface |
| `Mathlib.Algebra.Homology.DerivedCategory.TStructure` | `DerivedCategory.Plus`, `DerivedCategory.Plus.ι` |
| `Mathlib.Algebra.Homology.HomotopyCategory.KInjective` | `CochainComplex.IsKInjective` |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` | `Functor.rightDerivedFunctorCompIso'`, adjunction K-injective preservation |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective` | `Functor.rightDerivedFunctorObjQIso` |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated` | canonical right-derived shift and triangulated structures |
| `Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation` | `proEtaleOpenUnitEvaluation` supplies the sectionwise interpretation used in the open clause |
| `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation` | `kInjectiveDerivedMapComputation`, representative-map formula used in the proof docstrings |
| `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral` | pre-derived adjunction characterization used for the actual open unit |
| `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition` | ringed-topos representative normalization cited in the composition proof |
| `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses` | resolutions without a false site-universe equality |
| `WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution` | bounded-below K-injective resolution input |

The new definition node `def-pur-proetale-global-section-maps` owns the published
ordinary section functor and maps; it replaces the unused unit--Leray theorem in
stmt_deps. The landed `pur713-def-pullback-comparison` and
`lem-pur-proetale-derived-pullback-identity` remain statement dependencies. The
original `lem-weil-derived-direct-image-composition` record is preserved unchanged.

### Edge cases

Read against the formulas before writing: zero complexes and zero morphisms;
complexes concentrated in degree zero; arbitrary lower bounds; zero and negative
shifts; identity f, identity g, and both identities; an empty scheme; an empty open,
the identity open, and non-quasi-compact open immersions. Evaluation of the empty
site's module sheaves and all zero complexes is still functorial. No nonemptiness,
finite type, properness, smoothness, constructibility, or quasi-compactness is added.
The level-zero quotient is excluded exactly by the conventions' existing
`P.level_pos`, not by a new hypothesis. A shift changes the lower bound, but the
formulas quantify over D+ and all integral shifts, so do not require a common bound.
The open clause makes no assertion that the inverse image of a K-injective is
K-injective; H and v are arbitrary genuine resolutions. All definitions have real
data; extracting the identity comparison from the published normalization theorem
uses its determined isomorphism, not a bare `Nonempty` or undetermined existence.

### Searches

- `msearch.py ... leanfinder`: natural-language search for canonical derived
  global sections after pro-etale direct image, composition and restriction;
  eight results concerned ordinary scheme section restriction, not this statement.
- `msearch.py ... loogle "rightDerivedFunctorCompIso"`: no matching result.
- `msearch.py ... grep "rightDerivedGlobalSections|[Ll]eray"`: no Mathlib hit.
- `msearch.py ... leansearch`: normalized derived global-section/direct-image
  comparison; results included `Sheaf.Γ`, right-derived natural transformation
  composition, and `SheafOfModules.pushforward_comp_id`, but not this full theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for global sections, Leray,
  rightDerivedGlobalSections, and the item's id: found the published section functor,
  the etale analogue, and `ProEtaleUnitLerayChainFormula`; none already states all
  clauses of this node. Those existing notions are reused, not redefined privately.
- Read all stmt_deps nodes and their recorded signatures/docstrings. In particular,
  the fixed-scalar compositor is not directly applicable to the intrinsic ordinary
  module categories. The item module supplies the canonical mate compositor as a
  helper, without changing the recorded fixed-scalar compositor.
- Read local Stacks `sites-cohomology.tex`, lemma-Leray-unbounded (0D6H),
  lemma-derived-pushforward-composition (0D6E), and the K-injective/open-unit proof
  sources cited in the node. The statement is well-posed and needs no correction.

No `STATEMENT-DISPUTED` issue or statement change was found.

## New nodes

`def-pur-proetale-global-section-maps` is an `existing: true` ownership node for
`proEtaleUnitLeraySections`, `proEtaleUnitLerayDirectImageIso`,
`proEtaleUnitLerayFixedTerminalIso`, `proEtaleUnitLerayTerminalIso`, and
`proEtaleUnitLeraySectionUnit` in the already published
`Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula`. Its finite commutative
ring and schemes are the declarations' `A : Type u`, `[CommRing A]`, `[Finite A]`,
and `X Y : Scheme.{u}`. Global sections are the inverse intrinsic realization
followed by `Sheaf.Γ`. The direct-image identification is the coefficient-map
adjunction round trip; terminal evaluation cancels the scalar realizations and
uses preservation of the terminal object; the section unit is the whiskered
ordinary unit followed by that terminal comparison. These are exactly the
five existing definitions, with no use of the chain-formula theorem. The source
is Stacks 08J6 / 0D6H's ordinary terminal evaluation and adjunction construction.

Fresh `msearch.py` LeanSearch query "global sections functor constant ring module
sheaves pro etale site terminal object section unit" returned eight general
results, including `Sheaf.Γ` and `Sheaf.ΓNatIsoSheafSections`; Loogle `Sheaf.Γ`
returned zero hits / unknown identifier. Mathlib grep
`proEtaleUnitLeraySections|proEtaleUnitLeraySectionUnit|ΓNatIsoSheafSections`
in `CategoryTheory/Sites` found four general terminal-section hits. Project and
DAG grep of the exact helper names found these definitions only in the published
chain-formula module, with incidental ownership in the theorem's declaration
list; no separate definition node carries them. `blueprint_refs.py search Leray`
found 13 blueprint nodes, none defining these ordinary maps.
These actual searches are recorded in the new node. No definitions are copied.
Its source-site universes remain object u+1 and morphism u, with common scalar
lift `ULift.{u+1,u} A`, including empty schemes and the zero ring.

## Return repaired

F1 (H2): replaced the added theorem statement dependency
`lem-trf-proetale-unit-leray-chain-formula` by the new definition node above.
The module still imports the existing definitions' owning source, but never
uses `proEtale_unit_leray_chain_formula` as a theorem. No theorem assertion is
substituted for a missing definition.

F2 (H13): deleted the packet's dependency-node override and the separate
`ProEtaleOrdinaryDirectImageComposition.lean`. Q44's landed
`lem-weil-derived-direct-image-composition` node and
`FiniteDirectImageComposition.lean` are untouched. All four helpers now belong
to the item module, have its blueprint id, and are listed in its
`lean.declarations`: `proEtaleOrdinaryModuleAdjunction`,
`proEtaleOrdinaryDirectImage_preservesKInjective`,
`proEtaleOrdinaryDerivedAdjunction`, and
`proEtaleOrdinaryDirectImageComposition`. Their signatures and real construction
bodies are unchanged: the direct-image iso transports the adjunction, exact
inverse image preserves K-injectives, the actual adjunction is derived, and the
compositor is the mate of the published inverse-image compositor. Thus the
seven or more live importers and all 49 DAG citers retain their original API.
There are no dependency modules or dependency record changes in this packet.

## Second reading by Q61

The dispatcher brief explicitly forbids starting another agent; this is Q61's
second pass with the node, source passages, the item module and the new definition node open. It is not claimed
as an independent agent review; the maintainer performs the independent review.

Compared every hypothesis and clause with the mapping above. The first draft used
the ring-normalized pushforward directly; it was changed to the actual finite
sectionwise direct image by the published canonical isomorphism. The ordinary composition
helpers now belong to this item; the existing finite composition record is retained. The open formula includes the arbitrary
resolution map v and the inverse-image localization factor, so neither assumes
j^* preserves K-injectives nor identifies objects by an unspecified iso. The
identity comparison is the mate of the fully normalized published identity pullback.
The final triangle formula takes the actual d and the existing shift comparisons,
so retains its sign. Explicit localization universes and local fixed-universe
instances avoid an imported generic max-universe instance without shrinking the
small pro-etale site. No mathematical hypothesis or conclusion was changed.

### Validation

The single delivered Lean file is compiled individually by
`scompile.py` against the published live build. The delivery dry run also runs the
server preflight and per-file compilation. All postponed proofs are the six named
theorems in the item's module.

The repair second reading specifically checks F1 and F2: the new definition
node states each reused construction, records its exact existing names, and
removes the unused theorem edge. The item owns all four moved helpers and imports
`FiniteDirectImageComposition` directly; the delivery contains no compositor
node override. The six item theorem signatures and all 12 mathematical clauses
accepted at immutable head `23b894b1070e` remain unchanged.
