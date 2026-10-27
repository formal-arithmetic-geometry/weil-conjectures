## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceProperArbitrarySchemeTests` states
`AlgebraicGeometry.AlgebraicSpace.proper_iff_scheme_tests`. Its sole theorem has
proof `sorry`; it introduces no definitions or additional proof obligations.
The source was read locally in `literature/stacks-project/spaces-morphisms.tex`,
`definition-proper` and `lemma-proper-local` (Tag 083R, conditions (1) and (2)).
It states exactly this equivalence for arbitrary algebraic-space morphisms.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| A base scheme S, in the fixed size convention | Explicit `universe u` and `{S : Scheme.{u}}`; all schemes and algebraic spaces use this same universe, as in the recorded framework. |
| Algebraic spaces X and Y over S | `{X Y : AlgebraicSpace S}`, the existing full subcategory of fppf sheaves with representable diagonal and surjective etale scheme atlas. |
| A morphism q over S | `(q : X ⟶ Y)`, a sheaf natural transformation in that full subcategory. |
| Intrinsic separated, finite type, universally closed | `MapIsProper q`, the recorded definition `MapIsSeparated q ∧ MapIsFiniteType q ∧ MapIsUniversallyClosed q`. Finite type includes quasi-compactness and chartwise local finite type; universal closedness tests all algebraic spaces. |
| If and only if | `↔`. |
| Every S-scheme T | `∀ (T : Over S)`. Its left object is any `Scheme.{u}`, and its structure morphism to S is retained. This is the same universe as S and the site, not a potentially smaller independent universe. |
| Every morphism T to Y | `(g : schemeSpace T ⟶ Y)`; `schemeSpace` is the already defined representable fppf sheaf of T, bundled as an algebraic space. These arrows are exactly arbitrary Yoneda maps to Y. |
| Sheaf fibre product X ×_Y T | `enlargedFibreProduct q g`, whose data is `Limits.pullback q.hom g.hom`; its algebraic-space property is `(fibreProduct_isAlgebraicSpace X (schemeSpace T) Y q g).1`. |
| Projection X ×_Y T to T is proper | `MapIsProper (ObjectProperty.homMk (Limits.pullback.snd q.hom g.hom) : enlargedFibreProduct q g ⟶ schemeSpace T)`. This uses the literal second sheaf projection in precisely the node's factor order. |
| Pullback source need not be a scheme | The projection's source has type `AlgebraicSpace S`, with no witness of scheme representability. |
| No prior representability, Noetherian, finite presentation, flatness or quasi-compactness assumption | The theorem has only S, X, Y and q as parameters; no property binders or typeclass hypotheses occur. |

Statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`, read with their
  locally affine locally ringed-space signature and morphism signature.
- `def-weil-size-convention`: the record explicitly says this is a metatheoretic
  convention with no declaration or import. It is rendered by explicit universes.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace`, with `IsAlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale` and `IsSurjective` read in the same module. Exported through the public imports.
- `def-sfb-space-morphism-properties`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`,
  `AlgebraicGeometry.AlgebraicSpace.MapIsProper` and its three constituent predicates.
- `lem-trf-space-fibre-products-etale-covers`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`, used by the
  existing bundled pullback construction and exported through the public imports.
- `def-trf-scheme-algebraic-space`: its existing declaration
  `AlgebraicGeometry.AlgebraicSpace.schemeSpace` in
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` supplies the actual Yoneda
  representable sheaf of each scheme T, with its algebraic-space property.
- `def-sfb-space-sheaf-fibre-product`: its existing declaration
  `AlgebraicGeometry.AlgebraicSpace.enlargedFibreProduct` in the same module supplies
  the actual sheaf pullback bundled as an algebraic space. The statement uses
  `Limits.pullback.snd` for its second projection.
  These two definition owners are added to `stmt_deps`; the enlarged-etale-ringed-site
  theorem is not a statement dependency. The defining module remains publicly
  imported. No node statement or dependency interface is changed, and no helper
  is duplicated.

Plain proof imports retain the stated proof plan:
`AlgebraicSpaceEtaleOpenImage` (`points_compactSpace_iff`, `etale_open_image`),
`AlgebraicSpacePointOpenCalculus` (`point_open_calculus`),
`SpaceLocalPropertiesChartTest` (`local_properties_chart_test`), and
`Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`
(`quasiCompact_separated_etaleLocal`). Their signatures and proof docstrings were read.
The other proof dependencies are supplied by public imports.
`lem-sfb-space-proper-base-change` has no recorded Lean module in the read snapshot,
so no speculative proof import is added; its role is included in the proof docstring.

Edge cases checked against the signature and definitions: the empty base, source,
target and test scheme are allowed; no nonemptiness or field-characteristic binders
occur. Disconnected and non-quasi-compact test schemes are quantified without
restriction. Tests need not be etale, affine, flat or finitely presented.
The case T = Y when Y is a scheme includes its identity test. Algebraic-space
sources not represented by schemes remain allowed, including after base change.
No independent small test-universe can make the test condition vacuous.

Searches (all 2026-10-24, using the prescribed msearch.py wrapper):

- LeanFinder query: “A morphism of algebraic spaces is proper if and only if every
  base change to a scheme is proper, without representability by schemes”. Eight
  hits, all scheme properness facts such as `IsProper.isStableUnderBaseChange` and
  `isProper_iff`; no algebraic-space equivalence.
- LeanSearch query: “A morphism of algebraic spaces is proper if and only if all its
  base changes to schemes are proper”. Eight scheme-only hits; no exact match.
- Loogle query: `AlgebraicGeometry.AlgebraicSpace.MapIsProper, AlgebraicGeometry.IsProper`.
  Zero hits; the project's MapIsProper is unknown to this Mathlib search index.
- Mathlib grep query: `AlgebraicSpace|proper.*scheme.*test` in `AlgebraicGeometry`.
  Zero hits. Local rg additionally searched `MapIsProper|proper_iff_scheme_tests|proper.*scheme.*test`
  in Mathlib's AlgebraicGeometry, `lean/WeilConjectures`, `lean/Sheaf/AlgebraicGeometry`
  and the upstream-name record. No exact theorem or name conflict was found.
- Searched the item id in `lean/WeilConjectures`: no occurrence. The broader project
  search found the existing intrinsic predicate, strict-local tests, and the
  existing scheme and pullback bundles, all reused rather than redefined.

No fault in the item's mathematical statement was found; no statement correction
or new definition node is needed. One proof-interface issue is reported for later
proof work: `IsJointlySurjectiveEtaleFamily` in the recorded QC/separated-local
module asks for lifting sections over T itself, rather than after an etale cover.
A general etale surjective atlas need not satisfy that stronger predicate (a
nontrivial separable field extension already shows this). The item remains exactly
the Stacks statement and has no such hypothesis. The proof-only interface will
need repair when implementing the atlas-descent proof; it is not copied or assumed
as an extra hypothesis in this delivery.

Validation: scompile.py compiled the delivered file both under its sandbox module
name and its final library module name, with no errors or unexpected warnings
(1.4 s and 1.5 s respectively). The theorem proof remains `sorry` as required.

## Second reading by Q34

Author self-check, with the node, source, dependency definitions and final file open;
the maintainer supplies the independent delivery review under the dispatcher brief.
The node's scheme T is precisely an arbitrary object of `Over S`, rather than an
etale chart or an affine scheme. `g` is an unrestricted morphism of algebraic spaces
from its representable sheaf. The explicit type ascription on `ObjectProperty.homMk`
ensures that the projection is from the bundled X ×_Y T to the bundled T, with the
same S throughout. Expanding `enlargedFibreProduct` confirms that the source data
is the sheaf pullback, and expanding `MapIsProper` confirms that both sides use the
same intrinsic predicate, including algebraic-space universal-closedness tests.
There are no added assumptions. Empty objects and arbitrary scheme tests remain
in scope. The proof docstring follows the node's five steps, and the proof-only
interface issue above is recorded explicitly. No mismatch in the theorem signature
was found and no statement change was made.

## Repair of returned delivery 7a6de6e31c0c

H2 repaired: replaced the added theorem dependency
`lem-trf-space-enlarged-etale-ringed-site-model` with the two existing definition
owners `def-trf-scheme-algebraic-space` and
`def-sfb-space-sheaf-fibre-product`. Read both current node records and the existing
`schemeSpace` and `enlargedFibreProduct` definitions in their recorded module.
Updated the dependency paragraph above to identify these owners. The Lean file,
declaration and `lean.statement` are unchanged from the returned delivery, as
requested. Compared the retained node with current main: all fields other than
the authorized `lean` and added `stmt_deps` are identical. The delivery wrapper
rebases this repaired payload on the current main branch.
