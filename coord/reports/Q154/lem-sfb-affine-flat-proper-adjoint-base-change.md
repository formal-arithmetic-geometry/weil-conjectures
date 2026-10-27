## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAffineFlatProperAdjointBaseChange` states
`AlgebraicGeometry.AlgebraicSpace.affineFlatProperAdjointBaseChange` and defines its
full-subcategory tensor pullback and its actual right-adjoint comparison. There is one
postponed theorem, with the complete five-step proof of the DAG node in its docstring.
Both helpers have concrete data. No new node or dependency module is needed.

Source read: `literature/stacks-project/spaces-duality.tex`, lemma-more-base-change
(Tag 0E5I), case (1), and lemma-trace-map-and-base-change (Tag 0E5L). The existing
node already corrects the printed domain typo: F belongs to D_QCoh(O_Y), not O_X.
The node statement and proof are unchanged. Statement dependencies gain the already
landed nodes that own the canonical derived operations and their quasi-coherent lift.

Hypotheses and clauses, matched against the node:

- Schemes over a scheme S: `S : Scheme.{u}`, `Y Y' : Over S`. The affine hypotheses
  are `[IsAffine Y.left]` and `[IsAffine Y'.left]`.
- The arbitrary morphism of affine schemes is `g : Y' ⟶ Y`; `traceSchemeMap g` is its
  existing represented-space morphism. There is no flatness condition on g.
- `X X' : AlgebraicSpace S` are algebraic spaces, including nonrepresentable ones;
  `f`, `h`, `f'` are the stated three maps. `sq : IsPullback h f' f (traceSchemeMap g)`
  says that X' with these maps is precisely a realization of the required fibre product.
- Properness is `hproper : MapIsProper f`, whose definition is separated, finite type,
  universally closed. Flatness is `hflat : MapIsFlat f`, tested on étale charts.
- Finite presentation is `hfp : MapIsLocallyOfFinitePresentation f` together with
  properness: the latter already implies quasi-compactness and separatedness, hence
  quasi-separatedness. Thus this is exactly finite presentation in the proper case.
- Unbounded module derived categories use the fixed small ringed models equivalent
  to the original small étale sites. Four explicit `HasDerivedCategory.{w}` instances
  select localization morphism size, with no restriction to bounded derived categories.
- D_QCoh is the existing `DerivedQCoh`, the full subcategory of complexes with
  quasi-coherent cohomology, not the derived category of the abelian QCoh category.
- `D : QCohDirectImagePresentation f` and `D' : QCohDirectImagePresentation f'`
  identify the pushforward functors with the fixed K-injective `derivedDirectImage` by
  their specified natural isomorphisms `comparison`. They encode the named restrictions
  Rf_* and Rf'_* to D_QCoh, rather than adding any mathematical hypothesis about f.
- The chosen right adjoints are functors `a`, `a'` and the supplied adjunctions `adj`,
  `adj'`. Their own counits, not separately chosen trace maps, occur in every formula.
- Pullback uses `spaceDerivedPullback`, the existing K-flat total left derived tensor
  pullback. `spaceQCohPullback` is `ObjectProperty.lift` of that exact functor, using
  the already stated preservation theorem. It has the same ambient objects and maps.
- `F : (schemeSpace Y).DerivedQCoh` ranges over every unbounded quasi-coherent object.
- The canonical beta at aF is expressed as `∃ β : ... ≅ ...` and
  `β.hom = moduleDerivedExchange f f' (traceSchemeMap g) h sq.w (a.obj F).obj`.
  Thus the theorem asserts invertibility of the actual canonical derived base-change
  map needed in its statement, and the inverse is uniquely determined. This avoids
  introducing an invertibility assumption or selecting an unnormalized isomorphism.
- The alpha component is the concrete `affineProperAdjointComparison ... F β`.
  Its defining body is `adj'.homEquiv` applied to beta inverse followed by pulled
  `adj.counit`. The presentation comparisons merely transport between the ambient
  direct images and their named restrictions. These are exactly the node's adjunct.
  These components define the stated natural transformation: homEquiv is natural,
  the original exchange is natural, and the inverse of an invertible natural map is
  natural. No independent comparison morphism is quantified over in the conclusion.
- `IsIso (affineProperAdjointComparison ...)` is precisely alpha_F invertible.
- The final equality is beta.hom, then Rf'_*alpha_F, then epsilon_f', equal to
  Lg*epsilon_f, in Lean composition order `≫`. `D'.comparison.inv` and
  `D.comparison.inv` identify the named restrictions with the ambient direct images.
  This is the exact counit equation, not an equality merely up to an unspecified iso.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `Modules`,
  `structureSheaf`, `EtaleSite`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the
  underlying Mathlib `SheafOfModules.IsQuasicoherent` predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedQCoh`,
  `derivedQCohProperty`, `derivedDirectImage`, `QCohDirectImagePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`,
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation` and their full defining bodies.
- `Sheaf.AlgebraicGeometry.SpaceDerivedPullback`: `spaceDerivedPullback` and its
  canonical composition comparison; it uses `derivedTensorPullback` from
  `Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback`.
- `Sheaf.AlgebraicGeometry.SpaceModuleDerivedExchange`: `moduleDerivedExchange`.
- `Sheaf.AlgebraicGeometry.RelativeDualizingTracePair`: `traceSchemeMap` only.
- `Sheaf.AlgebraicGeometry.SpaceDerivedQCohPullbackTensor`:
  `spaceDerivedPullback_tensor_preserve_QCoh`, with all four universes explicit.

The stated proof dependencies imported privately are
`SpaceAffinePullbackPerfectDetection`, `SpaceAffinePerfectHomBaseChange`,
`AffineEtaleDerivedModuleRealization`, and `RingedToposDerivedPushforwardComposition`.
The remaining proof dependencies `lem-sfb-flat-space-derived-pushforward-base-change`,
`lem-sfb-space-global-hom-right-adjunction`, and
`lem-sfb-flat-proper-space-perfect-sections` have no recorded Lean declaration in the
read DAG, so there is no recorded module to import for those proof steps. Their
mathematical role is preserved in the theorem docstring; the statement does not need
new definitions or assumptions from them.

Edge cases checked before writing: empty affine schemes and empty algebraic spaces
are admitted; zero complexes and arbitrary positive or negative cohomology degrees
are admitted; identity base change has the usual adjunction triangle formula; a
nonflat affine morphism g is admitted since it is f that is flat; there is no Noetherian,
coherence, representability-of-X, or boundedness assumption. Arbitrary choices of the
right adjunctions are retained, with their exact counits. Only the four categories
actually used have localization instances; no instance for every algebraic space is
required. No statement dispute or source-based correction is needed.

Searches made on 2026-10-24:

- `msearch.py ... leanfinder "Right adjoint to derived pushforward of a proper flat
  finitely presented algebraic space commutes with arbitrary affine base change"`:
  eight ordinary module-adjunction hits, none for this derived algebraic-space theorem.
- `msearch.py ... loogle "Adjunction.homEquiv, IsIso"`: zero hits, reporting the
  unqualified identifier `Adjunction.homEquiv` unknown to that search service.
- `msearch.py ... grep "adjoint.*[Bb]ase[Cc]hange|[Bb]ase[Cc]hange.*[Aa]djoint"`:
  two general over-category adjunction results; neither is this theorem.
- `rg` of the same patterns in `lean/WeilConjectures` and `lean/Sheaf`: scheme-only
  proper-flat right-adjoint theorems and constant-coefficient étale sheaf results,
  none covering small-étale structure-module algebraic spaces. The existing canonical
  exchange, pullback and direct-image constructions were found and reused.
- `rg` of the item id in `lean/WeilConjectures` and `lean/Sheaf`: no declaration for
  this item. Searches for `spaceQCohPullback`, `affineProperAdjointComparison`, and
  `affineFlatProperAdjointBaseChange` in both roots and `dag/lean_names_upstream.json`
  found no previous declarations with these names.

Compilation uses only the prescribed `scompile.py`. An initial unresolved localization
universe in the unused tensor half of the preservation theorem was repaired by specifying
`.{u, w, w, w}`. The helper data contain no sorry. The only sorry is the main theorem.

## Second reading by Q154

I reread the node and the completed file in the same worker session; the dispatcher
explicitly prohibits starting other agents. The maintainer's independent review remains
independent of this self-check. The correspondence above was checked against the actual
signatures and bodies, including the directions of both presentation comparisons.
The adjunct starts with `D'.comparison.hom`, beta inverse returns to Lg*Rf_*aF,
and `D.comparison.inv` followed by the given counit gives Lg*F. In the conclusion,
`D'.comparison.inv` converts Rf'_*a'Lg*F back to the supplied restricted functor before
applying its counit. Thus the endpoints and exact counit equation match.
The first reading used a family of localization instances for every space; this was
replaced by the four actual category instances. There is no hidden universe metavariable,
extra flatness on g, boundedness, or Noetherian assumption. No node statement changed.
