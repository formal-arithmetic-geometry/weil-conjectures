## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianAffineLineUnit` states
`AlgebraicGeometry.Etale.isIso_noetherian_affineLine_unit`, with proof `sorry`.
It introduces no definition, auxiliary theorem, or replacement category. The declaration
docstring reproduces all seven proof steps of the DAG, including the actual-unit
normalization and the split-triangle calculation.

Source checked: ILO, Travaux de Gabber, Expose XVI, Proposition 1.5, printed p. 227
(PDF p. 233). Its proof identifies the canonical map with the affine-space homotopy
invariance map for schemes over Z[1/m]. The Noetherian specialization in this node
therefore requires neither a regular base nor a morphism to a field.

Hypothesis and conclusion correspondence:

- A scheme B: `(B : Scheme.{u})`, with arbitrary explicit universe `u`.
- Noetherian, meaning a finite affine cover by Noetherian rings: `[IsNoetherian B]`.
  Mathlib Noetherian.lean defines this as locally Noetherian and compact and proves
  `isNoetherian_iff_of_finite_iSup_eq_top`, precisely the stated cover characterization.
- A prime ell: `(ell : ℕ) (hell : ell.Prime)`.
- Exponent n at least one: `(n : ℕ) (hn : 0 < n)`.
- ell invertible on B: `(hB : IsUnit (ell : Γ(B, ⊤)))`. A global inverse restricts to
  every stalk; conversely local inverses glue uniquely, so this is invertibility on B.
- Lambda = Z/(ell^n): `ULift.{u + 1} (ZMod (ell ^ n))`. ULift only changes the
  carrier universe, canonically preserving this ring; it introduces no coefficient assumption.
- The affine line and its projection: `AffineSpace (ULift.{u} (Fin 1)) B ↘ B`.
  Mathlib AffineSpace.lean uses the integral polynomial affine-space base change;
  its `over` instance is the first pullback projection, not an arbitrary morphism.
- Ordinary small-etale module derived categories: the coefficient category is
  `ModuleCat.{u + 1} (ULift.{u + 1} (ZMod (ell ^ n)))` throughout. Its sheaf category
  is on B.smallEtaleTopology (and the corresponding affine-line site), matching
  `DerivedCategoryModule` in the recorded category dependency.
- Lambda_B and Lambda_A1 are the existing `ordinaryFiniteUnit`, the constant module
  sheaves placed in degree zero with `DerivedCategory.singleFunctor`.
- The canonical unit is `(derivedUpperStarLowerStarAdjunction ... p).unit.app ...`,
  followed by `ordinaryFinitePushforward ... p` applied to
  `(ordinaryFiniteUnitPullback ... p).hom`. The latter is the existing canonical
  single-complex/constant-sheaf pullback comparison. This spells out the target
  identification with Lambda_A1 rather than leaving the unit at an unidentified pullback.
- The asserted isomorphism is exactly `IsIso` of this composite. There is no
  existential choice of an isomorphism between endpoints, and no regularity,
  separatedness, finite-type-over-a-field, or field-structure hypothesis.

Dependency declarations used (source declarations and their full interfaces were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`,
  `isNoetherian_iff_of_finite_iSup_eq_top`.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace` and `AffineSpace.over`,
  as specified by def-sbc-affine-space.mathlib_match (that node needs no lean record).
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: `DerivedCategoryModule`.
  The current server source was read with scompile.py --source because the former
  is absent in the older local upstream checkout.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `etaleInverseImageModulesExact`, giving exact constant-ring inverse image and the
  specified adjunction. Its current full server source was read with --source.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `upperStar`, `lowerStar`,
  `upperStarLowerStarAdjunction`. `Derived.UpperLowerStar` supplies
  `derivedUpperStarLowerStarAdjunction`, the derived adjunction of those functors.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows`: `ordinaryFinitePushforward` and
  `ordinaryFiniteUnitPullback`; its public import OrdinaryFiniteP1Kummer supplies
  `ordinaryFiniteUnit`. The full definitions were read: pushforward is the existing
  right derived functor; the comparison is the derived single-functor comparison
  followed by `Scheme.upperStarConstantSheafIso` applied to the regular module.
  Added the already-landed `def-asd-ordinary-finite-p1-arrows` to stmt_deps to cite
  these shared canonical arrows explicitly, as permitted by brief-stage2 section 5.

All available recorded proof-dependency modules are imported non-publicly. Mathlib
adjunction uniqueness and triangle exactness modules are also imported for their
recorded proof matches. The not-yet-recorded closed-sheaf internal adjunction has
no import to add; it is only a future proof input, not a missing statement notion.
No dependency interface repair is required.

Edge cases checked: the empty scheme is admitted (its zero global ring makes the
invertibility condition valid); disconnected, singular and nonreduced Noetherian
schemes are admitted. Arbitrary mixed characteristic bases with ell inverted are
admitted. n = 1 and ell = 2 are included. n = 0, ell = 0 and ell = 1 are excluded
exactly by the source's stated positive-exponent and prime assumptions. No index
or coefficient universe imposes a size restriction on B.

Searches for an existing exact declaration:

- msearch.py leanfinder: "For a Noetherian scheme with ell invertible the ordinary
  etale derived affine line unit on Z modulo ell power is an isomorphism" returned
  eight standard-etale algebra results, no derived-unit theorem.
- msearch.py loogle: `AlgebraicGeometry.AffineSpace, CategoryTheory.IsIso` returned
  only the empty-coordinate affine-space projection instance, a different statement.
- msearch.py grep: `homotopyInvariant|homotopy_invariant|[Aa]ffine[Ll]ine.*[Uu]nit`
  returned five topological Eilenberg-Steenrod homology hits, no etale theorem.
- msearch.py leansearch: ordinary etale affine-line homotopy invariance with finite
  invertible torsion over a Noetherian scheme; recorded separately in searches.jsonl.
- rg over upstream WeilConjectures and lean/Sheaf for affineLine/unit and the node id:
  `cohomology_affineLine_unit` in FourierTransform/ArtinSchreierCohomology requires
  an algebraically closed field and states cohomology groups, not this derived unit.
  `nonempty_iso_rightDerivedLowerStar_affineLine` in Purity/Smooth/AffineLine requires
  a separated scheme locally of finite type over a field and only an unspecified
  endpoint isomorphism. Both full signatures and docstrings were read; neither matches.
  Shared ordinaryFiniteUnit/pullback comparisons are reused, not duplicated.
- rg for the proposed full theorem name across Mathlib, upstream and side sources
  found no collision. The node id occurs only in the existing downstream proof plan.

Validation: scompile.py checked the single delivered module on the server, both
sandbox and library form, cleanly (4.6 s and 4.3 s). Only its theorem has `sorry`.
There are no statement corrections, new nodes, disputed claims or dependency modules.

## Second reading by Q51

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
