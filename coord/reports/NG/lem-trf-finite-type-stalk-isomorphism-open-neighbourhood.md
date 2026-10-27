## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeStalkIsomorphismOpenNeighbourhood` states
`AlgebraicGeometry.exists_isOpenImmersion_of_stalkMap_isIso_of_finiteType`, with its sole proof
left as `sorry`. Its docstring gives all seven steps of the accepted node's denominator
argument, naming every proof dependency. The source was read directly in
`literature/stacks-project/varieties.tex`, Tag 09NH, `lemma-local-isomorphism`, including its
full proof. The statement agrees with that source and the node; no correction is needed.

Hypothesis and conclusion correspondence:

- Schemes and their morphism: `{Y X : Scheme.{u}} (g : Y ⟶ X)`; universe `u` is explicit.
- Finite type: `[LocallyOfFiniteType g] [QuasiCompact g]`, exactly the two parts of the
  recorded finite-type definition. Quasi-compactness is retained even though the local
  proof only needs local finite type.
- Reduced target: `[IsReduced X]`, Mathlib's sectionwise reducedness, equivalent to
  reducedness of every local ring by the two stalk results in `Properties.lean`.
- Finitely many irreducible components: `(hcomponents : (irreducibleComponents X).Finite)`.
  This is finiteness of the actual set of maximal irreducible subsets, not Noetherianity
  or an assumption of irreducibility.
- The chosen point: `(y : Y)`. The image point is written directly as `g y`; introducing
  a separate variable or equality for `x` would add redundant data.
- The induced local-ring map is an isomorphism: `(hstalk : IsIso (g.stalkMap y))`.
  `Scheme.Hom.stalkMap` has domain `X.presheaf.stalk (g y)` and codomain
  `Y.presheaf.stalk y`. This concerns the canonical map, rather than the mere existence
  of a ring isomorphism between the two stalks.
- An open neighbourhood of `y`: `∃ V : Y.Opens, y ∈ V ∧ ...`.
- The restricted morphism is an open immersion: `IsOpenImmersion (V.ι ≫ g)`. Here
  `V.ι : V.toScheme ⟶ Y` is Mathlib's canonical inclusion of the open subscheme.
- No finite-presentation, Noetherian, or reduced-source assumption appears.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`.
- `def-weil-irreducible-components`: `Mathlib.Topology.Irreducible`,
  `irreducibleComponents`, through the node's `mathlib_match`.
- `def-weil-pbc-module-stalk`: the recorded module
  `WeilConjectures.Topology.PresheafModuleStalkFunctor` is imported publicly. Its
  `PresheafOfModules.moduleStalkFunctor` bundles Mathlib's existing stalk carriers.
  The present statement uses the ring-stalk clause of this dependency, so it uses
  Mathlib's `TopCat.Presheaf.stalk` via `Scheme.Hom.stalkMap`; it does not introduce
  module sheaves into a statement about local rings.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Restrict`, `AlgebraicGeometry.Scheme.Opens.ι`, provides
  restriction to the actual open subscheme.

All recorded statement-dependency modules are public imports. Proof-only imports provide
`Scheme.isBasis_affineOpens` and the affine stalk dictionary (`AffineScheme`), spectrum
components and radical zero loci (`Spectrum.Prime.Topology`), prime localization
(`Localization.AtPrime.Basic`), minimal-prime containment (`Ideal.MinimalPrime.Basic`),
radical intersections (`Ideal.Operations`), and localization away with its universal
property (`GroupTheory.MonoidLocalization.Away`, `RingTheory.Localization.Away.Basic`).
The remaining proof dependencies use modules already imported publicly. No dependency
module is missing and no import cycle was introduced.

Edge cases checked before writing:

- Empty source: there is no point `y`, as in the source statement. Empty target likewise
  cannot supply an image point of a nonempty source. No nonemptiness instance was added.
- Zero algebra generators: the docstring explicitly uses empty products equal to `1`.
- Several target components through `g y` and a minimal/generic image point are allowed;
  only the finiteness of the component set is assumed.
- A nonreduced source away from the chosen point remains allowed. Its chosen local ring
  is reduced as a consequence of the actual stalk isomorphism and reduced target.
- Identity morphisms and already open immersions satisfy the expected local conclusion.
- No field, characteristic, dimension, affineness, separatedness, or finiteness of
  presentation is imposed. Arbitrary scheme universe `u` is retained.

Searches made with `msearch.py NG lem-trf-finite-type-stalk-isomorphism-open-neighbourhood`:

- LeanFinder: “A finite type morphism to a reduced scheme with finitely many irreducible
  components inducing an isomorphism on local rings at a point is an open immersion near
  that point”. Eight hits, including `IsLocalIso.exists_isOpenImmersion`,
  `isLocalIso_iff`, and the stalkwise open-immersion criteria. The former assume local
  isomorphism already, and the latter require an open embedding and isomorphisms at
  every stalk. None gives this criterion from the stated hypotheses.
- Loogle: `AlgebraicGeometry.Scheme.Hom.stalkMap, AlgebraicGeometry.LocallyOfFiniteType`.
  Two hits: `LocallyOfFiniteType.stalkMap` only gives essentially finite type on local
  rings; `spread_out_of_isGermInjective` spreads a supplied stalk map to a morphism,
  assumes germ injectivity, and does not assert this open-immersion conclusion.
- LeanSearch: “Finite type morphism over a reduced scheme with finitely many irreducible
  components and isomorphic local rings is an open immersion on a neighbourhood”.
  Eight hits on local isomorphisms, existing open immersions, and principal localization;
  no matching theorem.
- Mathlib grep: `stalk.*[Ii]so|[Ii]so.*stalk|local.*isomorph` in `AlgebraicGeometry`.
  Twenty-five returned hits, principally restriction, spectrum stalk comparisons, and
  open-immersion criteria. Relevant criteria and the spreading-out signature were opened.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for Tag 09NH, this node id,
  finite-type/stalk/neighbourhood patterns, and the proposed declaration name. No exact
  statement exists. The affine-source neighbourhood theorem mentions this item only
  in its proof plan. Quasi-finite factorization results concern different hypotheses
  and conclusions. Searching this node id in `lean/WeilConjectures` returned no match.
- The proposed full declaration name was also searched in Mathlib and
  `dag/lean_names_upstream.json`; no collision was found.

Validation: the prescribed `scompile.py` compiled this file in sandbox and library modes,
with no errors or warnings. The only postponed proof is the named main theorem.
There are no new nodes, dependency repairs, or statement disputes.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
