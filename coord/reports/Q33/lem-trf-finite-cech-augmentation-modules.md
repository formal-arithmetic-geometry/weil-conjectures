## Worker report

Repaired H3 from immutable head 65eee7c0dd61. The initial saved-packet dry run returned
OK at 0dc7b51457, but mathematical self-check confirmed the review: existential cofaces
could encode any differential, the augmentation was arbitrary, injectivity at F was
missing, cover maps had the wrong direction, and mere existence of chain maps did not
supply coherent naturality. The old arbitrary `FiniteCechAugmentationData` is removed.

The module defines the actual canonical sequence of module sheaves, as concrete maps,
and states `AlgebraicGeometry.finite_cech_augmentation_modules`. Its conclusion is the
proposition `FiniteCechAugmentationProperties Λ p`; every field is a proposition about
fixed maps. There is no existential complex, unspecified coface, term isomorphism,
augmentation, or naturality map. The only existential witnesses are proofs that two
consecutive fixed arrows compose to zero, needed by `ShortComplex.mk`.

Hypothesis and clause check:

- The commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]`; schemes are
  `Scheme.{u}` and the cover is `(p : Z ⟶ Y) [IsFinite p] [Surjective p]`.
- F ranges over `Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, the standard
  constant-coefficient module-sheaf encoding prescribed by brief-stage2 §2. This is
  equivalent to modules over the constant ring sheaf; no arbitrary ring sheaf is used.
  `CategoryTheory.ringedSiteModules` is imported as the recorded general-site module
  category interface, with Mathlib's module-valued sheaf encoding here as prescribed.
- `finiteCechScheme p n` is Mathlib's actual `(n+1)`-fold wide pullback; its base map
  is `finiteCechProjection p n`. In degree zero this one-factor wide pullback is
  canonically isomorphic to Z, so its unit is the usual p-augmentation transported
  through that canonical identification.
- `finiteCechTerm Λ p n F` is exactly `(p_n)_* (p_n)^* F`, using the recorded
  `Etale.lowerStar` and `Etale.upperStar`. `finiteCechTermFunctor` supplies the
  coefficient map `(p_n)_* (p_n)^* α` with functorial identity/composition laws.
- `finiteCechTriangleMap` is explicitly lowerStar of the adjunction unit for r,
  followed by `Etale.lowerStarComp.hom` and lowerStar of `Etale.upperStarComp.inv`.
  `finiteCechCoface` specializes it to `(Arrow.mk p).cechNerve.δ i`. By Mathlib's
  Čech nerve definition this selects the coordinates through `SimplexCategory.δ i`,
  namely deletion of coordinate i. The triangle equality comes from naturality of
  Mathlib's canonical scheme augmentation. There is no existential delta family.
- `finiteCechDifferential` is the sum of these very cofaces with signs +,-,+,... .
  `finiteCechAugmentation` is the actual adjunction unit for `p_0`.
- Exactness of `0 → F → C^0 → C^1 → ...` includes all degrees:
  `augmentationMono` is injectivity at F, `augmentationExact` is exactness at C^0,
  and `positiveExact F n` is exactness at C^(n+1). The latter two also include the
  zero-composite equations for the fixed arrows, hence define a complex.
- `coefficientAugmentation` and `coefficientCoface` assert the naturality squares
  for the specified functorial coefficient maps. Additivity gives the differential
  squares from the coface squares, so these are natural augmented complexes.
- For every map `a : W ⟶ Z` with `a ≫ p = p'`, where p' is finite surjective,
  `finiteCechCoverMap` uses `Arrow.mapAugmentedCechNerve`, applying a in every
  coordinate, and the same explicit triangle unit construction. Its direction is
  `C_p^n(F) → C_p'^n(F)`, as required by contravariance in covers.
- `coverAugmentation` and `coverCoface` assert the augmentation and each coface
  square for those fixed maps. `coverCoefficient` is their compatibility with α.
  `coverIdentity` and `coverComposition` assert equality with the identity map and
  the map for the composite, respectively. Thus naturality is coherent, with no
  arbitrary comparison map and no choices from the exactness proof.

Dependency declarations used in definitions: `AlgebraicGeometry.IsFinite` in
`Mathlib.AlgebraicGeometry.Morphisms.Finite`; `AlgebraicGeometry.Surjective` in
`Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`; the small étale site in
`Mathlib.AlgebraicGeometry.Sites.Etale`; `CategoryTheory.constantSheaf` in
`Mathlib.CategoryTheory.Sites.ConstantSheaf` for the constant-coefficient interpretation;
`CategoryTheory.ringedSiteModules` in `Sheaf.CategoryTheory.RingedSiteModules`;
`CategoryTheory.Limits.pullback` and the wide-pullback implementation of
`CategoryTheory.Arrow.cechNerve`, `augmentedCechNerve`, and `mapAugmentedCechNerve`;
`AlgebraicGeometry.Etale.upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`,
`lowerStarComp`, and `upperStarComp`, all in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
The modules of the recorded proof dependencies are imported without public visibility,
including the constant-module transport, finite stalk restriction, inverse-image germ,
geometric-fibre constant comparison, and coefficient-forgetting results. The geometric
stalk, base-change, and finite/composition Mathlib leaf modules are imported as well.
Missing/stale upstream source files were read with `scompile.py --source`.

The complete natural-language proof is retained in the theorem docstring: unit-based
cofaces and square-zero equations; finite nonempty geometric fibres; stalk identification
with functions on tuples and coordinate-deletion formula; prepend-a-point contraction
including degree zero; exact geometric stalks and forgetting coefficients; coefficient
naturality; and cover naturality from composition-unit equations.

Edge cases checked: F=0; empty Y (all relevant module sheaves are zero); an isomorphism
cover; radicial/nonreduced covers (one geometric lift); one- and two-point fibres; n=0;
identity maps of covers and two successive refinements; and the zero coefficient ring.
For a non-surjective cover the augmentation can fail to be mono, so surjectivity is
necessary. The coface and identity formulas make sense without choosing any point in a
geometric fibre; chosen fibre points occur only in the proof of exactness.

Searches made before writing the module:

- `msearch.py Q33 lem-trf-finite-cech-augmentation-modules leanfinder "finite etale Cech
descent for bounded below Lambda module sheaf complexes"`: generic sheaf finiteness and
condensed-module declarations only; no matching theorem.
- `msearch.py ... leansearch "derived global sections of a finite surjective Cech nerve with
module coefficients"`: generic Cech nerve and sheaf-module infrastructure only; no match.
- `msearch.py ... loogle "CechNerve"` and quoted `"CechNerve"`: generic Cech-nerve limits
only; no module-sheaf descent theorem.
- `msearch.py ... grep "finite.*(descent|[Cc]ech)|([Cc]ech|[Čč]ech).*finite" CategoryTheory`:
no matching finite Cech descent declaration.
- `rg -n "Cech|cech|finite.*descent" /home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
`rg -n "Cech|cech|finite.*descent" lean/Sheaf`: existing results concern generic Cech
complexes, open-cover resolutions, or unrelated sheaf operations; none states this finite
surjective module-sheaf augmentation.
- `grep -rl "lem-trf-finite-cech-augmentation-modules" dag/nodes`: only this node and its
review/ancestry references; no duplicate declaration node.


Additional repair search: `msearch.py ... loogle '"upperStarComp"'` returned no hits;
the exact existing comparison was found and its full signature read in the upstream
`UpperLowerStar/Defs.lean`. `rg` for `FiniteCech`, `finiteCech`, and Čech augmentation
in the project and upstream found a derived global-sections construction in
`Sheaf.TraceFormula.FiniteBaseCechHypercohomology` (in namespace
`AlgebraicGeometry.Etale`) and the ordinary site-cover resolution. Neither defines the
underived module-sheaf unit map for arbitrary finite covers used here. No new independent
notion or node is needed: these canonical maps are helpers of the owning node.

No statement correction or STATEMENT-DISPUTED flag is needed. The node is retained
unchanged outside `lean`.

## Second reading by Q33

I reread the node, all seven proof steps, Stacks Tag 09Z2 in the local source, and the
revised Lean file. This is the required self-check of a dispatcher worker; no other
agent was started. The review found the old existential cofaces and augmentation,
missing injectivity at F, reversed refinement map, and missing identity/composition and
mixed naturality laws. All are repaired by the fixed definitions and proposition fields
detailed above. I checked the triangle map's types in order: p_*η_r, the pushforward
composition comparison, then p'_* of the inverse pullback comparison. The cover square
uses the same arrow and its commuting triangle. In degree n, δ_i uses exactly the
scheme coordinate-deleting face, and n=0 exactness includes both F and C^0. The positive
short complexes are centred at C^(n+1), covering every remaining degree. Coefficient
maps are the actual composite functor maps; cover maps satisfy explicit identity,
composition and coefficient-compatibility equations. The one-factor wide pullback in
degree zero only changes the standard term by its canonical identification. No data
is defined using sorry and the only postponed theorem is the node's theorem itself.
