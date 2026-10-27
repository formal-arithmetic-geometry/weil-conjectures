## Worker report

The delivery states `lem-sp-finite-site-tower-paste` in
`Sheaf.Paper.FiniteSiteTowerPaste`. All declarations are in
`AlgebraicGeometry.ProEtale.FiniteSiteTower`. The main theorem is `paste`;
`etale_normalization`, `paste_naturality`, `word_naturality`, and
`comparison_naturality` state the remaining normalization and naturality clauses.
Every theorem has proof `sorry`. Every definition has actual construction data.
All 27 declarations are listed in the node's `lean.declarations`.

The Q70 delivery and its independent `reviewed` entry concern the stage-1 split.
The current node has neither `lean` nor `reviewed_lean`, and the prescribed
`scompile.py --source Sheaf.Paper.FiniteSiteTowerPaste` reports that no such
published module exists. Thus this supplies the missing stage-2 statement; it
does not reopen or replace Q70's split. The item node is unchanged except for
its new `lean` field. No repair note exists for this item.

### Hypotheses and objects

- A finite commutative ring is `(R : Type (u + 1)) [CommRing R] [Finite R]`.
  The coefficient universe is the project's fixed-module-sheaf convention;
  no presentation, field, nonzero-ring, flatness, or Tor assumption is present.
- The six schemes are `X U XB Y YB Z : Scheme.{u}`. Each has an
  `IsNoetherian` instance, the standard scheme predicate for the stated finite
  Noetherian affine-cover condition. `XB` and `YB` denote the barred schemes.
- The six arrows are `a b p q i s` with exactly the domains and codomains in
  the node. The three opens have `IsOpenImmersion` and `QuasiCompact`
  instances; the three proper maps have `IsProper` instances.
- `sq : IsPullback b s p i` includes the equality `b ≫ p = s ≫ i` and its
  Cartesian universal property. There is no extra Cartesian assumption on
  the composite compactifications. The notation `f = s a`, `g = q i` is
  rendered by their composites; no independent morphisms or equality
  hypotheses are needed. The pairs `(a,s)`, `(i,q)`, `(a ≫ b,p ≫ q)` are
  exactly the supplied compactifications, rather than newly chosen ones.
- `DE` and `DP` abbreviate `DerivedCategory.Plus` of sheaves of
  `ModuleCat.{u + 1} R` on the small etale and pro-etale sites, respectively.
  These are ordinary constant-ring module categories, with no completion or
  constructibility restriction. The finite coefficient realization recorded
  in `def-weil-pbc-proetale-modules` identifies this existing fixed-ring
  presentation with modules over its constant coefficient sheaf. No second
  module-sheaf or derived-category construction is introduced.
- `N` is the existing exact `comparisonUpperStar` mapped to D+; `PE`, `PP`
  are the existing bounded-below right derived direct images, and `JE`, `JP`
  the existing exact open extensions mapped to D+. They are abbreviations,
  not new functor data. `E : DE R X` ranges over all bounded-below inputs,
  with no uniform lower bound or upper bound imposed.

### Every clause of the conclusion

- The specified `d_v` is `fixedComparisonDirectImageMatePlus R v`, not a
  selected isomorphism. The specified derived `e_j` is
  `properOpenSiteExtensionIso R j`, whose body applies exact derived descent
  to `openImmersionLowerShriekComparisonUpperStarIso`.
- `B R j r E` is exactly `d_r(J_j E)` followed by `P_r(e_j(E))`. Hence
  `B R a s`, `B R i q`, and `B R (a ≫ b) (p ≫ q)` give the three B maps.
  The words `F_f`, `F_g`, `F_gf` are written as `JE` followed by `PE`, or
  `JP` followed by `PP`, in the displayed components. They are the fixed
  compactification words, not an arbitrary compactification-independent
  replacement.
- `kE` and `kP` are constructed using `conjugateIsoEquiv` on the single-map
  derived inverse-image adjunction and the composite derived adjunction.
  They invert the pullback composition isomorphism before conjugating and
  invert the result afterward, exactly the node's specified normalization.
  `mE`, `mP` are exact-derived descents of the inverses of the recorded
  open-extension composition isomorphisms. Those recorded isomorphisms point
  from composite extension to iterated extension, so the inverse is required.
  Components use ordinary categorical composition, incorporating the
  canonical functor associators without unidentified equality transports.
- `GE` is the specified `Etale.properOpenCoefficientInterchangePlus` at
  `JE a E`. `GP` uses `properOpenSiteInterchange` at this same etale-origin
  object and changes its input coordinate from `N(JE a E)` to `JP a (N E)`
  with the canonical open comparison and its inverse. The middle map is the
  actual open adjunct of `properOpenSiteRestrictionInverse`. In particular,
  neither `GP` nor `AP` is defined using the requested final transport formula.
- `AE`, `AP` first apply `P_q` to the corresponding interchange, then the
  proper compositor, then `P_(pq)` of the open compositor. These are the
  node's actual tower arrows, in the stated directions.
- `etale_normalization` compares `AE` under the fully faithful D+ inclusion
  with `AEUnbounded`, using explicit source and target compatibility
  isomorphisms. `AEUnbounded` is the recorded normalized unbounded tower
  prescription: the specified unbounded proper/open interchange, the
  unbounded conjugate proper compositor, and the exact-derived open
  compositor. The dependency's tower-normalization theorem identifies this
  precise word with its compact-support compositor. Thus the normalization
  is stated as equality of actual arrows after the canonical inclusion
  identifications, not merely an existence of isomorphic endpoints.
- `Win` has, in order, `d_q`, `P_q(e_i)`, `P_q J_i(d_s)`,
  `P_q J_i P_s(e_a)`. `Wout` has `d_q`, `P_q(d_p)`, `P_q P_p(e_b)`,
  `P_q P_p J_b(e_a)`. Lean's `≫` writes the opposite textual order from
  the node's right-to-left `∘`, so these match all four factors exactly.
- The first conjunct of `paste` is `N(P_q GE) ≫ Wout = Win ≫ P_q GP`,
  precisely the word equation. The second is
  `N(AE) ≫ B_gf = D ≫ AP`, precisely the equation after both compositors.
  `D` is defined as `B_g(F_f E)` followed by `F_g^p(B_f(E))`.
- The next conjuncts state invertibility of the actual `AP`, of `D`, and
  of the three B components. These record the comparison isomorphisms and
  witnesses used in the node's proof. The last conjunct, for any proof `h`
  that `D` is invertible, states
  `AP = inv D ≫ N(AE) ≫ B_gf`; it is exactly the final transport formula,
  and is a conclusion rather than a definition.
- `paste_naturality` states naturality of the actual pro-etale paste.
  `word_naturality` states naturality of both word comparisons and `AE`.
  `comparison_naturality` states naturality of the three B maps and `D`.
  The naturalities of `GE`, the underlying site adjunct, and the component
  compositors are inherited from the dependency's prescribed natural maps.
  Together these render the assertion that all expressions are natural in E;
  inverses of the resulting natural isomorphisms are natural as well.
- All intermediate inputs are actual D+ objects: exact site comparison and
  open extension and right-derived direct image are functors between D+
  categories. The origin witness for `JP a (N E)` is the open comparison
  with `JE a E`. The witness for `PP s (JP a (N E))` is `B R a s E`, whose
  invertibility is explicitly asserted. No preservation of boundedness under
  extension of coefficients is used.

### Dependency declarations read and used

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its
  category of morphisms; `Mathlib.RingTheory.Noetherian.Defs`:
  `IsNoetherianRing`. The geometric Noetherian hypothesis uses Mathlib's
  `AlgebraicGeometry.IsNoetherian`, supplied by the existing interfaces.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `Etale.DerivedCategoryModule`, Mathlib `DerivedCategory.Plus`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `FiniteCoefficientModules`, `FiniteCoefficientDerivedCategoryPlus`,
  `FiniteCoefficientEtaleDerivedCategory`, and coefficient realization.
  The fixed-ring `Sheaf … (ModuleCat R)` presentation is already supplied by
  the comparison and operation dependencies and needs no replacement node.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparison` and its module specialization. The
  specialized exact functor used by the recorded mate interface is
  `ProEtale.comparisonUpperStar`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonDirectImageMatePlus`, with its stated counit normalization
  and qcqs invertibility. Imported publicly and used directly in every B
  and word comparison.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparisonUpperStarIso`,
  `proEtaleOpenExtensionComp`; their exact-derived open comparison is
  `properOpenSiteExtensionIso` in
  `Sheaf.Paper.ProEtaleProperOpenComparison`, reexported by the proper/open
  dependency. `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`:
  `Etale.openImmersionLowerShriekComp` and its canonical composition coherence.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` supplies the
  arbitrary constant-ring specialization of the ordinary operations.
  Here the finite-ring fixed-coefficient operations already used in the
  recorded mate and proper/open dependencies are used, including
  `ProEtale.lowerStar`, `ProEtale.openImmersionLowerShriek`, and
  `ProEtale.derivedUpperStarLowerStarAdjunctionPlus`. The corresponding etale
  operations and adjunction are in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`.
- `Sheaf.AlgebraicGeometry.CompactifiableOverField` explains that the
  defining notion is the existing `Compactification` structure. Only the
  supplied open/proper factorizations are needed here; its extra existence
  theorem over a field is not a hypothesis of this result.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedLowerShriekOfCompactification` is exactly the word
  `D(j_!) ⋙ R(r_*)`. The module keeps that factorization explicitly.
- `Sheaf.Paper.ProperOpenCoefficientMate`:
  `Etale.properOpenCoefficientInterchange`,
  `Etale.properOpenCoefficientInterchangePlus`,
  `ProEtale.properOpenSiteInterchange`,
  `ProEtale.properOpenSiteRestrictionInverse` and their naturality clauses.
  Imported publicly. Their signatures and full construction bodies were read.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `Etale.unboundedEtaleLowerShriekCompIso_tower` gives the normalized
  unbounded proper/open tower. Imported for the proof and normalization.
  The proof dependency `lem-sp-finite-site-word-refinement` has no Lean
  record yet, so there is no corresponding module to import. It is used
  only in the natural-language proof, not as a missing notion or hypothesis.

### Source and edge cases

Read `literature/stacks-project/more-etale.tex`,
`lemma-shriek-composition` (Tag 0F7J), including the four displayed
equalities, and `lemma-shriek-proper-and-open` (Tag 0F7B). Stacks supplies
the etale tower and proper/open map; site comparison pasting is the
agent-written deduction recorded in the node. The theorem docstrings give
the seven-step proof plan and the naturality/normalization subarguments.

Checked the zero coefficient ring, zero input complex, empty schemes,
identity opens, identity proper maps and the entirely identity tower.
There is no nonemptiness, nonzero, positive degree, bounded-above, or
nonidentity-map hypothesis. The B and word definitions still use the exact
comparison maps in these cases. With nonidentity `a`, `GP` retains both
open-comparison factors, so its etale-origin witness is not silently
identified with its input. Proper and open compositor directions were
checked against the actual source signatures. Independent site object and
morphism universes are those of the existing small sites; no equality of
those universes has been imposed.

### Searches and validation

Required searches were run with `msearch.py`; actual results are retained
in the sandbox's `searches.jsonl`:

- LeanFinder: "Etale proetale comparison preserves proper open compatible
  compactification tower composition" returned eight results about etale
  maps, proper composition, directed schemes, and profinite projections;
  none states this site-comparison tower equation.
- Loogle: `CategoryTheory.mateEquiv, CategoryTheory.conjugateEquiv` returned
  four generic mate/conjugacy identities. They are tools for the calculation,
  not the geometric finite-site statement.
- Mathlib grep: `properOpen|FiniteSiteTower|tower_paste` in
  `AlgebraicGeometry` returned no hits.
- Direct `rg` over both project Lean roots for
  `finite.site.*tower|FiniteSiteTower|lem-sp-finite-site-tower-paste`
  returned no existing declaration or module. The published-module source
  probe also found no existing `Sheaf.Paper.FiniteSiteTowerPaste`.

`scompile.py Q152 lem-sp-finite-site-tower-paste` compiled the final module
in sandbox and library-module coordinates cleanly (27.0 s and 18.8 s),
within the unchanged 60 s limit. `autoImplicit` is false. There are no
line-width or other warnings, no data `sorry`, no private definitions,
no file-local notation or instances, no custom axioms, and no statement
correction or disputed claim.

## Second reading by Q152

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
