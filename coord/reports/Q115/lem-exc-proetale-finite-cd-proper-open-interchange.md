## Worker report

The module `Sheaf/SecSmoothPurity/ProEtaleFiniteCDProperOpenInterchange.lean`
states `AlgebraicGeometry.Scheme.proEtaleFiniteCDProperOpenInterchange`.
It uses the published canonical map
`sfProperOpenDerivedComparison`, whose source is
`Rr_* ⋙ i_!` and whose target is `k_! ⋙ Rp_*`, with the pullback square
`(IsPullback.of_hasPullback p i).flip`.  No definition is duplicated: the
sheaf comparison, open extension, ordinary derived operations, and open
adjunction are the recorded declarations below.

The Lean signature renders the node clause by clause as follows.

* The finite coefficient hypothesis is
  `(A : Type u) [CommRing A] [Finite A]`.
* The scheme morphisms and geometry are
  `{V T W : Scheme.{u}} (p : V ⟶ T) (i : W ⟶ T)`, with
  `[IsProper p] [IsOpenImmersion i]`.  The open is arbitrary; no
  quasi-compactness instance is bound.  The Cartesian object and its
  projections are the Mathlib `pullback p i`, `pullback.fst p i`, and
  `pullback.snd p i`.
* The integer (d\geq0) is `(d : ℕ)`.  The all-sheaf finite-CD clause is
  `hcd`: for every
  `F : proEtaleRingModules V (proEtaleConstantRing V A)` and `q : ℕ`,
  `d < q` implies that the `q`-th homology of
  `proEtaleConstantDerivedDirectImage p A` applied to the degree-zero
  `DerivedCategory.singleFunctor` of `F` is `IsZero`.  This is exactly the
  ordinary constant-coefficient (R^q p_*F=0) hypothesis and quantifies over
  every module sheaf.
* The comparison is
  `sfProperOpenDerivedComparison A (pullback.snd p i) (pullback.fst p i)
  i p (IsPullback.of_hasPullback p i).flip`, and its isomorphism assertion is
  `IsIso`.
* The canonical restriction inverse is
  `proEtaleOpenRestrictionLambdaInverse p i A`; its `IsIso` assertion records
  the specified canonical restriction isomorphism and its open-unit
  normalization.
* For each
  `M : proEtaleDerivedCategory (pullback p i) A`, the first displayed
  conjunction is the unit form of
  `lambda_M \circ i^* Gamma_M = 1`: the unit of
  `exceptionalOpenAdjunction i A`, followed by
  `(sfIntrinsicDerivedPullback A i).map` of the comparison component, equals
  `(proEtaleOpenRestrictionLambdaInverse p i A).app M`.  The latter is the
  explicitly specified inverse of `lambda_M`, so this equation is exactly the
  same normalization without introducing a noncanonical inverse operation.
* The second displayed equation is the open-adjunction transpose:
  the comparison component equals `i_!` applied to that inverse restriction,
  followed by the counit of `exceptionalOpenAdjunction i A`.  This renders
  `Gamma_M = epsilon_i \circ i_!(lambda_M^{-1})` and fixes the map itself.
  Naturality in `M` is supplied by the natural transformation
  `sfProperOpenDerivedComparison`; the `IsIso` assertion therefore gives all
  component isomorphisms.

The module docstring records all six proof steps from the node: K-injective
representatives with injective terms and a resolution of `k_!J`; termwise
acyclicity from `isZero_higherDirectImage_cartesianOpen_injective` and injective
vanishing; the finite-CD acyclic-complex comparison; independence and naturality
from K-injective Hom bijectivity; the restriction/unit normalization; and the
open-adjunction counit formula.  Every theorem body is `sorry`.

The dependency declarations used are:

* `def-pc-scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` from Mathlib module
  `Mathlib.AlgebraicGeometry.Scheme`.
* `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` from
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
* `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and its `fst`/`snd`
  projections from `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
* `def-weil-pbc-proetale-site`: `AlgebraicGeometry.Scheme.ProEt` from
  `Mathlib.AlgebraicGeometry.Sites.Proetale`, repaired in the recorded module
  `Mathlib.AlgebraicGeometry.Sites.Proetale`.
* `def-weil-pbc-constant-sheaf`: `CategoryTheory.constantSheaf` from
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
* `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules`
  from `Sheaf.CategoryTheory.RingedSiteModules`.
* `def-weil-pbc-proetale-operations`:
  `AlgebraicGeometry.Scheme.proEtaleConstantRingPullback`,
  `proEtaleConstantRingPushforward`, and
  `proEtaleConstantRingDerivedPullback` from
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`, together with
  `proEtaleConstantDerivedDirectImage` from
  `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`.
* `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` from
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
* `def-weil-derived-cohomology-sheaves`: Mathlib's
  `DerivedCategory.homologyFunctor` from
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
* `lem-exc-proetale-proper-open-sheaf-comparison`:
  `AlgebraicGeometry.Scheme.sfProperOpenSheafComparison` and its
  `sfProperOpenSheafComparison_isIso` statement from
  `Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison`; the derived
  comparison used here is its published `sfProperOpenDerivedComparison`
  transport in `Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange`.
* `def-weil-extension-by-zero`:
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero` from
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`.
* `lem-weil-extension-by-zero-exact`:
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero_exact` from
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`.
* `prop-pur-kinjective-resolutions-exist`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`
  from `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
* `lem-exc-proetale-derived-open-restriction`:
  `AlgebraicGeometry.Scheme.proEtaleOpenRestrictionLambdaInverse` and
  `proEtaleDerivedOpenRestriction` from
  `Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction`.
* `prop-exc-open-adjoint`:
  `AlgebraicGeometry.Scheme.exceptionalOpenAdjunction` from
  `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`.

The proof-only imports also expose the exact declarations used by the node's
proof: `isZero_higherDirectImage_cartesianOpen_injective`,
`exists_rightDerived_computes_acyclic_of_finite_dimension`, and Mathlib's
`CochainComplex.IsKInjective.Qh_map_bijective`.

Edge cases checked before writing the signature were: (d=0); the zero ring
(which is a finite commutative ring); (M=0); the empty open (W=\varnothing);
the identity open (i=\mathrm{id}); the identity proper morphism; and an
empty or non-quasi-compact open.  The signature imposes no nonempty, quasi-
compact, bounded, constructible, or etale-origin restriction, and uses the
scheme universe for all sites and coefficients.

Searches made:

* `msearch.py ... leanfinder "Finite cohomological dimension proper pushforward
  commutes with extension by zero on unbounded proetale derived categories"`:
  eight hits, including generic `SheafOfModules.pushforwardComp` and related
  pushforward composition declarations; none states this fixed-coefficient
  comparison.
* `msearch.py ... loogle "CategoryTheory.Functor.rightDerivedFunctor IsIso"`:
  zero hits and an unknown-constant diagnostic; this is not evidence of an
  exact match, and the published comparison was checked directly instead.
* `msearch.py ... grep "ProperOpenDerivedComparison" AlgebraicGeometry`:
  zero hits in Mathlib.
* `rg -n 'finiteCDProperOpenInterchange|sfProperOpenDerivedComparison'` in the
  project and source: only the existing canonical
  `sfProperOpenDerivedComparison` in
  `Sheaf/AlgebraicGeometry/ProperExceptionalOpenBaseChange.lean`; no declaration
  for this node.
* `grep -rn 'lem-exc-proetale-finite-cd-proper-open-interchange'` in the source
  and project Lean: no existing declaration.

No new definition node or dependency module was needed.  No statement fault or
`STATEMENT-DISPUTED` flag was found.

## Second reading by Q115

I reread the target node and the completed module side by side.  The binders
`A`, `p`, `i`, `[IsProper p]`, `[IsOpenImmersion i]`, `d`, and `hcd` match the
finite ring, proper morphism, arbitrary open immersion, and all-sheaf bound in
the node.  The first conclusion is the canonical `Gamma` map with exactly the
node's Cartesian projections and ordinary unbounded derived functors.  The
second conclusion states the canonical restriction isomorphism.  For every
`M`, the first equation is the unit-expanded form of
`lambda_M \circ i^* Gamma_M = 1`, and the second is exactly the counit formula
for `Gamma_M`; no object, hypothesis, or edge case was added or omitted.  The
module docstring's six numbered paragraphs match the six proof steps and cite
the same dependency declarations.  The module compiled cleanly with
`scompile.py`, with only the expected `sorry` proof warning suppressed by the
module options.
