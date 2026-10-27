## Worker report

The delivery states `WeilConjectures.CanonicalTate.canonicalTateArrowNaturality`
in `Sheaf.Paper.CanonicalTateArrowNaturality`. Its proof is `sorry`. The supporting
module `Sheaf.Paper.CanonicalTateComparisons` supplies the missing normalized
comparison maps between the existing intrinsic Tate lines, without redefining
those lines, the coefficient categories, or their operations. Every postponed
property is a named theorem with a source, blueprint reference, and proof
explanation. Definitions use explicit composites or uniquely characterized maps.
No comparison is selected from a bare existence or `Nonempty` assertion.

Hypotheses and objects, checked against the item and the current blueprint:

- `D : FiniteFieldDatum` fixes the finite field, its algebraic closure, and the
  geometric Frobenius. `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p` express the
  prime and characteristic restriction. `E`, `[Field E]`, `[Algebra (Padic l) E]`,
  and `[FiniteDimensional (Padic l) E]` express the finite coefficient extension.
- `X₀ Y₀ : Over (Spec (CommRingCat.of D.k₀))`, with `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` on each structure morphism, are exactly the
  two separated finite-type models. `w₀ : X₀ ⟶ Y₀` is arbitrary; in particular
  it need not be smooth or an isomorphism. `geometricMap D w₀` is its actual
  geometric base change. `D.geometricFrobenius` is the geometric Galois map,
  rather than the absolute scheme Frobenius. The commuting square is the
  component of `D.frobenius_square_cartesian`.
- `sfWeilPrimeInvertible` supplies the residue-field invertibility instances
  from these hypotheses; they are not extra assumptions on the theorem.
- `Ω : Type v`, with field, Padic algebra, and algebraic-closure instances,
  is independent of the scheme universe `u`. The common coefficient category
  uses its existing small finite coefficient models. The small pro-etale site
  retains object universe `u+1` and morphism universe `u`.
- The finite level index `n : ℕ` denotes the existing quotient with exponent
  `n+1`. Thus the universal quantifier includes every required positive
  exponent, without adding the zero quotient or omitting exponent one.

Clause-by-clause rendering of the conclusion:

1. `ArrowSquare` is the literal equality
   `R.map tau.hom ≫ t.hom = comparison.hom ≫ G'.map t.hom ≫ tau'.hom`.
   Lean composes in the opposite written order from the displayed TeX.
   `GeometricLaws` universally quantifies the spatial equation over `r : ℕ`.
   `finiteGeometricLaws`, `integralGeometricLaws`, `rationalGeometricLaws`, and
   `commonGeometricLaws` instantiate it with the recorded pullbacks and lines.
   `finitePull`, `integralPull`, `rationalPull`, and `commonPull` give `t_w`;
   the corresponding `*Square` definitions give `C_w`. Finite pullback is
   transported through the uniquely unit-normalized `finiteRealization`.
   Integral pullback uses the published good-complex augmentation; rational
   and common comparisons are its localized and common-stage images.
2. `coefficientLaws` states the same `ArrowSquare` for every `n ≤ m` finite
   quotient, every integral-to-finite quotient, and every finite coefficient
   extension `ι : E →ₐ[Padic l] L`. The functors are respectively
   `coefficientFiniteQuotientDerived`, `constructibleReduction`, and
   `sfConstructibleIntegralScalarExtension`. Its last conjunct also gives the
   rationalized extension equation. `finiteScalarLine`, `integralReductionLine`,
   and `integralScalarLine` supply `t_R`; `pullbackTensorQuotient`,
   `reductionSquare`, and `integralPullbackScalarComparison` supply `C_R`.
   The integral reduction square is conjugated from the ordinary double-unit
   comparison using the specified K-flat quotient counit and completed
   augmentation; it is not chosen to force the desired Tate equation.
3. `Additivity` is exactly
   `mu.hom ≫ tensor.map (Prod.mkHom tau_r.hom tau_s.hom) ≫ alpha.hom =
   G.map alpha.hom ≫ tau_(r+s).hom`. Each `alpha` comes from the canonical
   root-list concatenation map `*Product`. Each `mu` is the recorded
   `canonical*PullbackTensor`. All `r s : ℕ` occur. `geometricTateLaws` includes
   the identity spatial map on `Y` as well, so additivity is stated on both
   source and target of the given spatial morphism.
4. `MixedIdentity` inserts exactly `comparison.inv ≫ W.map tau_s.hom` for
   the transported arrow. Its subsequent factor is
   `tensor.map (Prod.mkHom (𝟙 _) t_s.hom) ≫ alpha.hom`, the specified `a_w`.
   Both sides are arrows on the geometric target `X`, with the tensor source
   `T'_r ⊗ W(T_s)`. The source and target therefore match the corrected mixed
   identity already present in the supplied node, with no further correction.
5. `rootTowerLaws` uses `proEtaleRootsOfUnityInverseImageMap` and its actual
   adjunction unit at every root level `l^j`. `finiteRootSection` contains no
   arbitrary replacement map. The recorded root-system comparison retains its
   Kummer power transitions. `strictGeometricLaws` applies the actual ordinary
   reduction functor to equalities of entire total-tensor complexes, obtaining
   equations of entire strict quotient systems, rather than unrelated derived
   equalities at each level. `strictCoefficientLaws` gives integral reduction
   before realization and equality of the whole strict target system under
   completed finite scalar extension. The maps use the same actual line,
   ordinary inverse-image, scalar, and total-tensor comparisons. The named
   K-flat/completion comparisons then produce the derived integral equations.
6. Rational and common-stage geometric equations are separate conjuncts of
   `allStageLaws`. Common-stage products are normalized at every larger finite
   coefficient field through `commonLineAtStage` and the recorded
   `commonStageTensorComparison`; they are not arbitrary isomorphisms in the
   common category. Common-stage pullback uses the existing object/arrow
   realization of the canonical finite-stage maps.
7. The single complexes `integralComplex` and `finiteComplex` are the existing
   lines in degree zero. At `r=0` the empty ordered root list gives the
   coefficient-unit map in all generator normalizations. The final conjunct
   of `geometricTateLaws` states both sign equalities for arbitrary `p : ℤ`:
   `(-1)^((2s)p)=1` and `(-1)^((2r)(2s))=1`, using `Int.negOnePow`.

Dependency declarations used (all their full signatures and docstrings were
read in the published source):

- `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical`:
  `FrobeniusCoefficientTwists.positiveLine`, `generator`, `rootTowerMap`,
  `rootSection`, `modulePull`, `moduleSection`, `positiveLineMaps`,
  `finiteModulePull`, `finitePositiveLineMaps`, `finiteDerivedLineMap`,
  `integralDerivedLineMap`, `completedToOrdinaryOnGood`,
  `pullbackAugmentation`, `rationalDerivedLineMap`, `commonDerivedLineMap`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`:
  `sfIntegralTwistingCoefficient`, `sfRationalTwistingCoefficient`, and
  `sfQbarTwistingCoefficient`, including their recorded constructibility.
- `Sheaf.Paper.DerivedPullbackTensorHom`:
  `finiteDerivedPullback`, `finiteIntrinsicDerivedTensor`,
  `constructibleIntegralPullback`, `constructibleIntegralTensor`,
  `rationalDerivedPullback`, `rationalDerivedTensor`,
  `commonStageDerivedPullback`, `commonStageDerivedTensor`,
  `integralPullbackScalarComparison`, `rationalPullbackScalarComparison`,
  `commonStagePullbackComparison`, and `commonStageTensorComparison`.
- `Sheaf.Paper.DerivedPullbackTensorIso` and its imported comparison modules:
  `canonicalFinitePullbackTensor`, `canonicalIntegralPullbackTensor`,
  `canonicalRationalPullbackTensor`, `canonicalCommonStagePullbackTensor`,
  `pullbackTensorQuotient`, and the integral/rational/common composition maps.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`:
  `scalarCompletion`, the normalized ordinary/completed scalar comparisons,
  and their representative and tower constructions.
- `Sheaf.Paper.OrientationIntegralCoefficientTwists`:
  `sfOrientationIntegralLineMaps`, the arbitrary-morphism comparison on the
  actual intrinsic integral line. `Sheaf.Paper.IntegralTwistBaseChange`:
  `twistLineScalarIso`. `Sheaf.Paper.SignedTwistReductionComparison`:
  `signedTwistReduction_comparison`, whose normalized sheaf comparison is used
  for integral reduction instead of choosing an unspecified line isomorphism.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage`:
  `Scheme.proEtaleRootsOfUnityInverseImageMap`.
  `Sheaf.Paper.CartesianCoefficientTwists`: the recorded `spTwists_cartesian`
  supplies the root-transition and coefficient-normalization comparison in
  its condensed presentation. The supplementary module exposes the matching
  normalized maps on the intrinsic degree-zero line realization required by
  the present node; it does not replace the condensed coefficient objects.
- `Sheaf.SixFunctors.SchemeGeometricFrobenius` supplies the recorded
  geometric/scheme-Frobenius convention. `Sheaf.SixFunctors.FrobeniusSquareCartesian`:
  `FiniteFieldDatum.frobenius_square_cartesian`. The underlying
  `FiniteFieldDatum`, `geometricFiber`, `geometricFrobenius`, and
  `sfWeilPrimeInvertible` are those already used by the intrinsic Weil API.
  `Sheaf.Paper.PurityFiniteSetting` fixes the finite coefficient convention;
  the existing coefficient APIs retain its positive quotient indexing.

The remaining ordinary imports are the item's recorded proof dependencies:
root comparison composition and invertibility, local freeness and inverse
image, completed-operation tower substitution and well-definedness,
isomorphism pullback, and shifted tensor morphism calculus. Their role is
spelled out in the main theorem's nine-step natural-language proof.

Edge cases checked: either exponent zero, both exponents zero, positive finite
exponent one, identity finite reduction `m=n`, identity spatial morphism,
empty schemes, arbitrary nonsmooth spatial morphisms, `l=2`, identity coefficient
extension, ramified finite extensions (no equality of uniformizers imposed),
and an algebraic closure in an independent universe. All are included. Only
Frobenius is assumed to be an isomorphism, and that follows from the datum.
For ramified extensions the strict system is the existing functorial reduction
system, allowing larger source exponents; no same-index coefficient map was
substituted. No statement correction or disputed mathematical claim is made.

Searches: the required `msearch.py` LeanFinder search for canonical Tate-arrow
naturality, Loogle search for `Functor.map_comp, NatTrans.naturality`, Mathlib
grep for Tate/Frobenius comparisons, and direct `rg` searches in both
`lean/WeilConjectures` and `lean/Sheaf` found no existing declaration of this
four-stage theorem. The literal item-id search found none. The further
comparison searches are recorded verbatim in the new node's `mathlib_searches`:
LeanSearch and LeanFinder returned ordinary tensor/base-change lemmas, Loogle
reported no `Tate` identifier, and grep found no assembled canonical comparison
family. DAG and `tools/blueprint_refs.py search` searches found related Tate
nodes but no node for this normalized unshifted comparison interface.

Compilation uses only the prescribed `scompile.py`; final compile and delivery
preflight results are recorded below after validation.

## New nodes

`def-pur-canonical-tate-comparisons` defines the missing normalized unshifted
line comparisons on the existing finite, integral, rational, and common-stage
objects. Its source is the canonical Tate factors in the displayed composite
of the current blueprint `def-pur-tate-datum`, through the item's recorded
ancestor `prop-pur-weil-equivariance-compatibilities`. The maps are fixed by
all scalar/root generators, canonical derived counits and augmentations,
localization, and all larger finite coefficient stages. The searches above
and in the JSON found underlying ingredients but no such reusable interface.
The theorem asserting the present naturality/additivity equations remains in
the original item's module; it has not been moved into this definition node.

## Second reading by NZ

I reread the supplied item, current blueprint unit, both modules, and the new
node after drafting; this is a worker self-check, with the maintainer's
independent delivery review still to follow. The finite-field/prime hypotheses
are the original ones. Finite type and separatedness occur only on the models;
no condition is imposed on `w₀`. The four actual coefficient categories and
canonical Frobenius arrows are retained. I checked the domain and codomain of
each of the four displayed equations, especially the inverse `C_w` in the
mixed term. I checked that finite quotient indices cover `m ≥ n ≥ 1` and
include equality, and that strict-system assertions are equalities after the
whole reduction functor. I checked exponent-zero generators and the two even
sign exponents. The added node only supplies missing maps and model
comparisons. During compilation I repaired unconstrained total-tensor site
universes by supplying the actual small-site universes explicitly; this does
not restrict the independent coefficient-closure universe. No mathematical
statement was changed in this reading.

Validation: `scompile.py NZ lem-pur-canonical-tate-arrow-naturality` compiled
both delivered modules separately and cleanly, including their library forms.
The delivery dry run printed `OK (dry run): commit 4e1dda90874 passes the
preflight and compiles; nothing pushed`. Its initial schema error was repaired
by supplying the required empty `import_flags` list on the new definition node;
its citation-format advisories were also repaired. All Lean proofs remain
postponed as required for stage 2.
