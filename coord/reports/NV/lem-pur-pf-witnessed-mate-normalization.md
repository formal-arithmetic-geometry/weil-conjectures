## Worker report

The module `Sheaf.Paper.PurityWitnessedMateNormalization` states
`AlgebraicGeometry.ProEtale.purityWitnessedMateNormalization`, with `sorry` as its
only theorem proof. The item's natural-language statement, dependencies, and accepted
four-step proof are unchanged. Definitions contain the actual canonical composites.

Source read: `literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`,
the compactification-independence sentence, and the complete accepted four-step
finite-site normalization proof in this item's node. The source's compatibility
with counits and extension by zero is rendered using the specified maps, rather
than unspecified isomorphisms between their endpoints.

Hypotheses and clauses, in order:

- `P : PurityFiniteSetting.{u}` retains the finite-field datum, prime different
  from the characteristic, actual finite extension in the coefficient closure,
  and positive level. `P.Coefficient` is the standard ULift of the existing
  quotient `O_E/(varpi_E^n)`. `purityNormalizationCoefficientFinite` derives
  finiteness from `Padic.finite_coefficientExtensionRing` and `P.level_pos`;
  no finiteness or Kummer-divisibility assumption is added.
- `X.Over` and `Y.Over (Spec (.of P.field.k))` are the k-schemes. Their
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` structure-map
  instances say separated finite type, exactly as in the item.
- `f : X ⟶ Y`, `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, and
  `QuasiCompact f` say that f is a separated finite-type k-morphism.
- `c₁ c₂ : Compactification f` retain the schemes, open immersions, proper
  maps, and factorizations. `v : c₁.Refinement c₂` retains `v.hom`,
  `v.i_hom : c₁.i ≫ v.hom = c₂.i`, and `v.hom_g`. Properness is the
  existing refinement instance; no cartesian condition is imposed.
- The categories are `DerivedCategory` of `Sheaf (Scheme.ProEt.topology X)
  (ModuleCat.{u+1} P.Coefficient)`, the ordinary uncompleted fixed-scalar
  module categories. `ProperOpenShriek` is the exact degreewise extension
  by zero and `ProperOpenPush` is the ordinary total right derived image.
  The intrinsic extension-by-zero dependency is imported and its fixed-scalar
  realization is the existing upstream `openImmersionLowerShriek`.
- `M : DerivedCategory.Plus ...` supplies bounded below M. The retained
  `w : X.FixedEtaleOriginWitness P.Coefficient M` supplies H as `w.complex`
  and the actual a as `w.iso`. Its type is exactly
  `comparisonUpperStar.mapDerivedCategory.obj H.obj ≅ M.obj`.
- `refinementProperOpenIsoFixed P.Coefficient v M w` is Gamma: first
  `J₂.mapIso w.iso.symm`, then the specified `properOpenProEtaleIso` at H,
  then `Rv_*.mapIso (J₁.mapIso w.iso)`. This is the part (a) formula,
  written in Lean's left-to-right composition order.
- `purityRefinementMate` uses exactly `properOpenMate` from the recorded
  projection-mate node. Its definition is beta, identity/zero projection
  onto `(j₁,1_X)`, canonical compositors, and the proper-adjunction mate.
  The left identity direct image is identified by the conjugate of
  `leftDerivedUpperStarId`, so the resulting transformation has source J₂.
  Both required `QuasiCompact cᵢ.i` instances are derived inside the definition
  by `cᵢ.quasiCompact_openImmersion`; no new hypothesis is imposed.
- The first conjunct is equality of the actual Gamma hom and this mate at
  `M.obj`, rather than an existence or equality of their isomorphism classes.
- `purityEtaleRefinementComparison` evaluates the existing resolution-normalized
  `Etale.ClopenMateNormalization.normalizedComparison` for the square
  `(j₁,j₂,1,v)`, inserting `Etale.lowerStarIdDerivedPlus.inv` on its source.
  This is the gamma^e specified by the interchange-coherence dependency.
- `purityRefinementSiteWordPlus` is exactly `e₂.inv ≫ nu*(gamma^e) ≫ b_v ≫
  Rv_*(e₁.hom)`, using `properOpenSiteExtensionIso` and the canonical
  `fixedComparisonDirectImageMatePlus`. `purityRefinementSiteWord` includes
  that word in D, inserting the same canonical D-plus compatibility maps
  used in `properOpenProEtaleIso`. The second conjunct is precisely the
  explicit four-factor identity on `nu_X^*H`, in the unbounded category.
- The last conjunct quantifies over another bounded-below M', any retained
  witness w', and every ambient derived arrow `t : M.obj ⟶ M'.obj`. It says
  `Gamma_M ≫ Rv_*J₁(t) = J₂(t) ≫ Gamma_M'`. Witness morphisms are not
  required; this is the category with all underlying arrows, as in the source.
- Every witnessed bounded-below tensor input is an admissible value of M
  in this same theorem, with its own w. Thus the tensor-input clause is
  retained without a claim that arbitrary tensor products preserve D-plus
  or etale origin. There is no constructibility or Tor-amplitude assumption.

Dependency declarations read and used (all full names are in the indicated namespaces):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Ring`, `.Coefficient`, and their existing ring instances.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement`, its fields, and properness.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicExtensionByZero`, defined through the canonical fixed-scalar
  realization and upstream `ProEtale.openImmersionLowerShriek`.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `Scheme.FixedEtaleOriginWitness`, `.complex`, `.iso`.
- `Sheaf.Paper.RefinementComparisonIsomorphism`: the existing
  `ProEtale.refinementProperOpenIso`, `refinementComparisonAtWitness`,
  `refinementComparisonIsomorphism`, and the fixed coefficient realization;
  reexported by the dependency module below.
- `Sheaf.Paper.ProEtaleProperOpenComparison`:
  `ProEtale.properOpenProEtaleIso`, `.properOpenProEtaleIsoPlus`, and
  `.properOpenSiteExtensionIso`.
- `Sheaf.SixFunctors.ProperOpenProjectionMate`:
  `ProEtale.ProperOpenDerived`, `ProperOpenShriek`, `ProperOpenPush`,
  `properOpenAlpha`, and `properOpenMate`.
- `Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization`:
  `ProEtale.properOpenComparison_site_normalization` (proof dependency API).
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`:
  `Etale.properOpenInterchangeCoherence`; its canonically normalized comparison
  is exposed by `Etale.ClopenMateNormalization.normalizedComparison` in
  `Sheaf.AlgebraicGeometry.EtaleClopenMateNormalization`.
- Plain proof imports: `Sheaf.AlgebraicGeometry.FiniteClopenMateSiteTransport`
  (`ProEtale.finiteClopenMateSiteTransport`) and
  `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`
  (`ProEtale.fixedComparisonDirectImageMatePlus` and its counit equation).

Edge cases checked before writing: identity refinement uses the canonical identity
comparison, not definitional equality of derived functors; empty X allows the empty
clopen section and zero extensions; zero complexes and arbitrary shifts are admitted;
positive level 1 and ramified coefficient extensions need no divisibility by the
ramification index. Noncartesian refinements are admitted. Universes retain scheme
universe u, site object universe u+1, site morphism universe u, and coefficient/module
universe u+1. The witness keeps both antecedent and isomorphism, including a different
witness of the same M. No node fault or disputed statement was found.

Searches actually run with `msearch.py NV lem-pur-pf-witnessed-mate-normalization`:

- LeanFinder: `proper open comparison at an etale origin witness equals the clopen projection adjunction mate`.
  Eight hits, including locally constant adjunction triangles, topological open
  adjunctions, an etale pair hom equivalence, and clopens of a spectrum; no match.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.NatTrans`: zero hits.
- LeanSearch: `proper open comparison for etale origin complexes agrees with its normalized adjunction mate`.
  Eight hits: topological open adjunctions, comonadic comparison adjunction,
  and Dold-Kan comparison; no match to these specified derived maps.
- Mathlib grep: `proper.?open|clopen.*mate|refinement.*comparison` in
  AlgebraicGeometry: zero hits.
- Project rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `witnessed.*[Mm]ate|properOpenMate|witnessedMateNormalization` located the
  existing generic mate and its product/tensor consumers, but no witnessed
  normalization theorem. Upstream node-id grep found no declaration.
- Declaration-name and upstream-index rg found no collisions for the delivered
  names. Reading the original refinement module showed the missing fixed-scalar
  witness interface; this is repaired without duplicating its ringed construction.

## Dependency modules

`def-sf-refinement-comparison-isomorphism`: the existing
`refinementProperOpenIso` takes `EtaleOriginDerivedCategory`, whose underlying
object is in the continuous-coefficient ringed presentation and is then sent back
by `refinementFixedObject`. The separately recorded `FixedEtaleOriginWitness`
retains an ordinary fixed-scalar D-plus object, so it cannot be passed directly to
that declaration. `Sheaf.Paper.RefinementComparisonFixedWitness` publicly reexports
the entire original module (including part (b)) and adds
`AlgebraicGeometry.ProEtale.refinementProperOpenIsoFixed`. Its data is exactly the
same three-isomorphism transport formula at M, H, and a, directly in the recorded
fixed-scalar witness interface. The original construction is not replaced or copied;
only this coordinate evaluation is supplied. The dependency node changes only `lean`,
with `lean.note` recording the mismatch and repair. No arbitrary map, antecedent
choice, new coefficient equivalence, or mathematical hypothesis is introduced.

Validation uses `scompile.py` for both files separately in dependency order, against
the live published library. The delivery dry run and final delivery use `deliver2.py`.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
