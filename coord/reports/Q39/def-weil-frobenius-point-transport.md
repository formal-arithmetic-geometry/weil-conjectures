## Worker report

`Sheaf.SixFunctors.FrobeniusPointTransport` constructs the point transport in all
four coefficient realizations. The saved packet's arbitrary
`FrobeniusPointTransportData` record has been replaced: accepting an arbitrary
scheme automorphism, fibre functor, inverse image, comparison and section transport
did not define the maps in this node. The first required dry run also found that
its node record lacked `lean.file`; that record is repaired.

The construction follows the node without a statement change:

- The finite-field tuple is `D : FiniteFieldDatum`. The prime is `l` with
  `[Fact l.Prime]` and `hl : l ≠ D.p`. The coefficient extension has `[Field E]`,
  `[Algebra ℚ_[l] E]` and `[FiniteDimensional ℚ_[l] E]`. For the fourth case the
  fixed closure is `Ω` with `[IsAlgClosure ℚ_[l] Ω]`; its finite subfields are
  `Padic.FiniteCoefficientFields l Ω`, with the existing Shrink coefficient model.
  The constructions for E are independent of an embedding into Ω, exactly as the
  recorded coefficient categories are; the fourth case specializes E to the actual
  finite subfield models in Ω. No embedding is chosen or changed.
- The positive finite exponent is `n + 1`, with
  `Nat.succ_le_succ (Nat.zero_le n)`. This covers every n ≥ 1 in the text; the Lean
  parameter 0 is the first positive level. No level-zero coefficient ring is used.
- `s` is always `Spec (.of D.k)`. `frobeniusPointIso` is `Spec.mapIso` of the
  recorded geometric field Frobenius, the inverse of the arithmetic Frobenius.
  Its inverse is therefore Spec of the inverse field automorphism.
- The actual site is `Scheme.ProEt` with `ProEt.topology`. Its final object is
  `ProEt.mk (𝟙 (Spec (.of D.k)))`. `frobeniusPointRestriction` is the morphism
  from its postcomposition by g_s to this final object, with underlying map g_s.
- Inverse image is `inverseImageFiniteModules` or `inverseImageIntegralModules`
  from the comparison dependency. Those are the recorded canonical sectionwise
  models of the sheafified comma-colimit inverse image. The dependency's
  `proEtaleIsoInverseImageIdentification` identifies a comma coprojection followed by
  sheafification with the section itself at the distinguished comma index. Thus
  the node's `ins ∘ res` is precisely restriction along
  `frobeniusPointRestriction` in this model, not an unspecified map.
- The two `frobeniusPoint*Sigma_existsUnique` statements prescribe **every** term
  and **every** element of sigma by this restriction formula. Their chosen chain
  maps therefore have uniquely determined data. The source and target module
  objects come from `pointFiniteSections` and `pointIntegralSections`, which
  restrict scalars along the actual constant-section maps. The inverse-image
  action is through c inverse, as defined in the comparison dependency. Their
  named well-definedness theorems have complete proof docstrings and `sorry`;
  no map or proof inside a definition is `sorry`.
- `frobeniusPointTransportFiniteComplex` composes the class of sigma with
  sections of `inverseImagePullbackComparisonFiniteIntrinsic`. That dependency
  is exactly the sheafified x tensor 1 map and has target the recorded
  `finiteDerivedPullback`. Localization's canonical factor isomorphisms identify
  termwise sections with derived sections. `frobeniusPointTransportFinite`
  evaluates on an arbitrary derived object using the localization's chosen
  complex representative and its specified isomorphism. The constructible
  component is `frobeniusPointTransportFiniteConstructible`.
- `frobeniusPointTransportIntegralComplex` uses exactly
  `inverseImagePullbackComparison` with its good K-flat flat-term representative
  `P` and quasi-isomorphism `q`. That dependency constructs the compatible finite
  reduction maps, their product and the zero-homotopy mapping-cocone lift into
  the recorded strict Roos complex, followed by inversion of inverse-image(q).
  It is not completed tensor extension. The named
  `frobeniusPointTransportIntegral_existsUnique` fixes the arrow by this explicit
  formula on every representing complex and resolution; it chooses a uniquely
  determined arrow, not arbitrary comparison data or a nonunique representative.
  Its docstring explains common-refinement independence. This auxiliary
  well-definedness statement does not assert naturality of a family. The
  constructible component is `frobeniusPointTransportIntegralConstructible`.
- `frobeniusPointFinitePullback` restricts the actual finite pullback using
  `isomorphismFiniteDerivedPullback_termwise`. `frobeniusPointIntegralPullback`
  uses `constructibleIntegralPullback`, the recorded restriction of the completed
  pullback. Thus the targets of the constructible components really are
  `Fib_s(Lg_s^* N)` in their recorded finite and integral point categories.
  The named prime-unit statements derive the stalk and residue-field units from
  the finite-field datum and l ≠ p, rather than imposing additional assumptions.
- `frobeniusPointRationalPullbackObj` is the same integral pullback object in raw
  rationalization. `frobeniusPointTransportRational` applies the exact recorded
  tensor functor for `pointIntegralToField l E` to the integral arrow. Its only
  other maps are `pointFibreSizeDescent` and `pointRationalFibreObjIso`: these are
  exactly the existing point-fibre coefficient-size and object identifications.
  Its source and target use the actual `pointRationalFibre`.
- `frobeniusPointQbarPullbackObj` retains `N.stage` and uses that rational pullback
  object. `frobeniusPointTransportQbar` represents the rational transport at
  **that same stage**, using `pointFdQbarStage` and the recorded Shrink algebra
  equivalence, with source and target the actual `pointQbarFibreObj`.
- No natural-transformation structure or invertibility of transport is part of
  these definitions. Those remain the separate downstream nodes identified in
  the text. The auxiliary uniqueness statements only make the component data
  well defined.

Dependencies read and used (module, declarations):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: its recorded convention is the
  existing `FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`; `Spec.mapIso`
  specializes that same field automorphism directly to s, rather than using the
  isomorphic chosen base-change scheme `D.geometricFiber`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.mk`,
  `ProEt.forget`, `ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  as used by the recorded canonical inverse-image comparison.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleSheafInverseImage`, `proEtaleInverseImageIndex`, and the
  constant coefficient maps, through the comparison dependency.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`; the completed coefficient sheaf and
  its projections are those used in the integral comparison and sections functors.
- `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`:
  `inverseImageFiniteModules`, `inverseImageIntegralModules`,
  `inverseImagePullbackComparisonFiniteIntrinsic`, `inverseImagePullbackComparison`.
  Its imported `IsoSectionwiseInverseImage` gives the canonical sectionwise model
  and its module action transported through the inverse coefficient map.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`,
  `constructibleIntegralPullback`; the rational and common-stage operations have
  the same integral object formulas as the explicit object definitions here.
- `Sheaf.Paper.PointProEtaleSectionsExact`: `point_proEtale_sections_exact`,
  `pointModuleSections`, through the exact sections and point-fibre interfaces.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFiniteFibre`, `pointIntegralFibre`,
  `pointFibreIntegralAmbient`, `pointRationalFibre`, `pointRationalFibreObjIso`,
  `pointFibreSizeDescent`, `pointQbarFibreObj`; its imports give
  `pointFiniteSections`, `pointIntegralSections`, `pointIntegralToField`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory` and its actual stage objects.
- `Sheaf.Paper.PointFdQbarCategory`: `DerivedCategory.PointFdQbar`,
  `pointFdQbarStage`, the common-stage target realization.
- `Sheaf.Paper.IsomorphismDerivedPullback`:
  `isomorphismFiniteDerivedPullback_termwise`; the integral constructibility
  restriction is supplied by `constructibleIntegralPullback`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `DerivedCategory.Q`; `ExactFunctor` supplies `mapDerivedCategoryFactors`.

Edge cases checked: the first positive exponent is included; zero complexes and
zero morphisms use the same restriction and tensor formulas; no l = p case is
silently admitted; the algebraic closure k need not be a particular chosen model;
finite-stage field repetitions and identity extensions do not change the stage
in the fourth construction; and the integral map uses the ambient completed
pullback even before restricting to derived-complete constructible objects. The
site retains object universe u+1 and morphism universe u. Section-module carriers
live in u+1, with the existing coefficient ULift and fibre size-descent conventions.

Sources read: the node and all statement-dependency records; the corresponding
source signatures and docstrings; the current blueprint's global-geometric-
Frobenius unit; Deligne's PDF pp. 150--151, including (1.1.3) on rationalization
and finite-stage passage, and (1.1.7) on geometric Frobenius and transport of
structure. No statement correction, new node, or dependency repair is needed.

Searches retained from the previous packet:

- `msearch.py ... leanfinder "point transport along geometric Frobenius of Spec k"`:
  eight unrelated Frobenius/spec-point hits, no transport construction.
- `msearch.py ... loogle "NatTrans, DerivedCategory, proEtaleSheafInverseImage,
  geometricFrobenius"`: unknown identifier `NatTrans`, no match.
- `msearch.py ... grep "Frobenius.*point.*transport|point.*transport.*Frobenius" Mathlib`:
  no matches.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` for Frobenius transport,
  `sigma_N`, and `iota_N`: no existing declaration.

Current-source self-check searches:

- `msearch.py ... leanfinder "canonical point transport along geometric Frobenius
  on the pro-etale derived category"`: eight unrelated etale/isocrystal hits;
  no transport construction.
- `rg` in both the source project's `WeilConjectures/` and the shared
  `lean/Sheaf/` for `frobeniusPointTransport`, `FrobeniusPointTransportData`, and
  the node id: no existing declarations.

## Second reading by Q39

The replacement worker read the saved packet against the node and current
comparison/fibre modules. The previous record substituted arbitrary categories,
functors, a scheme automorphism and component maps, and strengthened the node by
requiring a natural transformation; none of those fields specified the canonical
restriction, comma coprojection, finite comparison, integral derived-limit map,
rational tensor or same-stage algebraic-closure arrow. Those mismatches were
removed by the explicit constructions above. The missing `lean.file` was repaired.

A second pass over the new module checked the finite positive-level indexing,
Spec of geometric rather than arithmetic Frobenius, restriction-arrow direction,
the c inverse module action, both localization factor directions, the integral
resolution map's target, the actual constructible full subcategories, scalar
extension after integral transport, and preservation of the exact coefficient
stage in Qbar. All helper signatures bind their variables and universe explicitly
or use the explicit section-variable declarations. Each postponed helper is a
named well-definedness statement of this definition with its full proof in its
docstring; definitions have real data and no arbitrary-map parameter. Naturality
and invertibility remain separate. This is the replacement worker's reading;
no additional agent was launched, as the dispatch brief requires.

A corrected Loogle query `CategoryTheory.NatTrans, CategoryTheory.Functor` returned
12 generic natural-transformation declarations and no canonical point transport.

During compilation, projection syntax and omitted section hypotheses in the
prime-unit helper signatures were repaired. Both primality and l ≠ p are now
explicit in those signatures. The two sigma/comparison composites insert the
canonical inverse-image localization factor before kappa. In the rational case,
the source and target of the arrow before size descent are explicitly named by
`pointFibreRationalLarge`, so elaboration need not recover objects through the
chosen inverse equivalence. These are implementation repairs to the stated
canonical maps; the node statement is unchanged.

Explicit return types for sigma and integral transport keep Lean from expanding
their uniqueness specifications into inferred signatures. The Shrink algebra
equivalence at the last stage also has an explicit coefficient type. These retain
the same mathematical objects and maps and reduce repeated elaboration.

Additional searches for the sigma ingredient: LeanFinder query “Frobenius
restriction map on pro-etale global sections before derived pullback” returned
eight unrelated etale algebra/site declarations. Loogle query
`CategoryTheory.Functor.mapHomologicalComplex` returned the generic prolongation
functor and its twelve related declarations. Mathlib grep
`Frobenius.*[Ss]ection|[Ss]ection.*Frobenius` found only section headings in
unrelated algebra files. `blueprint_refs.py search "Frobenius point section"`
found no separate blueprint node. These introduce no additional notion: the
sigma helpers remain in the owning point-transport module.

The final file compiled without errors or warnings in both server passes.
The first preflight required the recorded signature to end before the assignment
token; `lean.statement` now uses that exact signature boundary.


### Independent maintainer landing review, 2026-10-18

Read the immutable delivery at a7941457037d562b2cdaf4f222e43fffb10e71a9
against its node, all 17 statement dependencies, the actual side-library APIs,
and Deligne (1.1.7), printed pp. 150–151. Checked all four coefficient cases,
the restriction direction, comma/sheafification identification, c inverse action,
localization comparisons, integral resolution/Roos formula, raw rationalization,
same-stage Qbar realization, constructibility, universes and edge cases. No
mathematical or statement mismatch was found. The recorded final signature is
verbatim and all 22 declaration names match. The five postponed proofs remain
named theorems with only sorry bodies and proof docstrings.

Fresh scompile reproduction found H10: the original library-file pass and its
server confirmation exceeded 60 seconds. Profiling located repeated kernel
checking in the conversions from exists-unique to plain existence. The complete
replacement changes exactly three expressions: finite sigma, integral sigma,
and integral transport choose directly with Classical.choose from the same
exists-unique theorems, rather than first applying .exists. Their specifications
and uniqueness are unchanged. No declaration, hypothesis, signature, source
construction, resource limit or linter setting changes. Temporary profiling and
an ineffective transparency-setting trial were removed.

Validation of the complete corrected module:
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q39 def-weil-frobenius-point-transport fixes/lean/Sheaf/SixFunctors/FrobeniusPointTransport.lean

The installed wrapper compiled against its persistent side overlay: sandbox
44.4 s, library file 44.8 s, exit 0, no errors or warnings. No global build,
project-clone edit, branch-head change or live Lean write was performed.
The independent review record is review.md in the immutable review directory.
