## Worker report

The delivery states `AlgebraicGeometry.LineKummerField.line_kummer_field_realization`
in `Sheaf.Paper.LineKummerFieldRealization`. Its proof is `sorry`; all helper definitions
have real data. The original node and dependencies are unchanged except for its Lean record.
The helper predicates organize clauses of this very statement, rather than introduce
independent mathematical notions or alternate definitions of twists or functors.

Hypotheses and clauses, with the node and complete Lean module read together:

- Any field K₀: `(K₀ : Type u) [Field K₀]`, with `_hl : IsUnit (l : K₀)`.
  There is no algebraic-closedness or finite-type-over-a-smaller-field hypothesis.
- Prime and finite coefficient extension: section binders `(l : ℕ) [Fact l.Prime]`,
  `(F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]`.
  Index `n : ℕ` denotes exponent `n+1`, so every positive exponent is included.
  `finiteTateCoefficient l F n` is precisely the ordinary ULift of the recorded quotient
  `Padic.coefficientExtensionRing l F (n+1)`, with its recorded uniformizer, not a new ring.
- `∃ hA : ((l^(n+1) : ℕ) : finiteTateCoefficient l F n) = 0` asserts NA=0.
- Every K₀-scheme T is quantified with `T.Over (Spec (.of K₀))`.
  `etaleLine` is the degree-zero ordinary root tensor `finiteEtaleTateLine`.
  The final clause of `CoefficientRealization` gives its derived scalar-unit universal
  property from the lifted Z/N root line, normalized on all pure root tensors.
  This is the identification with derived tensor, without flatness of A over Z/N.
- `CoefficientRealization` gives `IsLocallyConstantSheaf` and an etale cover with
  actual module isomorphisms to the constant free A-line. Since the quotient is finite,
  these local bases also give finite stalks. It includes empty T and empty covering families.
- `q` is an actual site-comparison isomorphism to `finiteTateProSheaf ... 1`, the
  constant-scalar realization of the prescribed twist. `IsFiniteTateSiteComparison`
  fixes it by the inverse-limit root projection on every pure tensor, excluding rescaling.
  `AlphaPullback` gives the exact scheme/site square with normalized etale and pro-etale
  root maps, for every morphism, including identity maps and isomorphisms.
- `intrinsicLine` is the same prescribed `finiteCoefficientTwist ... 1` in the existing
  intrinsic constant-ring encoding. `HasProEtaleTorAmplitude ... (-2) (-2)` applies to
  its shift by 2 on every T, with all unbounded K-flat tests from the recorded predicate.
- B carries its scheme-over-field structure, locally finite type, quasi-compact and
  separated structure morphism. `∃ hB : IsNoetherian B` supplies the consequence needed
  to type the recorded vector bundle construction; Noetherianity is a conclusion.
  V ranges over all `B.Modules` with `IsFiniteLocallyFreeOfRank 1`.
- X, π, z in the theorem are exactly `VectorBundleZeroSection.scheme`, `.π`, `.zero`.
  `zeroClosed` reuses the published closed-immersion proof, and `hz` the published
  zero-section identity. `BundleRealization` asserts π separated, locally finite type,
  quasi-compact, and every frame's affine-space chart is an isomorphism over its open,
  carrying z to the origin. Rank one is `ULift (Fin 1)`; over affine opens this is R[t].
- `∃ hI : z.ker.IsInvertible` is the effective Cartier condition for the closed section.
  `hX` supplies the deduced invertibility needed by the prescribed Kummer interface.
- `etaleClass` is the actual arrow of the boundary-normalized ordinary family selected
  in `cartier_kummer_map`; `proClass` is the arrow in its prescribed pro-etale family,
  the same as `cartierKummerMap`. `extPlusMap` transports their Ext realization into D⁺
  through the fully faithful inclusion, retaining the actual arrow and the shift.
- `PairRealization` states exactness of both closed direct images and the equation
  `ν.map cᵉ ≫ alpha[2].hom = compareSupported ≫ cᵖ`. Closed direct image is already
  left exact; preservation of finite colimits is its exactness, equivalently Rz_*=z_*
  under the canonical exact-derived comparison of the recorded dependency.
- On X, `finiteTorConstructible ... (intrinsicLine[2])` asserts bounded constructibility
  and finite Tor amplitude with the original recorded intrinsic predicates.
- For every Cartesian presentation of base change, `BundleRealization` quantifies B',
  X', g, v, π', z' and both Cartesian squares. It concludes the Cartier condition,
  exactness on both sites, normalized site realization, its alpha pullback square,
  and `PairPullback`. The latter writes both actual D⁺ arrow equations with the
  canonical `etaleBeta` / `proBeta` supported mates and root-normalized target maps.
  No Noetherianity, flatness, finite type or separatedness is required on B' or g.
  Closedness of z' is supplied with the Cartesian presentation, as is automatic for
  a base change of z. The final quantifier covers every isomorphism of Cartier pairs.
- Every compactification c is allowed. `etaleTau` is `etaleSource.hom ≫ Rπ!.map cᵉ`;
  `proTau` is `proSource ≫ Rπ!.map cᵖ`, with the published normalized source maps.
  `CompactRealization` says proSource is invertible and writes the exact equation
  `proTau ≫ compactTarget.hom = compareConstant.inv ≫ ν.map etaleTau`.
  `compactTarget` is Rπ! of inverse alpha[2] followed by the inverse canonical
  `compactSupportSiteComparisonPlus`. Thus its direction is exactly Tπ in the node.
  The explicit `compareConstant.inv` is the scalar-preserving identification of the
  two A_B objects; it represents identity on A_B, with no arbitrary source automorphism.
- Applying the theorem anew with K₀=Ω supplies its geometric-field specialization.
  The final base-change clauses concern supported arrows only and introduce no compact
  exchange along g and no supported/compact cohomology identification.

Dependency declarations read and used (the recorded modules are available transitively):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the actual coefficient quotient definitions.
- `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`: `scheme`, `π`, `zero`, `zero_spec`,
  `Trivialization`, `trivializationMap`, `zeroRestricted` in its recorded namespace.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the ordinary derived module
  categories; `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: fixed-scalar/intrinsic
  presentation; `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus` (its body is the exact mapDerivedCategoryPlus used here).
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` and its public coefficient-twist
  dependency: `finiteCoefficientTwist`; its constant restriction `finiteTateProSheaf`.
- `Sheaf.Paper.AmbTateRootProjectionReduction`: root-projection reduction and prescribed
  normalization; `IsFiniteTateSiteComparison` in `Sheaf.Paper.FiniteTateSiteDescent` is
  its published fixed-scalar pure-root normalization used to specify alpha.
- `Sheaf.Paper.FiniteTorAmplitudeSites` and `IntrinsicFiniteTorsionConstructibility`:
  `WeilConjectures.finiteTorConstructible`, using `intrinsicFiniteTorsionConstructible`
  and `HasProEtaleTorAmplitude` in its original intrinsic ringed-site categories.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`: `ordinary_supported_kummer`;
  `Sheaf.AlgebraicGeometry.CartierKummerMap`: `cartier_kummer_map`, `cartierKummerMap`.
  Their shared unique ordinary boundary fixes exactly the ordinary class used here.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification`;
  `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` and the finite pro-etale
  operations imported by `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport` supply Rπ!.
- `Sheaf.Paper.SectionCompactSourceExchange`: `etaleSource`, `proSource`, `compareConstant`,
  `compareSupported`, `etaleBeta`, `proBeta`. Its `composition_normalization` identifies
  the pro-source with the canonical compositor of
  `Sheaf.Paper.CanonicalOriginCompactSupportComposition` and finite compact-site coherence.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparisonPlus` fixes the actual compact target comparison.

Proof dependency imports are retained for stage 3: vector projective completion,
finite-etale twist lines, flat-single derived normalization, finite-root site comparison,
etale supported kernel adjunction, exact functor derived functor. The closed-exact input
uses the already imported `FiniteCoefficient.UpperLowerStar.ClosedImmersion` interface;
its legacy non-finite path would duplicate declarations and is deliberately not imported.

Edge cases checked: n=0 here is coefficient exponent 1; arbitrary ramification including
exponent less than ramification index; l=2; empty schemes; nonreduced and non-Noetherian
pullback bases; identity morphisms; pair isomorphisms and fibre frames; arbitrary fields
including a geometric field not finite type over an original field. The polynomial
variable remains a nonzerodivisor even over a ring with nilpotents. Universes are explicit
and autoImplicit is disabled. A common u accommodates arbitrary fields and schemes;
site object and morphism universes remain u+1 and u respectively.

Searches performed with the prescribed msearch.py wrapper:

- LeanFinder: “Line bundle zero section supported Kummer class etale proetale field
  realization compact support normalization”: eight unrelated section/etale-locus hits,
  no exact statement.
- Loogle: `AlgebraicGeometry.Etale.cartierKummerMap,
  AlgebraicGeometry.ProEtale.compactSupportSiteComparison`: zero hits, project name
  unknown to its Mathlib index. Project source search located both recorded interfaces.
- grep: `Kummer|compactSupportSiteComparison`, Mathlib AlgebraicGeometry: zero hits.
- LeanSearch: “supported Kummer line bundle etale proetale compact support”: eight hits
  about topological compact support, unramified loci and the etale pretopology; no match.
- rg in both project roots for `line.*[Kk]ummer|[Kk]ummer.*[Ll]ine`, plus exact node-id
  search in WeilConjectures: local affine-line calculations and framed divisor realization
  are present, but no arbitrary-field line-bundle combined statement with normalized
  compact arrow. The existing maps and predicates identified by those searches are reused.

Validation: required scompile.py clean in sandbox (46.8 s) and module (45.8 s),
no warnings. Earlier typed D⁺ conversion duplicated kernel work; factoring its generic
Ext realization into `extPlusMap` removed that cost without changing the statement.
No statement correction, dependency repair, new DAG node, or disputed assertion.

## Second reading by NU

I reread the original node and the final file clause by clause after the clean compile.
This is a second pass by the same worker: the dispatcher explicitly prohibits starting
other agents, and the maintainer performs the independent delivery review.

I checked positive quotient and root exponents together, arbitrary field hypotheses,
every-scheme coefficient realization, pure-root normalization, the intrinsic Tor window
[-2,-2], constructibility on the actual total space, and use of the published bundle.
I checked that Cartier and exactness are conclusions, that primed schemes carry no
Noetherianity or flatness assumption, and that both supported pullback equations use
the actual canonical mates. I checked target-comparison direction and composition order:
Rπ! inverse alpha followed by inverse site comparison, with compareConstant inverse on
the source. The etale source is already an isomorphism; proSource invertibility is asserted.
The field Ω case is a new application of the theorem, not restricted to old finite-type
base change. I added the over-open chart equation and the alpha pullback square during
this pass; neither is silently omitted. No mathematical mismatch remains identified.
