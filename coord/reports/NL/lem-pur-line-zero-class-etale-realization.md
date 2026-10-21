## Worker report

This delivery states `lem-pur-line-zero-class-etale-realization` in
`Sheaf.Paper.LineZeroClassEtaleRealization`. Its two postponed theorems are
`WeilConjectures.PurityFiniteSetting.line_zero_geometry` (the geometric paragraph and
its domain facts) and `line_zero_class_etale_realization` (the class, supported site
square, normalized source square, and actual compact-support arrow square). All
other declarations have real data. Each declaration belongs to this node and has
its source/blueprint docstring; the two theorem docstrings contain their proof plans.

Hypotheses and clauses:

* The fixed finite-field/coefficient datum is `P : PurityFiniteSetting.{u}`. Its
  `field`, `coefficients`, `extension`, `finiteExtension`, `level`, and `level_pos`
  are the fixed algebraic closure, prime different from the characteristic,
  finite coefficient subextension, and positive integer of the conventions.
  `P.Ring` is exactly the valuation-ring quotient and `P.Coefficient` is its
  standard `ULift` into the sheaf coefficient universe, not another coefficient.
* `B : Scheme.{u}`, `b : B ⟶ Spec (.of P.field.k)`, `[IsSeparated b]`,
  `[LocallyOfFiniteType b]`, and `[QuasiCompact b]` say precisely separated and
  finite type over k. `V : PurityVectorBundle P B b 1` is the rank-one bundle,
  with its existing total scheme `V.E`, projection `V.p`, relative-Spec
  isomorphism, locally free generator module, and actual `V.zeroSection`.
* `line_zero_geometry` states `IsSeparated V.p`, `LocallyOfFiniteType V.p`,
  `QuasiCompact V.p`, and `SmoothOfRelativeDimension 1 V.p`. It states closedness
  and invertibility of `V.zeroSection.ker`, hence the actual effective Cartier
  divisor, rather than an arbitrary subscheme with the same support.
* `SmoothOfRelativeDimension 0 (V.zeroSection ≫ V.p)` is smoothness of D over B.
  The pointwise `ringKrullDim` equality with `+ (1 : WithBot ℕ∞)` is precisely the
  pure codimension-one convention of the recorded frame/divisor interfaces.
* `lineZeroBaseChange V h` is the literal pullback section with components
  `h ≫ V.zeroSection` and `𝟙 B'`. The geometry theorem quantifies over every
  `B' : Scheme.{u}` and `h : B' ⟶ B`, asserting closedness and invertible kernel
  for that section. It imposes no flatness, finite type or Noetherianity on B'.
  This is base change over B, not pullback by an arbitrary morphism into E.
* The additional geometric domain facts in that helper (absolute finite type
  and separatedness, compactifiability and exact closed pushforward) justify
  the constructions in the remaining paragraphs. They are conclusions from
  the given bundle, never extra hypotheses on the item.
* `P.generalDivisorClass (V.p ≫ b) V.zeroSection (lineZeroIdeal V)` is the existing
  normalized relative divisor class in the supported-Hom realization. The first
  main clause identifies it with `P.agreementCartierMap ...`, the published
  supported Cartier map in its prescribed root chart. No new divisor-class or
  twisting construction is supplied.
* `P.DivisorLocalEquations ...` uses the very same unique normalized etale family.
  Unfolding that recorded predicate gives minus `P.frameBoundary U (e ≫ a) f`
  and minus the one-element frame product for each etale principal presentation.
  In particular this is exactly `-∂κ(t)` on a bundle-coordinate chart. It retains
  the corrected Yoneda sign; it does not use the older positive formula.
* `P.diagonalExponent` is exactly ell^n; `P.diagonalExponent_annihilates` is NA=0,
  and `P.diagonalExponent_isUnit (V.p ≫ b)` is its invertibility on E. The etale
  line is `P.frameTwistEtale T 1`, the existing mu_N tensor A. Its degree-zero
  embedding in `lineZeroEtaleTarget` represents mu_N tensor^L_(Z/N) A canonically:
  the existing finite etale root line is flat. This uses no flatness of A over
  Z/N and includes ramified levels not divisible by the ramification index.
* `lineZeroEtaleMap` is the exact Ext realization of
  `P.agreementCartierEtale ...`, lifted through the full D+ inclusion.
  The explicit `SupportedKummerBoundary ...` clause ensures it is the relative
  ordinary supported Kummer arrow, with its specified frame off the divisor,
  rather than just a class with the same image after forgetting support.
* `lineZeroProMap` is `P.agreementCartierMap ...` in the same published root chart.
  `lineZeroSupportedComparison` is the source comparison uniquely normalized by
  the constant quotient. `lineZeroTwistComparison` is exact comparison followed
  by its canonical single/shift identifications. The root chart is precisely the
  projection-induced twist chart of the dependency `CartierClassAgreement` and
  `def-pur-frame-class`; it does not choose a root or a trivialization. The fourth
  main clause is the explicit supported realization square for these maps.
* `lineZeroProSourceIso` and `lineZeroEtaleSourceIso` are literal composites of
  closed proper/exact comparison, the published compositor, the section equality,
  and the published identity comparison. The fifth main clause says the source
  component of compact-support site comparison respects these specified source
  identifications and the canonical constant-sheaf comparison.
* `lineZeroTau` is the inverse of that pro-etale source identification followed
  by Rpi_! of the actual supported arrow. `lineZeroEtaleTau` is the identical
  construction with the ordinary etale arrow and etale source identification.
  The etale target is Rpi_!^et L_E[2], in D+. `lineZeroTargetWitness` retains this
  precise object and the canonical compact-support/twist comparison isomorphism;
  `lineZeroSourceWitness` retains A_B and its canonical constant comparison.
  The final equality is their commuting arrow square, with the explicit D+/D
  target-compatibility isomorphism. Thus it witnesses this actual map with its
  prescribed endpoints. No clause asserts that tau is an isomorphism.

Dependency declarations used (the listed modules are imported directly or publicly
reexported by a direct dependency):

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `Ring`, `Coefficient`, `constantEtale`, and `constant`.
* `Sheaf.Paper.PurityVectorBundleZeroSection`:
  `AlgebraicGeometry.PurityVectorBundle`, `.zeroSection`, `.zeroSection_spec`.
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` and its reexported
  `FixedFinitePositiveCoefficientTwist`: the existing finite twist presentation,
  `diagonalExponent`, `diagonalExponent_annihilates`, `diagonalExponent_isUnit`.
* `WeilConjectures.AlgebraicGeometry.EffectiveCartier`:
  `Scheme.IdealSheafData.IsInvertible` and the closed-immersion/invertible-kernel
  effective Cartier convention.
* `Sheaf.Paper.PurityDivisorClass`: `generalDivisorEtaleClasses`,
  `generalDivisorClass`, `DivisorLocalEquations`, and the source `divisor_class`.
* `Sheaf.Paper.CartierClassAgreement`: `agreementCartierEtale`,
  `agreementCartierMap`, through the new existing-definition node
  `def-pur-cartier-agreement-maps`. The theorem `cartier_class_agreement` is used
  only by the proof plan and remains in `proof_deps`; its node is not changed.
* `Sheaf.AlgebraicGeometry.CartierKummerMap`: `cartier_kummer_map` and its
  uniquely normalized ordinary/pro-etale families, reexported by the preceding.
* `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`:
  `ordinary_supported_kummer` and its unique relative boundary.
* `Sheaf.Paper.PurityFrameClass`: `frameBoundary` and the one-element
  `frameBoundaryProduct`, through `DivisorLocalEquations`.
* `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary`:
  `AlgebraicGeometry.Etale.SupportedKummerBoundary`.
* `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  the existing exact `comparisonUpperStar.mapDerivedCategoryPlus` realization of
  `siteComparisonDerivedPullbackPlus`; its ambient version is used for the squares.
* `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`, including its retained
  `complex` and `iso`, used twice as actual data, not just a Nonempty predicate.
* `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport` is imported to retain the
  recorded compact-support notion. For compatibility with the comparison and
  origin-composition dependencies, all displayed arrows use its published fixed-
  scalar realization, `ProEtale.rightDerivedLowerShriekOfCompactification`
  and its chosen-compactification `rightDerivedLowerShriek`. These are the same
  Di_! followed by Rg_* candidate, in the module-valued sheaf coordinates used by
  the node's recorded comparison and composition interfaces.
* `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: its compactification
  candidate, bounded-below restriction and inclusion compatibility, for ordinary
  etale compact support.
* `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `originCompositionAmbient`, `originCompactSupportId`, and the full origin class.
* `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparison`, with the exact orientation specified in the DAG.
* The supported-Hom presentation is the recorded `FunctorialCupH` of
  `SupportedCupFunctoriality`, reexported by the divisor and agreement modules;
  it is the supported-cohomology realization of `supported_cohomology_hom`.

The stated proof-dependency modules for vector-projective completion, affine-space
smoothness, ordinary Kummer, finite Tate descent, closed exactness, closed finite
transport, etale compact comparisons and compact-support site coherence are
imported as the stage-3 proof plan. Mathlib-only proof leaves are already available
through these imports. No downstream Thom-class module is imported: its dependency
path goes through projective-bundle formula -> rank-one Thom -> this item.
The source-normalization helpers here use only the already recorded primitive
composition/identity/proper/exact comparisons, so that cycle is avoided.

Edge cases checked before writing: empty B (the dimension clause is vacuous and
all canonical maps remain defined); B=Spec k; polynomial rings over nonreduced
bases (t is still a nonzerodivisor); arbitrary nonflat/non-Noetherian B' (only the
polynomial coefficient argument is used); n=1 and arbitrarily ramified coefficient
extensions (N=ell^n always kills the quotient); and the distinct site object and
morphism universes u+1 and u. No comparison of site universes is imposed.
The D+ target objects are explicit ambient shifts with their bounded-below proofs,
so the ordinary inclusion-shift isomorphism is not mistaken for definitional equality.

Searches for an existing statement:

* `msearch.py ... leanfinder`: "The zero section of a line bundle is an effective
  Cartier divisor and its supported Kummer map has a bounded below etale
  realization after compact direct image". Eight hits: affine-open section
  vanishing/localization results, the etale locus of a ring, and basic-open/germ
  zero tests; none states this supported Kummer or compact-support result.
* `msearch.py ... loogle`: `"Kummer", "zero"`; zero hits.
* `msearch.py ... grep`: `Kummer|zeroSection.*[Cc]artier|[Ee]tale.*[Oo]rigin`,
  Mathlib/AlgebraicGeometry; zero hits.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `line.zero.class|line_zero_class|zeroSection.*[Cc]artier|zero_section.*[Cc]artier`:
  valuation/nonzero-section Cartier lemmas only, not this statement.
* Search for the exact node id under `lean/WeilConjectures`: no declaration.
  Searches of the published purity/Thom modules found the reusable divisor,
  Cartier, frame and compactification interfaces just listed, not this theorem.
  The existing Thom source normalization was inspected and its downstream cycle
  diagnosed before constructing the comparisons from the primitive interfaces.

There is no statement correction, disputed clause, or unusable dependency
interface requiring replacement. The new node records existing definitions only.

## Second reading by NL

This is the sole dispatcher's worker's second pass, not a claim of an independent
second agent (the brief prohibits starting agents). The maintainer supplies the
independent mathematical review. I reopened the node and the full module and
matched the hypotheses and all four paragraphs in the clause audit above.
In particular I checked the universal base change is over B, retained the minus
sign, checked the source comparison is the actual identity-normalized compositor,
and checked the final equation uses the supplied FixedEtaleOriginWitness data
and the actual tau rather than an arbitrary isomorphic arrow. During elaboration,
the opaque shift on the full D+ subcategory required explicit ambient shifted
objects with bounded-below proofs; the underlying complexes and maps did not change.

Validation: `scompile.py NL lem-pur-line-zero-class-etale-realization` compiled the
complete final module in both sandbox and library names, in 44.9 s and 41.0 s,
with no errors or warnings. The D+ objects use explicit result types and the
direct Mathlib single/derived comparison functors; the recorded Cartier maps
remain unchanged. Delivery preflight is run by the prescribed `deliver2.py` wrapper.


## New nodes

`def-pur-cartier-agreement-maps` records the existing definitions
`WeilConjectures.PurityFiniteSetting.agreementCartierEtale` and
`agreementCartierMap` in `Sheaf.Paper.CartierClassAgreement`, with `existing: true`.
Its source is the relative-torsor construction in
`lem-amb-cartier-kummer-map.proof.md` and the explicit c_D normalization paragraph
of `lem-pur-cartier-class-agreement`. The new statement reproduces that paragraph
and introduces its fixed coefficient datum, Cartier immersion and two maps.
The Lean binders are `P`, `{D T}`, `a`, `i`, `[IsClosedImmersion i]`, and `hI`;
no smoothness, finiteness or separatedness is needed to define these maps.
`agreementCartierEtale` splits the positive level as n+1 and selects the etale
component of the unique family from `Etale.cartier_kummer_map` at the two zero-based
indices n. `agreementCartierMap` applies `functorialCupCompare i 2 1` to its Ext hom.
This gives exactly the specified constant-quotient source normalization and
root-projection target chart. The new node asserts no agreement theorem.

Searches made for this repair: logged `msearch.py leansearch` query
"The normalized supported Cartier Kummer morphism is the relative Kummer boundary
with derived scalar extension and etale to proetale comparison" returned eight
scheme-normalization declarations, none about Kummer maps. Logged `loogle` query
`"Kummer", "Sheaf"` and Mathlib/AlgebraicGeometry `grep` query
`agreementCartier|CartierEtaleKummer|SupportedKummerBoundary` returned no hits.
`rg` for the two declaration names in `lean/WeilConjectures`, `lean/Sheaf` and
`dag/nodes` found precisely the definitions in CartierClassAgreement and their
auxiliary listing under the agreement theorem. No independent definition node
owns these specialized maps. `blueprint_refs.py search 'Cartier Kummer'` found
zero blueprint nodes; the broader `Cartier` search found 47, including the
upstream general family but no definition of these two specializations. The
related CartierKummerData, geoCartierEtaleClass, GeoCartierClass and
OrdinarySupportedKummerSystem node statements were read: they describe general
families or different interfaces, not these finite-datum comparison definitions.
The new node therefore reuses the existing declarations without another module.

## Repair of return L (immutable head e1133fdd92a4)

H2 repaired: the saved packet differed from the current base only in `lean` and
an added `lem-pur-cartier-class-agreement` statement dependency. That theorem is
removed from `stmt_deps`; the new definition node above is its sole addition to
the base's 15 statement dependencies. The agreement theorem stays in
`proof_deps`. The item's natural-language statement, proof and proof dependencies
are unchanged. The item's Lean module is byte-identical to the saved packet and
the returned delivery; the unused SfIntrinsicCompactSupport import was advisory
and is retained to avoid reopening the reviewed Lean content.

Repair self-reading by NL: reopened both existing definitions and their bodies,
`functorialCupCompare` and its source-normalization theorem, the unique-family
statement `Etale.cartier_kummer_map`, the c_D normalization paragraph, and the
blueprint relative-torsor construction. The choice is from the unique Cartier
family, never from `cartier_class_agreement`; equality with `generalDivisorClass`
is still the item's first assertion. The new node's signature is verbatim from
the existing `agreementCartierMap` declaration, and both definitions are listed.
The finite coefficient level is positive, includes n=1 and ramified levels,
and the definitions also apply to empty T or D. No new universes or hypotheses
are imposed. This is the required author self-check; independent review remains
with the maintainer, as required by the dispatcher brief.
