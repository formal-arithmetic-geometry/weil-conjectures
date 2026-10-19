## Worker report

The delivery states `AlgebraicGeometry.Scheme.TrfLocalization.localizationFilteredSectionExchange`
in `Sheaf.AlgebraicGeometry.ProEtaleLocalizationFilteredSection`. Its sole theorem has proof
`sorry`. `SectionData`, `PullbackData`, and `ExchangeData` are the explicit witnesses for this existence theorem;
they do not select functors or maps from a non-unique existence assertion. All helper definitions
have actual data: composites, a recorded derived adjunction, its derived
open counit, the exact-functor factorization, and the unit--square--counit closed mate.

The node's mathematical statement is unchanged. Its statement dependencies gain three already
landed nodes: `lem-trf-filtered-derived-hom-calculus` supplies the uniformly finite filtered
localization and its chain-level forgetful/graded functors; `def-weil-proetale-inverse-image`
supplies the section-normalized intrinsic constant-module adjunction; and
`lem-trf-open-square-exchange` supplies definitions of the canonical open mate and the
constant-coefficient pullback comparisons. The latter's existence theorem is restricted to
special coefficient rings, so this delivery does not invoke it for arbitrary finite A.
Instead, the present theorem includes existence of the normalized open comparison needed here,
proved by the generic open exchange proof dependency, as the node requires.

Hypotheses and clauses, read against the node:

- A finite commutative ring is `(A : Type u) [CommRing A] [Finite A]`. The schemes are
  `{U Z X : Scheme.{u}}`. The immersion and complement hypotheses are `[IsOpenImmersion j]`,
  `[QuasiCompact j]`, `[IsClosedImmersion i]`, and
  `h : Set.range j = (Set.range i)ᶜ`. No field, torsion, characteristic, constructibility,
  completion, properness of t, or geometric-stalk conservativity is assumed.
- The main theorem uses `proEtaleRingModules X (proEtaleConstantRing X A)` through
  the types of the recorded operations. It retains the small pro-etale site,
  with object universe u+1 and morphism universe u, and module universe u+1. This is
  exactly the intrinsic coefficient presentation used by the recorded extension by zero.
- `D⁺(X,A)` is `DerivedCategory.Plus CX`, with CX instantiated by the recorded module
  category. The filtered category is the existing
  `CochainComplex.FiniteFiltered.Derived (A := CX) false`. Its `Complex` is the
  full category of uniformly finite decreasing filtrations by subcomplexes on strictly
  bounded-below complexes, and its `quasiIso` tests every `graded false r`. No fixed
  filtration interval is imposed on the entire filtered category.
- `SectionData.complexSection` is the functor on bounded-below chain complexes, and
  `totalComplex` identifies its total with C naturally, including all chain maps.
  `filtration` says every step r≤0 is the whole complex and every step r≥2 is zero.
  `subcomplex` and `subcomplex_inclusion` identify F¹ with termwise `j!j*` and its inclusion
  with the actual open counit. Thus all integer steps in the displayed filtration are fixed.
  Naturality of the total and monicity of the inclusions also force the action on F¹ maps.
- `gradeOneComplex` is normalized by the projection from F¹, and `quotientComplex` by
  `quotient_projection`, the closed unit from F⁰. These give the actual two graded
  complexes, rather than arbitrary objects isomorphic to them. The remaining grades
  vanish because of the specified filtration bounds.
- `omega`, `gr`, `omegaFactors` and `grFactors` give the descended forgetful and all graded
  functors, valued in D⁺. The factorization isomorphisms are natural transformations,
  so they specify maps as well as objects. `sectionFunctor` and `descent` express descent
  of the actual chain-level section. `total`, `gradeOne` and `gradeZero` are the three
  natural identifications in the node. Their `_normalization` fields pin them to the
  total/subcomplex/quotient identifications on representatives; they cannot be freely
  chosen or rescaled independently of those constructions.
- The closed operation in `gradeZero` is `proEtaleConstantDerivedDirectImage i A`, the
  ordinary right-derived direct image via K-injective resolutions in all sheaves.
  `closedFactors` compares it with the termwise closed direct image. Its normalization
  fixes the image of the derived closed unit to the actual termwise sheaf unit. This
  identifies the ordinary Ri* with its specified adjunction and does not substitute a
  completed direct image. The existence theorem passes the recorded K-injective-derived
  functor and derived adjunction explicitly; they are not assumptions on the input.
- `complex_zero` and `complex_shortExact` state the actual termwise localization sequence,
  with the open counit and the unit of `sfIntrinsicConstantModuleAdjunction`. `connecting`
  is natural, `triangle_distinguished` gives the localization triangle with exactly these
  derived first two arrows, and `connecting_normalization` fixes its connecting map to
  `DerivedCategory.triangleOfSESδ` on representatives. Together with the normalized
  graded identifications this is the subcomplex--total--quotient triangle of the filtration.
- t, tU and tZ are arbitrary endomorphisms. `wU` and `wZ` say `tU ≫ j = j ≫ t` and
  `tZ ≫ i = i ≫ t`. The only square hypothesis is `IsPullback tU j j t`; there is no
  pullback condition on the closed square. `ExchangeData` is parameterized by the canonical square comparisons;
  the theorem supplies it when the open square is Cartesian.
- The inherited `PullbackData` fields `complexPullback`, `complexTotal`, `complexStep`, `complexStep_inclusion`, `complexGrade`
  and `complexGrade_projection` specify the actual termwise filtered inverse image,
  including all subobject inclusions and cokernel projections. `filteredPullback` and
  `pullbackDescent` give its localization. `plusDescent`, `omegaPullback` and `grPullback`
  have explicit representative normalizations, so all comparisons used later are canonical.
- `complexAlpha` is a natural isomorphism of the two chain-level functors. Its total is
  exactly the identity after the specified total comparisons (`complexAlpha_total`).
  `alpha` descends that isomorphism by `alpha_descent`, and `total` gives its identity
  total map on every derived K.
- `openExchange.inv` is fixed to `sfIntrinsicDerivedOpenMate` by
  `openExchange_normalization`. This is the canonical open-unit transpose, not an arbitrary
  base-change isomorphism. `gradeOne` identifies gr¹(alpha) with this b_t followed by j!(c_j).
  F¹ and gr¹ coincide under the already specified zero F² and projection comparison.
- `closedMate` is actual data: the unit of `closedAdjunction`, the inverse of the
  recorded pullback-square comparison, and its counit, composed and whiskered. Its
  transpose is c_i inverse followed by tZ* of the counit. `closedCounit` states that
  this counit is invertible. `gradeZero` identifies gr⁰(alpha) with exactly this mate
  followed by Ri*(c_i). This construction never uses a Cartesian closed square.
- Every `u : (sfIntrinsicPullback A t).mapDerivedCategoryPlus.obj K ⟶ K` is admitted.
  `morphism_total`, `morphism_gradeOne`, and `morphism_gradeZero` give the three displayed
  formulas for `alpha.hom.app K ≫ sectionFunctor.map u`. The explicit plus compatibility
  only transports between the full bounded-below subcategory and the unbounded ordinary
  operations; its inverse in the last two formulas turns u into the corresponding
  unbounded derived morphism. There is no `[IsIso u]` and no chain-map representative
  hypothesis. Lean composition order is left to right.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the recorded ordinary
  operations, reexporting the finite intrinsic exact inverse image
  `sfIntrinsicPullback` and `sfIntrinsicDerivedPullback`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `sfIntrinsicExtensionByZero`; its recorded exactness is reexported by the open exchange
  module. `sfIntrinsicDerivedOpen` is its termwise derived functor.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicConstantModuleAdjunction`, `sfIntrinsicDirectImageComparison`, and
  `sfIntrinsicDerivedEquivalence`. The former's unit and counit fix the closed maps
  in precisely the same intrinsic category.
- `Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`:
  `proEtaleCanonicalPullbackComposition` and its unique normalized characterization.
  The finite intrinsic interface's `sfIntrinsicPullbackComp` and
  `sfIntrinsicDerivedSquarePullback` use the same canonical composition of inverse images
  transported through the coefficient realization; both are read in the imported
  `ProEtaleIntrinsicFiniteOperations` and `ProEtaleOpenSquareExchange` modules.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `proEtaleDerivedCategory`, the
  standard ordinary localization in intrinsic constant-ring modules.
- `Mathlib.AlgebraicGeometry.Scheme`, `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, and
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `Scheme`, `IsOpenImmersion`,
  `IsClosedImmersion`, and `constantSheaf` respectively, as in the dependency records.
- `Sheaf.Algebra.Homology.FilteredDerivedHomCalculus`: `Complex`, `Derived`, `Q`,
  `forget`, and `graded` in `CochainComplex.FiniteFiltered`; these are existing definitions.
- `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`: `sfIntrinsicOpenAdjunction`,
  `sfIntrinsicDerivedOpenMate`, `sfIntrinsicDerivedSquarePullback`, and
  `sfIntrinsicDeriveMap`. The open counit uses the same `Localization.liftNatTrans`
  construction in an abstract category interface; the recorded canonical square and
  mate data, rather than the special-ring existence theorem, enter the main signature.
- The proof dependency modules are imported without `public`: generic finite open base
  change, general pre-derived adjunctions, exact-functor derivation, ringed-site
  localization, ringed open-closed localization, weakly-etale slice localization,
  Mathlib adjunction mates, adjunction localization, homology sequences and naturality,
  and the localization universal property. `triangleOfSESδ` is public because its
  actual map occurs in the statement.

Edge cases checked before and during writing:

- U=X and Z empty gives F¹=C and zero closed grade; U empty and Z=X gives F¹=0 and
  gr⁰=C. Empty schemes, the zero complex, and the zero finite ring are admitted.
- All integer filtration indices, including negative indices, 0, 1, 2 and larger ones,
  are covered explicitly. Strict lower bounds are existential and can be negative.
- t=id, u=id and u=0 are included. Noninvertible u and derived roofs are included.
- For absolute Frobenius on affine one-space and Z=V(x), the closed square need not
  be Cartesian (inverse image V(x^p)); the statement requires only its commutativity.
- No target-site universe equality is introduced: the intrinsic source categories
  retain the published object and morphism universes and the canonical ULift on scalars.

Searches for an existing statement:

- `msearch.py leanfinder`: “exact open closed localization section of finite filtered
  bounded below complexes compatible with pullback”: eight results about homological
  support, module localization, and derived fractions; none state the section/exchange.
- `msearch.py leansearch`: “finite filtered derived category open closed localization
  section”: eight general localization and derived-category hits; no match.
- `msearch.py loogle`: `CategoryTheory.mateEquiv, CategoryTheory.Functor.mapDerivedCategory`:
  zero hits for the combined query.
- `msearch.py grep` in Mathlib/CategoryTheory:
  `(localizationSection|filteredSection|localization.*filtration|filtered.*localization)`:
  zero hits. The actual searches are logged by the prescribed wrapper.
- `rg` in Mathlib's filtered/localization sources and in the upstream WeilConjectures
  and project's Sheaf sources found the existing finite-filtered localizations and
  open-square comparison modules. Those were read and reused. The node id and the
  proposed main declaration have no upstream match. The etale
  `lem-trf-localization-filtration-descent` is different (bounded etale and no specified
  pro-etale exchange), and the filtered-operation-lifts node is a generic operation
  result rather than this canonical section.

Source checks: read Varshavsky Example 5.2.3 on PDF page 42, its surrounding comparison
principle, the current blueprint proof of `prop-trf-trace-additivity-open-closed` Steps
2 and 6, and the dependency signatures/docstrings. The ordinary pro-etale generalization
and explicit closed-mate computation are the node's stated agent-formulated part.
No statement dispute, correction, new node or dependency repair is needed.

Validation: `scompile.py` completed without errors or warnings (sandbox check 7.6 s;
library check 16.9 s), both within the per-file limit. The delivery dry run and final
delivery recompile the delivered source and run the server preflight.
`deliver2.py --no-push` printed OK: commit a1683b5462 passed preflight and compilation.

The witness structures are parameterized by abelian categories and operation functors to
keep Lean from repeatedly expanding the coefficient realization and K-injective construction. The
main theorem fills every such parameter with its recorded canonical operation, adjunction
or square comparison. These parameters add no hypothesis to the main statement. In
particular the helper closed mate is the explicit unit--inverse-square--counit composite
for the adjunction and square comparison that the theorem supplies.

## Second reading by Q25

Independent maintainer second reading, 2026-10-17, of immutable delivery
3aef3d17edeaf79f0bce45e4432c4af1ab2e36b4. This section replaces the worker's
placeholder; it is the maintainer's reading, not a claim of an earlier group review.
I read packet.md, the snapshot node and its eleven statement dependencies, this
report, and all 508 lines of the delivered module. The mathematical statement and
Lean source need no change.

Sources read: Varshavsky, Example 5.2.3, printed p. 42, and Sections 5.2.1--5.2.2
on pp. 41--42; Stacks proetale.tex, lemma-ses-associated-to-open (09AH),
lines 5135--5180, and lemma-closed-immersion-complement-retrocompact-exact (09BM),
lines 5020--5040. The paper gives the filtered section in the etale constructible
setting; the node explicitly states its ordinary pro-etale extension. The Stacks
sequence and exactness justify that extension with precisely the quasi-compact
complement required here. I also read the parent trace-additivity proposition's
localization-section and non-Cartesian closed-mate uses.

Hypothesis and conclusion comparison:

1. The theorem binds arbitrary Scheme.{u} objects U, Z, X and a finite commutative
   ring A : Type u. IsOpenImmersion, QuasiCompact, IsClosedImmersion and the range
   complement equality express exactly the geometric hypotheses. There is no
   characteristic, invertibility, field, Noetherian, constructibility, completion,
   properness or finite-type hypothesis. Verdict: exact.
2. CX is instantiated by proEtaleRingModules X (proEtaleConstantRing X A).
   proEtaleDerivedCategory is the ordinary DerivedCategory of these module sheaves.
   The original small ProEt site has object universe u+1 and morphism universe u;
   ULift A and the module values live in u+1. The helper parameters CX : Type (u+2)
   and Category.{u+1} CX fit this actual category. All universes are bound; there is
   no site-object/site-morphism universe equality. Verdict: exact.
3. Complex CX false and Derived false from FilteredDerivedHomCalculus are uniformly
   finite filtrations of bounded-below cochain complexes and their localization at
   every graded quasi-isomorphism. DegreeBound false imposes no upper degree bound.
   SectionData uses these definitions, not the different per-term finite-filtered
   category. Verdict: exact.
4. complexSection and totalComplex give the actual complex-level section.
   filtration specifies F^r=top for r<=0 and F^r=bottom for r>=2. subcomplex and
   subcomplex_inclusion fix F^1 and its inclusion to j!j* and the open counit.
   Monicity of inclusions forces the induced maps to be j!j* of the total maps.
   gradeOneComplex_projection and quotient_projection fix the subobject and
   quotient identifications to the projection and the actual closed unit.
   Verdict: every filtration clause, including all integer indices, is present.
5. omega, gr, omegaFactors and grFactors are natural descended evaluation functors.
   sectionFunctor and descent give S on D+, and total, gradeOne, gradeZero give the
   three identifications. Their normalization equations fix their values on
   representatives, including maps. closedFactors compares the actual K-injective
   right-derived direct image with termwise direct image; its normalization fixes
   the closed unit. Verdict: ordinary derived operations, with the correct maps.
6. complex_zero and complex_shortExact use the open counit and closed unit.
   triangle_distinguished uses their derived counterparts; connecting_normalization
   identifies the boundary with DerivedCategory.triangleOfSESdelta (the Lean name
   ends in the Greek delta). Thus this is the underlying localization triangle,
   not an arbitrary completion of its first two objects. Verdict: exact.
7. The universally quantified t, tU, tZ and commuting equations have the correct
   composition order. IsPullback tU j j t is required only for the open square.
   PullbackData specifies termwise filtered inverse image by total, step-inclusion
   and graded-projection comparisons, and normalizes its localization comparisons.
   complexAlpha is an actual filtered natural isomorphism; complexAlpha_total fixes
   its total to the identity, and alpha_descent descends that same comparison.
   Verdict: the required canonical filtered comparison is stated.
8. openExchange.inv equals sfIntrinsicDerivedOpenMate; the latter is the actual
   unit--square--counit open transpose. It is not a freely chosen comparison.
   gradeOne is b_t followed by j!(c_j). Because F^2=0 and the grade-one projection is
   normalized, this also specifies F^1. closedMate is the explicit composite of
   the closed unit, inverse square comparison, and closed counit. closedCounit
   records invertibility of that counit. gradeZero is e_(t,i) followed by Ri*(c_i).
   No Cartesian closed-square hypothesis occurs. Verdict: the two specified maps.
9. morphism_total, morphism_gradeOne and morphism_gradeZero quantify every derived
   u : Lt*K -> K, with no IsIso or single-chain-map hypothesis. The plus compatibility
   inverse converts u to its unbounded ordinary derived map; composition then gives
   exactly j!(j*u after c_j) after b_t and Ri*(i*u after c_i) after e_(t,i).
   Verdict: all three formulas and the quantifier over arbitrary u are present.

Dependency and construction audit:

- Read the snapshot statements and lean records of all eleven dependencies:
  ordinary operations, extension by zero, pullback composition, schemes, closed and
  open immersions, pro-etale site, constant sheaf, filtered derived Hom calculus,
  open-square exchange, and inverse image.
- Read the actual side-clone definitions in ProEtaleIntrinsicFiniteOperations,
  ProEtaleIntrinsicExtensionByZero, SfIntrinsicRealizationTransport,
  ProEtaleOpenSquareExchange, ProEtaleCanonicalPullbackComposition,
  ProEtaleDerivedCategory, ProEtaleInverseImage and ProEtaleConstantDerivedDirectImage.
  The recorded finite interfaces remain reexported by the newer general interfaces.
  Pullbacks are canonical realization transports, extension by zero is the same
  localization Kan extension and sheafification, and direct image is sectionwise
  base-change precomposition through the constant-section scalar map.
- Read the side framework's FiniteCoefficient UpperLowerStar Defs/Iso/Coherence,
  LowerShriek/Open/Defs, and ordinary UpperLowerStar/Defs, as well as the framework
  manifest. The small pro-etale site is retained; no etale or condensed substitute
  enters the signature. The special A_(E,n) theorem of open-square exchange is not
  invoked for arbitrary A. Its canonical mate definitions are generic in finite A;
  the present existence theorem includes invertibility. FiniteOpenBaseChangeNormalized
  also provides the generic finite-level open comparison needed by the proof plan.
- closedAdjunction, openCounit, openFactors and closedMate have real composite data.
  The three witness structures only package this theorem's existential witnesses;
  no definition chooses unspecified data from Nonempty. The sole local theorem is
  localizationFilteredSectionExchange, with proof exactly sorry. There are no
  proof-filled local obligations or sorry-filled definitions.
- The seven numbered proof-docstring steps match the seven node steps: exact
  localization and derived adjunctions; complex section; localization descent;
  normalized triangle; open comparison; closed quotient transpose; arbitrary u.
  I recomputed the closed transpose: naturality of c_i inverse and the closed
  triangle identity give m_C t*(p_C)=p_(t*C); epimorphy gives the required quotient
  normalization. This uses no closed Cartesian assumption.

Edge cases: U=X/Z empty and U empty/Z=X give respectively zero closed grade and
zero open grade. The empty scheme, zero ring and zero complex are included. Negative
filtration indices, 0, 1, 2, and all larger indices are covered. t=id and u=id or 0
are admitted, as are noninvertible u and derived roofs. Absolute Frobenius on A^1
with Z=V(x) has nonreduced inverse image V(x^p), so its closed square need not be
Cartesian; the statement still applies, consistently with the quotient computation.

Independent duplicate searches, 2026-10-17: msearch.py LeanSearch query
"filtered derived localization section open closed pullback" returned eight general
site/pullback hits, none a match. LeanFinder query "finite filtered derived category
canonical open closed localization section compatible with pullback" returned eight
derived-category/factorization hits, none a match. Wrapper grep for
(localizationSection|filteredSection|localization.*filtration) returned zero hits.
Direct rg in Mathlib's CategoryTheory and Algebra/Homology, upstream WeilConjectures,
and the group's lean/Sheaf found only the existing filtered-category machinery and
unrelated localization uses. Those definitions are reused. No duplicate full section
or exchange statement was found.

Mechanical checks: lean.statement is byte-for-byte the theorem signature before :=.
Every local declaration and the module have source/blueprint docstrings. All Lean
lines are at most 100 characters; autoImplicit is false and every variable/universe
is bound. The three added statement dependencies are already landed interfaces,
not private definitions or unrecorded prerequisites. No statement correction, new
node or dependency module is needed.

Compiler reproduction: ran
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q25
lem-trf-localization-filtered-section-exchange
snapshot/lean/Sheaf/AlgebraicGeometry/ProEtaleLocalizationFilteredSection.lean
as one command from the immutable review directory. Exit code 0; no diagnostics.
The wrapper reported sandbox Sheaf/Stage2/Sandbox0.lean [10.1 s] and library
Sheaf/AlgebraicGeometry/ProEtaleLocalizationFilteredSection.lean [19.5 s]. The current
wrapper executes the side-overlay checks on the server, superseding the report's
historical local timing; it was invoked as prescribed, without a direct ssh command.
No global build, project-clone edit, live Lean write, delivery or Git mutation was run.

Finding and fix: H11 (also the substantive report-section requirement in H1): the
original second-reading heading contained only a statement that no second reading
had occurred. This complete independent reading replaces it. Worker report retained
verbatim. No Lean or node changes. Verdict: FIX, report only.
