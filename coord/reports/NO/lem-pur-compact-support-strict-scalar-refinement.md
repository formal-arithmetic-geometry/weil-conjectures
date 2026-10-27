## Worker report

The delivery states `lem-pur-compact-support-strict-scalar-refinement` in
`Sheaf.Paper.CompactSupportStrictScalarRefinement`, namespace
`WeilConjectures.PurStrictScalar`. The main declaration is
`compactSupportStrictScalarRefinement`. Its first conjunct is the requested equality
in the derived category of strict B-module towers. Its second conjunct is the
normalized total-limit square. The remaining declarations retain the clopen
normalization, ordered proper/open scalar cube, refinement and composition
coherence, and the canonical integral-support coordinates of that limit square.
All theorem proofs are `sorry`; every definition has actual data composed from
published constructions. No source statement is corrected or disputed.

Hypothesis and notation correspondence:

- The finite-field datum is `D : FiniteFieldDatum.{u}`. It contains the prime
  characteristic, positive finite-field exponent, finite field and fixed algebraic
  closure. `l : ℕ`, `[Fact l.Prime]`, and `hl : l ≠ D.p` are precisely the coefficient
  prime and unequal-characteristic hypotheses. These are explicit section variables
  included in the geometry theorems, not auto-bound parameters.
- `E F : Type u`, the two `Field`, `Algebra ℚ_[l]`, and `FiniteDimensional ℚ_[l]`
  instances, and `i : E →ₐ[ℚ_[l]] F` encode the two finite extensions and their
  inclusion. A field algebra homomorphism is injective. The same universe convention
  is used by the recorded strict scalar mate and the finite-field scheme library.
- `A` and `B` are the existing `Padic.coefficientExtensionIntegers l E/F`;
  `t` and `v` are their recorded uniformizers. No new integer ring, valuation,
  uniformizer, coefficient quotient, tensor, or reduction is defined here.
  `e : ℕ`, `he : PurCompactSupport.Ramification l E F i e`, and `hepos : 1 ≤ e`
  are the specified ramification equality and positivity.
- `X Y : Scheme.{u}` with the `Over (Spec (.of D.k))` instances give the k-schemes.
  `LocallyOfFiniteType` and `QuasiCompact` of both structure maps give finite type;
  `IsSeparated` of both structure maps gives the required separated schemes.
  The morphism is `f : X ⟶ Y` with `f.IsOver`, `IsSeparated f`,
  `LocallyOfFiniteType f`, and `QuasiCompact f`.
- `c d : Compactification f` are the two supplied factorizations: their fields
  `i`, `g`, `fac`, and instances are the open immersion, proper morphism and
  factorization. `r : c.Refinement d` is the recorded refinement structure, with
  ambient arrow, `i_hom`, and `hom_g`; its properness is already an instance.
  No Cartesian refinement hypothesis is added. Quasi-compactness needed by the
  proper/open calculus follows from the finite-type f, via the recorded
  the two explicit `quasiCompact_openImmersion` instances in `supportRefinement`.
- `M : DerivedCategory (scalarReductionSource l E X)` is an object over the actual
  completed integral sheaf. `hM : finiteTorConstructibleIntegral l E X M` contains
  derived completeness, bounded constructibility and a single cohomological
  interval for all reductions, and the single Tor interval for all reductions.
- `pbcDerivedExtend (completedCoefficientMap l E F i X)` is `C_X`; the completed
  coefficient map and derived extension are the published ones, including their
  K-flat normalization. `R_W` and `S_W` are the completed coefficient ring sheaves
  used by `scalarReductionSource` and `completedCoefficientMap`.
- `S S' : CoefficientDerivedSystemCalculus.{u,u} l E/F X` select the same
  normalized reduction-calculus presentations used by the recorded scalar mate.
  Their reduction functors and adjunctions are not arbitrary finite-level maps.
  `support l E/F c S/S'` is the existing native, separately derived proper/open
  reduction tower restricted to discrete constant integral coefficients.
- The strict tower is `Towers B W = ℕᵒᵖ ⥤ Modules B W`; its ordinary derived
  category is `Derived B W`. Here `B` is the standard `ULift.{u+1}` of the integer
  ring, needed for the small pro-etale site's coefficient universe. The site's
  object and morphism universes remain u+1 and u. No equality of those site
  universes is imposed. The scalar mate's existing coefficient universe lift is
  reused throughout.
- Lean index `n : ℕ` denotes positive level n+1, including level 1. The existing
  `subsequence l F Y e` retains e(n+1), with composite transitions. `T l E F i Y`
  is the existing finite-free constant tensor on entire tower complexes; its
  exact localization is used, not a family of unrelated derived-level tensors.
- The finite objects and their integral scalar restrictions, including
  `A_n`, `B/t^n B = B/v^(en)`, `M_n`, and `C_W^(n)`, are exactly those in
  `arrow`, `sourceEvaluation`, `targetEvaluation` and `finiteTensorMap` from
  `CompactSupportStrictScalarMate`. The current theorem uses that actual `arrow`
  and therefore retains all those fixed evaluation and quotient normalizations.

Conclusion correspondence, clause by clause:

1. `supportRefinement` is Theta, direction d to c. Its middle factor is precisely
   `StrictTower.compositionC`, which is the identity-left-square gamma,
   followed by the specified proper compositor. Its outer factors are the
   existing unit-normalized `supportModel` isomorphisms. It is therefore the
   normalized strict comparison, not an unspecified isomorphism.
2. `supportRefinement_isIso` applies to the separately supplied finite origins,
   with no common lower bound. `supportRefinementIso` is exactly inverse Theta,
   constructed as `(asIso ...).symm`. It is rho in the displayed direction.
3. `scalar_refinement_origins` supplies both families of bounded-below finite
   scalar etale-origin witnesses for the actual reduction of M and of C_X M.
   The witnesses are conclusions, not additional hypotheses of the main theorem.
4. The first conjunct of `compactSupportStrictScalarRefinement` reads, in Lean's
   left-to-right composition convention,
   `q_c ≫ subsequence.map rho_F.hom = T.map rho_E.hom ≫ q_d`.
   This is exactly the node's right-to-left displayed equality. The category of
   both sides is `Derived` of strict B-towers. Evaluation and inverse limit have
   not been applied.
5. `scalar_clopen_projection` says that T of the intrinsic `pi` followed by the
   open tensor map equals pi over B followed by open image of the canonical
   pullback/tensor identification. The existing `pi_components` gives identity
   on the section and zero on its complementary open. This uses that actual pi,
   including its zero component; no arbitrary splitting or Cartesian replacement
   enters the statement.
6. `scalar_properOpen_alpha` is the cube for the published beta/pi alpha on every
   commutative proper/open square. `scalar_properOpen_gamma` is the ordered proper
   mate equation, with the published `proper` and `openTensor` factors. Their
   definitions already fix the units/counits, so these clauses retain the actual
   refinement normalization on non-Cartesian squares.
7. `supportRefinementIso_coherence` gives identity and composable-refinement
   equations for rho. `scalar_compactification_composition` gives the scalar
   square with the actual `compositionD` for any supplied compatible proper/open
   tower. The general gamma equation applies also to each horizontal or vertical
   pasted square, using the already recorded `normalizedProperOpenCalculus`.
8. `supportCommonRefinementIso` is rho along the first common-refinement arrow
   inverted, followed by rho along the second. The first three conjuncts of
   `compactSupportStrictScalarRefinementCoherence` state its scalar square,
   independence of both the common refinement and its arrows, and its cocycle.
   The E coherence is a uniform assertion for every coefficient field (so applies
   to F too); the B-valued common-refinement scalar square is stated explicitly.
   `c₀` in this theorem is any supplied compactification used only to obtain the
   same origin proofs; it does not choose or constrain a common refinement.
9. The second conjunct of the main theorem is
   `c_c ≫ Rlim.map rho_F = baseTensor.map (Rlim.map rho_E) ≫ c_d`, where
   `c_c = scalarLimitArrow ... c` is the existing three-factor map
   `tau ≫ Rlim.map q_c ≫ r_e⁻¹`. `scalarLimit` is total right-derived limit on the
   ordinary strict diagram category. Its tau and r_e are the already normalized
   maps of `CompactSupportScalarLimitReduction`, not chosen replacements.
10. `supportRefinementIntegral` is exactly total limit of rho conjugated by
    `scalarSupportLimit`, the canonical native completed-limit/constant-restriction
    identification. `scalarIntegralRefinementComparison` is the same scalar-limit
    arrow in these integral-support coordinates. The last conjunct of the
    coherence theorem states their square. The integral support `scalarSupport`
    is literally the reduction-limit definition (native reduction, separately
    derived proper/open images, then total limit), not a substitute definition.
    Its constant-coefficient coordinates are identified with completed scalar
    extension by the published `scalarCompletion`, normalized on ordinary pure
    tensors and whole-complex counits. Thus the constant/completed equivalence
    carries precisely this square to the completed integral square.
11. Augmentation preservation is inherited from the specific reused maps, via
    `scalarRoosNormalization`, `scalarRoosTensorNormalization` and
    `scalarLimitArrow_augmentation`. These retain the full Roos coordinates and
    every strict augmentation (0,a). The final square does not identify maps by
    testing their finite reductions.

Dependency declarations and sources read:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`; its
  constituent finite-field data are reused without fixing an unnecessary single
  finite coefficient exponent for this all-level statement.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and the imported coefficient constructions.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement`, its category, id and comp.
  The convention-only scheme-property node introduces no new declaration.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: the public general-site
  change-of-rings construction, used through the recorded `pbcDerivedExtend`;
  no ordinary-module specialization is substituted for the sheaf tensor.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: the retained
  `WeilConjectures.finiteTorConstructibleIntegral` and finite coefficient predicates.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `WeilConjectures.sfQcqsCompactSupportRealization`, and its public integral support
  definitions; `Sheaf.Paper.CompactSupportReductionTower`:
  `WeilConjectures.exists_compactSupportReductionTower` and the native lift machinery.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence`;
  `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`:
  `pi_components`, `gamma_isIso`, `normalizedProperOpenCalculus`, and the imported
  actual `pi`, `alpha`, `gamma`, `J`, `G`, `R` and compositors.
- `Sheaf.Paper.CompactSupportStrictScalarMate`:
  `WeilConjectures.PurStrictScalar.arrow`, `strictScalarPull`, `proper`, `openTensor`,
  `image`, `comparison`, `support`, `supportModel`, and
  `compactSupportStrictScalarMate`, including its evaluation statement.
- `Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps` (statement dependency
  `def-cbc-strict-tower-composition-maps`): `compositionC` constructs Theta and
  `compositionD` occurs in the compatible-tower scalar square.
- `Sheaf.Paper.RefinementExchangeCoherence` is a plain proof import only:
  `refinementComparison_isIso` and the identity/composition/common-refinement laws.
  Its `refinementComparison` is definitionally `compositionC` with the same two
  quasi-compactness instances; no theorem supplies the data defining Theta.
- `Sheaf.Paper.CompactSupportScalarLimitReduction`: `scalarLimit`,
  `scalarLimitTensor`, `scalarLimitRestriction`, `scalarLimitArrow`,
  `scalarSupport`, `scalarSupportLimit`, `scalarCompletion`, and the Roos and
  augmentation normalizations just listed.

The two theorem nodes flagged in return H2 are removed from the delivery-added
`stmt_deps`. Refinement coherence remains the original proof dependency, with a
plain import. The item instead cites `def-cbc-strict-tower-composition-maps` and
the new `def-pur-compact-support-scalar-limit-maps`. The latter binds the existing
definitions (including their three named exactness/cofinality helpers) without
asserting `compactSupportScalarLimitReduction`. No dependency node is altered.
No replacement or duplicate Lean module is introduced.
Every already recorded proof-dependency module is imported; the coefficient-model
node presently has no recorded module, so there is none to import for it.

Source and edge-case checks:

- Read the item's full statement and eleven proof steps, every direct statement
  dependency statement and record, the relevant signatures and docstrings, and
  Stacks more-etale.tex at `lemma-shriek-proper-and-open`, its vertical and horizontal
  composition lemmas. Read the current blueprint transport unit in
  `literature/blueprint/latest`; it does not change the auxiliary's statement.
- For e=1 arithmetic restriction retains every positive level. e=0 is excluded
  exactly by the source's e≥1; it is not silently assigned a constant zero level.
- Index n=0 is positive coefficient level 1; no positive quotient is omitted.
- Empty schemes and zero complexes are allowed. No nonempty-site or nonzero-object
  binder occurs, and all specified maps act on zero objects as zero/identity as
  appropriate. A clopen section with empty complement has identity projection;
  an empty section projects to zero. Both cases remain in the same formula.
- Identity refinements and repeated compactifications are included explicitly.
  Common refinements are supplied as actual refinement arrows and the result
  compares any pair of choices, including parallel arrows. There is no assumed
  faithfulness of finite evaluation and no common lower-bound hypothesis.
- The compatible-tower scalar square uses its supplied canonical proper/open
  compositors and therefore also includes identity/open/proper degeneracies.
- No finite-free basis is chosen in this delivery. The basis-independent scalar
  mate from the dependency is the map in every displayed square.

Searches made (all wrapper searches executed, not inferred):

- Lean Finder: `extension of scalars commutes with compactification refinement
  comparison on derived strict towers`: eight hits, ordinary module scalar
  associators and unrelated completion comparisons; no matching statement.
- Loogle: `CategoryTheory.Adjunction, CategoryTheory.NatTrans`: zero hits.
- LeanSearch: `The tensor extension of scalars map commutes with proper open
  compactification refinement comparisons in a derived category of strict towers.`:
  eight hits, ordinary ModuleCat scalar extension and tensor-product functoriality;
  no strict pro-etale tower refinement square.
- Wrapper Mathlib grep: `refinement|compactification` in `CategoryTheory/Adjunction`:
  zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for strict scalar/refinement
  names and concepts, plus the item's literal blueprint id in WeilConjectures:
  no existing declaration of this strict refinement statement. Found and reused
  the scalar mate, normalized strict proper/open calculus, refinement coherence,
  and scalar-limit comparison. The general finite-coefficient refinement modules
  are not the requested equality in D(strict integral B-towers).

Validation: every declaration is explicitly bound (`autoImplicit false`), all lines
are at most 100 characters, and the whole module compiled cleanly through scompile.py
in both required modes (sandbox and its actual library module name). Definitions
introduce only composites/inverses of the specified maps; the sole delayed inputs
are named theorem proofs with their blueprint/source/proof-plan docstrings.

## Second reading by NO

This is a direct-dispatch repair; the dispatcher forbids starting another agent.
The checks below are a self-rereading with the item, new definition node, and Lean
module open. The maintainer supplies the independent reading.

- Field and geometry hypotheses: the main theorem includes `D`, `hl`, both finite
  field-extension instances, the algebra inclusion `i`, the base-scheme instances,
  separated/finite-type/quasi-compact structure maps and `f`, and exactly the
  source's ramification equation `he` and positivity `hepos`. `c` and `d` are
  supplied compactifications, `r` is their existing refinement. No Cartesian
  condition is imposed on `r`. The only extra quasi-compact instances in the
  repaired definition are deduced from `QuasiCompact f`; they add no hypothesis.
- Input and finite origins: `M` is in the completed coefficient derived category,
  and `hM` is the recorded derived-complete bounded-constructible uniform Tor
  predicate. `scalar_refinement_origins` concludes each finite-etale-origin family;
  neither family is an input to the main theorem. Each positive level has its own
  bound. `S` and `S'` present the native reduction systems, and do not replace them
  by arbitrary towers. The ULift coefficients leave the small site's universes
  unchanged.
- Main strict equation: `arrow ... c` has source T of the c support and target
  the e-subsequence of F support. Postcomposing by `subsequence.map rho_F.hom`
  yields the same target as `T.map rho_E.hom` followed by `arrow ... d`.
  `supportRefinementIso` is `(asIso Theta).symm`, so this is the displayed
  rho direction, and the equation is still in `Derived` of strict B-towers.
  Neither evaluation nor total limit is used to assert this equality.
- Normalization clauses: `scalar_clopen_projection` uses the existing pi with
  identity on the section and zero on its complement; `scalar_properOpen_alpha`
  and `scalar_properOpen_gamma` give the ordered mate cube for arbitrary
  commutative proper/open squares. The repaired Theta is now literally
  `supportModel.hom`, whiskered `compositionC`, then `supportModel.inv`.
  Reading `compositionC` shows rId, the identity-left gamma and rComp in precisely
  the source order. No coherence theorem is used to choose this map.
- Coherence clauses: `supportRefinementIso_coherence` has both the identity and
  composable-refinement equations. `scalar_compactification_composition` uses
  the actual `compositionD`, whose definition is now explicitly cited.
  The three initial conjuncts of the final coherence theorem give the common
  refinement scalar square, independence of both choices and arrows, and the
  cocycle. The final conjunct gives the integral refinement square.
- Total limit and augmentations: the main theorem's second conjunct uses the
  actual `scalarLimitArrow`, read in its source as tau followed by Rlim(q) and
  inverse of the specified arithmetic restriction. `scalarSupportLimit`
  conjugates total limit of rho to the integral-support coordinates.
  The source definitions use ordinary cone comparison and universal derived
  units; the recorded Roos/augmentation theorems provide their normalization.
  No equality is inferred just from equality after finite reductions.
- New node: checked its definitions of L, tau, r_e, the scalar arrow, completed
  support and constant restriction against `CompactSupportScalarLimitReduction`.
  Its record lists the used definitions and the helper lemmas
  `scalarLimitTensor_exact`, `scalarLimitRestriction_isIso`, and
  `scalarLimitRestriction_exact`. It records `existing: true` and creates no
  Lean declaration. It does not claim the scalar reduction theorem.
- Edge cases: e=1 retains every positive level; Lean n=0 is exponent 1; e=0 is
  excluded by the source. Empty schemes, zero M, identity refinements, repeated
  compactifications, and empty/full clopen sections remain allowed. Inverses
  are of the specified maps, so these cases do not introduce a free choice.

Mismatch repaired (H2): the previous packet appended two theorem nodes even though
it used only definitions in their modules. Both appended theorem dependencies were
dropped; Theta was rewritten directly using compositionC; its owning definition
node and the new scalar-limit definition node are cited. Theorem statements and
all binders are unchanged. Advisory H11 is addressed by this explicit clause
reading. The repaired module compiled in both wrapper modes in 8.1 seconds each,
with no errors or unexpected warnings.

## New nodes

`def-pur-compact-support-scalar-limit-maps` records the already published canonical
maps in `Sheaf.Paper.CompactSupportScalarLimitReduction`, with `existing: true`.
Its source is Stacks 0941 and 0GL6 together with auxiliary Steps 10--11. It names
the total derived limit, ordinary/derived arithmetic restriction and its inverse,
finite-free tensor/limit comparison, three-factor scalar arrow, exact constant
restriction, native completed support, and canonical native/constant limit
identification. The exactness/cofinality helper lemmas are included in the record.
The existing native support and ringed sequence-site nodes are cited rather than
redefined. No independent definition node already carried this map package; the
only matching helper names were under the scalar-limit reduction theorem.
LeanSearch returned direct-limit tensor and linear-restriction declarations;
LeanFinder returned light-condensed module tensor/projectivity declarations;
Mathlib grep returned zero hits. The DAG/source and blueprint searches are recorded
verbatim in the new node. The exact existing definitions found in the project are
reused, not copied. This is the definition node explicitly requested by the return.

