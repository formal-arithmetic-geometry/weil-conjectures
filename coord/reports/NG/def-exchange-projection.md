## Worker report

The module `Sheaf.Paper.ExchangeProjection` defines the three transformations of
`def-exchange-projection`. The finite construction specializes existing canonical
pro-etale maps to the actual coefficient quotient. For the other coefficient
stages it writes the three composites on supplied operation domains, together with
interfaces expressing the required coefficient compatibilities and the operation
of taking a common-field representative. Every definition has real data; there are
no new theorems, proofs, axioms, or `sorry`s in this file. The item's mathematical
statement, dependencies, and proof fields are unchanged.

### Hypotheses and clauses

1. A prime ell is `(l : ℕ) [Fact l.Prime]`. The finite extension is
   `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
   [FiniteDimensional (Padic l) E]`. The exponent is `(n : ℕ) (hn : 1 ≤ n)`.
   `coefficientExtensionExchangeProjection` passes
   `Padic.coefficientExtensionRing l E n` to the finite construction, with the
   finiteness proof `Padic.finite_coefficientExtensionRing l E n hn`.
   The valuation ring and uniformizer are those of the coefficient dependency;
   neither is a fresh arbitrary choice in this delivery.
2. The base scheme is `(S : Scheme.{u})`. Invertibility of ell is
   `[∀ s : S, Invertible (l : S.residueField s)]`, the usual equivalent residue
   field formulation of invertibility on S. The three schemes have `[X.Over S]`,
   `[Y.Over S]`, `[Y'.Over S]`. Their structure morphisms each have
   `LocallyOfFiniteType` and `QuasiCompact`, exactly finite type. The two named
   maps have `[f.IsOver S]`, `[g.IsOver S]`, `IsSeparated`, `LocallyOfFiniteType`,
   and `QuasiCompact`. There is no assumption of a field base, no Noetherian
   hypothesis, and no properness assumption on f or g.
3. The four schemes and four arrows are explicit, and
   `(sq : IsPullback g' f' f g)` is the Cartesian square, including commutativity.
   A specified Cartesian square is used instead of replacing X' by a syntactic
   chosen pullback. `(c : Compactification f)` supplies the chosen open immersion,
   proper factor, and factorization. `c.ofIsPullback sq` is precisely c'.
4. The finite ambient categories are the existing unbounded
   `DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat Λ))` presentation
   of constant-coefficient module sheaves. This is the fixed-scalar presentation
   already used by the extension-by-zero and compactification dependencies, on
   the same small pro-etale site. The pro-etale-operations dependency explicitly
   provides `finiteCoefficientRealization_isEquivalence` and
   `finiteCoefficientUnrealization` between this presentation and its ring-sheaf
   module presentation. This delivery uses the existing fixed-scalar operations,
   not a new category, scalar action, pullback, direct image, or tensor definition.
   All coefficient and scheme sizes are retained: Λ is in `Type (u+1)`,
   schemes in `Scheme.{u}`, and fixed-scalar modules in `ModuleCat.{u+1} Λ`.
5. `finiteExchangeProjection` has three components. Its first component is
   `AlgebraicGeometry.ProEtale.derivedBaseChangeMap ... sq.toCommSq`.
   The imported definition takes the mate of
   `leftDerivedUpperStarSquareIso`, whose construction is the inverse of the
   first pullback-composition comparison, the equality supplied by the square,
   and the second composition comparison. Thus theta has the stated orientation.
   Its mate is the unit at f', followed by the image of theta and of the counit
   at f. This is the constant-coefficient realization of the ambient ringed
   exchange formula, rather than an assumed base-change isomorphism.
   Mathlib `mateEquiv` fixes the mate convention; its `mateEquiv_counit`
   characterizes the transpose appearing in the node.
6. The second finite component is
   `rightDerivedLowerShriekOfCompactificationBaseChangeMap ... sq c`.
   It uses `rightDerivedLowerShriekOfCompactification = D(j_!) ⋙ R(p_*)`,
   and the base-changed compactification, applies `derivedBaseChangeMap` for p
   after j_!, then applies proper direct image to open base change. The existing
   `derivedOpenImmersionLowerShriekBaseChangeIso` is oriented
   `j'_! g'^* ≅ bar_g'^* j_!`; its inverse is beta in this node. Exactness makes
   `D(j_!)` termwise extension on arbitrary unbounded complexes. There is no
   boundedness or etale-origin restriction on the map's definition.
7. The third finite component is `projectionMapOfCompactification ... c`.
   Its proper-factor map is the canonical right-adjoint projection map:
   `CategoryTheory.Adjunction.rightAdjointProjectionMap`, defined using the
   tensor-pullback comparison followed by `epsilon ⊗ 1`, then unit/adjunction.
   The remaining factor is proper direct image of the inverse open projection
   isomorphism, followed by the pullback-composition identification for p j=f.
   This is gamma in the node's order. The source and target are the actual
   bifunctors `derivedTensorRightDerivedLowerShriek` and
   `rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar`.
8. K and L are arbitrary because each component is a natural transformation
   (the projection map is a transformation of curried bifunctors). Taking `.app K`
   and then `.app L` gives the displayed components. Consequently the very same
   maps apply on the bounded constructible and finite-Tor subcategories; no
   assertion that the operations preserve those categories is used or added.
   None of the three outputs has type `Iso`, `IsIso`, or a nonempty collection of
   arbitrary transformations.
9. The higher-stage formulas are explicitly relative to supplied data, as the
   node requires. `ExchangeProjectionStage` takes six categories with independent
   object and morphism universes, the restricted operation functors, both
   pullback/direct-image adjunctions and the proper-factor adjunctions, theta for
   the two squares, beta, mu, gamma, and the identifications with `Rp_* j_!`.
   The category parameters are the supplied full domains; closure is expressed by
   each displayed composite being a functor between those domains. This interface
   does not claim to construct integral/rational/Qbar domains or operations on
   an arbitrary S. Instantiate it with the integral completed operations, their
   rationalizations, or the supplied common-field operations, respectively.
10. `ExchangeProjectionStage.exchange` is exactly `mateEquiv ... theta.hom`.
    `compactExchange` transports by the compactification identifications and calls
    `compactificationExchangeFromData`, whose displayed body is the proper-square
    mate followed by the image of beta, with only associators inserted.
    `projection` transports by the same identifications and calls
    `compactificationProjectionFromData`; that body is
    `J ◁ adj.rightAdjointProjectionMap mu.hom` followed by `(postcompose₂ R).map
    gamma.hom`. Thus no arbitrary transformation replaces a canonical mate.
11. Integral comparison requirements are expressed by
    `ExchangeProjectionAdjunctionComparison.unit` and `.counit`, and
    `ExchangeProjectionComparisonPreserves` for theta, mu, beta and gamma.
    The supplied reduction functors are their arguments, for each positive m,
    and the scalar-cocycle interface expresses compatibility with successive
    transition functors (use the opposite order on positive exponents).
    These are requirements on supplied comparison data, not newly proved
    preservation or existence statements. They retain all positive levels,
    rather than only the originally fixed n. The tensor and pullback fields at
    this stage are the supplied completed operations, not ordinary tensor/pullback.
12. Rationalization and common-field passage are genuine functor actions on the
    finite/integral component: `exchangeProjectionCoefficientRepresentative`
    returns `source.hom ≫ inclusion.map component ≫ target.hom`.
    Its endpoint isomorphisms are the supplied identifications, not arbitrary
    morphisms. For rational coefficients inclusion is the localization functor;
    for Qbar it is the supplied finite-stage inclusion into the common-stage
    category. The embedding in the chosen algebraic closure and finite field
    presentations belong to that supplied coefficient category, not to a new
    coefficient object in this definition. `ExchangeProjectionScalarCocycle`
    includes both `.identity` and `.composition` with all three indices and the
    transition composition isomorphisms. Together with preservation of comparison
    maps and units/counits, these are the stated admissibility requirements on
    scalar comparisons, including identity field extensions and arbitrary towers.
    No rational-to-finite reduction functor is introduced.
13. The c in all compact-support constructions remains an explicit input (or the
    supplied identifications refer to the chosen c). No comparison between
    compactifications or claim that such comparisons intertwine the maps is
    asserted. The final paragraph of the node is thus respected: functor coherence,
    map coherence, existence, and preservation are separate theorems.

### Dependencies read and declarations used

The following existing declarations supply the actual finite construction:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the real quotient
  `Padic.coefficientExtensionRing` from its coefficient-construction import.
- `WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar`:
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarSquareIso`,
  `derivedBaseChangeMap` and the canonical derived adjunctions.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv` and
  `mateEquiv_counit`; the adjunction-mate dependency already has this exact
  `mathlib_match` and needs no replacement record.
- `WeilConjectures.Compactification.Refinement` and `.BaseChange`:
  `AlgebraicGeometry.Compactification`, its factorization data and
  `Compactification.ofIsPullback`.
- `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek`:
  `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`.
- `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekBaseChange`:
  `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`.
- `WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.BaseChange`:
  `openImmersionLowerShriekBaseChangeMap`, its invertibility theorem,
  `openImmersionLowerShriekBaseChangeIso`, and
  `derivedOpenImmersionLowerShriekBaseChangeIso`.
- `WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriekProjection`:
  `derivedOpenImmersionLowerShriekProjectionIso` and the existing invertibility
  theorem for `derivedOpenImmersionLowerShriekProjectionMap`.
- `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekProjection`:
  `derivedTensorRightDerivedLowerShriek`,
  `rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar`,
  `projectionMapOfCompactification`.
- `WeilConjectures.CategoryTheory.Adjunction.ProjectionMap`:
  `CategoryTheory.Adjunction.rightAdjointProjectionMap` (its source was read to
  check the order mu, counit, and adjunction).
- `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.FlatModuleCat` supplies
  the required flatness and Grothendieck coefficient instances for `ModuleCat Λ`.

The recorded ringed interfaces were also read: `ChosenCartesianSquare`,
`proEtaleDerivedCategory`, `proEtaleRingDerivedPullbackComposition`,
`proEtaleAmbientRingedExchange`, `ProEtaleTensorModel`,
`proEtaleCanonicalTensorPullback`, `derivedProjectionFormulaMate`,
`ringedProjectionMateExact`, and `finiteCoefficientDerivedDirectImage` with
its realization equivalence and derived pullback. The construction uses the
canonical fixed-scalar operations already used by the recorded compactification
and open-extension nodes. Importing the legacy derived framework together with
the relocated `FiniteCoefficient.UpperLowerStar.Defs` declares `lowerStarComp`
twice. I repaired that compilation issue by importing the consistent upstream
closure; no duplicate declaration, fresh operation, or edited live file is used.

The constructibility dependencies were read in
`Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` and
`Sheaf.Paper.FiniteTorAmplitude`, and the completed integral category in
`Sheaf.Paper.DerivedCompleteIntegralDetailed`. Their hypotheses are restrictions
on the supplied domains, not assumptions needed to define the finite maps on
ambient categories. `Sheaf.Paper.SfDerivedDirectImage` and the integral completed
pullback/tensor interface were read to distinguish completed operations from
finite or ordinary operations. The absent records for rationalization,
algebraically closed coefficients, higher compact support, and compactification
coherence do not need arbitrary replacements here: the node expressly takes
higher operation domains and coefficient comparisons as supplied data and asserts
no compactification coherence. No theorem about those constructions is invoked.

### Edge cases and checks

- n=0 is excluded by `hn`; n=1 is admitted and uses the actual coefficient quotient.
- Empty schemes and zero complexes are admitted. No geometric point, nonempty
  scheme, nonzero object, connectedness, or positive degree is required.
- The generic finite helper also accepts the zero finite ring. All three arrows
  are the same canonical composites, even when source or target is a zero object.
- K,L can be unbounded and need not be constructible or finite Tor. Invertibility
  of a projection or exchange map is never inferred from its mere definition.
- The arbitrary-base and field-base cases use the same chosen-compactification
  composites. In the former, a chosen compactification is supplied rather than
  an existence theorem being assumed silently.
- Higher categories have independent object and Hom universes. No equality of
  small-site object and morphism universes is imposed.
- Identity coefficient changes and arbitrary composable towers are both present
  in the scalar interface; reduction applies at every positive integral level.
- Every binder is explicit (`set_option autoImplicit false`); every declaration
  has its source and blueprint docstring; the file has no local instances,
  private definitions, file-local notation, or postponed theorem.

### Searches

- `msearch.py NG def-exchange-projection leanfinder` with query
  “Exchange and projection natural transformations for derived pullback direct
  image and compactly supported direct image of proetale sheaves” returned eight
  generic sheaf pullback/adjunction hits, including `SheafOfModules.pullbackComp`,
  `pullbackIso`, `conjugateEquiv_pullbackComp_inv`, and
  `TopCat.Sheaf.pullbackPushforwardAdjunction`; no combined construction.
- Loogle query `CategoryTheory.Adjunction, "projection"`: zero hits.
- Mathlib grep query `projectionFormula|projectionMap|lowerShriek|extensionByZero`
  in CategoryTheory: zero hits for the requested whole construction.
- Local `rg` of the upstream and side-project sources found the three canonical
  finite maps used above; searching the item id found no existing declaration
  covering all finite and supplied higher-stage clauses. Source searches also
  checked the proposed new helper names to avoid duplicate declarations.
- `scompile.py --source` was used for current published sources, including
  side-only lower-shriek base change and the recorded ringed interfaces. It
  confirmed the proposed `Sheaf.Paper.ExchangeProjection` module was absent.
  Guessed modules for the unrecorded higher-category nodes were not published;
  those categories remain supplied as the node explicitly requires.

There is no new `STATEMENT-DISPUTED` finding and no stage-2 statement correction.
The stage-1 correction already present in the base node remains unchanged.

## Dependency modules

`lem-cbc-proetale-extension-zero-base-change` had no usable recorded declaration.
Its lean-only attachment now names the existing upstream
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.BaseChange` maps
and isomorphisms. This is exactly the canonical open-immersion base-change
isomorphism on arbitrary complexes; the inverse of the displayed upstream iso is
the orientation written in the node. No source module is copied or redefined.

`lem-cbc-extension-zero-projection-formula` had declaration names but no module or
complete record. Its lean-only attachment now names the existing upstream
`WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriekProjection`
isomorphism and invertibility theorem. The upstream iso is oriented from
`j_!(K ⊗ Lj*L)` to `j_!K ⊗ L`; its inverse is exactly the node's displayed
canonical map. The full signature retains `Functor.postcompose₂` and j_!.

Both dependency JSON files change only `lean`. No new DAG node is introduced.

### Validation

Each delivered Lean file is compiled separately through the authorized
`scompile.py` wrapper, including its library module name. The delivery dry run
also runs the maintainer preflight and its per-file checks. The first preflight
requested signatures starting at the declaration keyword `def`; the metadata was
corrected to that convention. Independent second reading is left to the assigned
reader, as required by the worker brief.

## Second reading by NG

I read the current node before the Lean, then its blueprint source at
`sec-smooth-purity/sk-def-sf-operations/def-exchange-projection.md` (order
1487), the dependency statements and recorded signatures, and the actual
declarations used by this module. The literature files absent from the shared
clone are present in the read-only local literature checkout. I also read
Stacks `sites-cohomology.tex`, section `section-base-change-map` (0735), and
`section-projection-formula`, equation `equation-projection-formula-map`
(0B56). The latter explicitly constructs the map for arbitrary objects of
the unbounded derived categories without a perfectness assumption; perfectness
is needed for the subsequent isomorphism theorem, not for this definition.

The node-to-Lean checklist is as follows. Every verdict below is a match.

1. **Prime and coefficients.** `l`, `Fact l.Prime`, `E`, `Field E`,
   `Algebra (Padic l) E`, and `FiniteDimensional (Padic l) E` introduce exactly
   a finite extension of Q_l. `n` and `hn : 1 ≤ n` give the positive exponent.
   `coefficientExtensionExchangeProjection` uses the dependency's actual
   `Padic.coefficientExtensionRing l E n`. I opened `CoefficientExtension`:
   this is the quotient by the nth power of the ideal of its recorded
   uniformizer in its recorded valuation ring. The named finiteness theorem
   supplies `Finite`; a second valuation ring, uniformizer, or quotient is
   not introduced here.
2. **Base and geometric hypotheses.** `S : Scheme.{u}` and
   `[∀ s : S, Invertible (l : S.residueField s)]` say that l is invertible on
   S, including an empty S. `X.Over S`, `Y.Over S`, `Y'.Over S`, and the
   `LocallyOfFiniteType`/`QuasiCompact` pairs on the structure maps express
   the three finite-type S-schemes. The analogous pairs and `IsSeparated`
   on f and g, together with `f.IsOver S` and `g.IsOver S`, express precisely
   the two separated finite-type S-morphisms. No field-base, Noetherian,
   properness, or nonemptiness assumption has entered this specialization.
3. **Square.** The four schemes and the arrows g', f', f, g are explicit.
   `sq : IsPullback g' f' f g` supplies commutativity and the Cartesian
   property. This is the existing Mathlib pullback-square notion, not a
   private definition or an assumption that X' is a literal pullback term.
   It supplies the identification required by the Cartesian-square node.
4. **Ambient finite categories.** I expanded the imported functor signatures:
   they are the unbounded derived categories of fixed-scalar `ModuleCat`
   sheaves on exactly `Scheme.ProEt.topology T`. This presentation is also
   used by the recorded open-extension and compact-support dependencies.
   The recorded operations module's `finiteCoefficientRealization` and
   `finiteCoefficientUnrealization` identify it with the ring-sheaf module
   presentation. The delivered file reuses these existing finite operations;
   it does not define another scalar action, site, or derived tensor product.
5. **Theta.** The first component of `finiteExchangeProjection` invokes
   `derivedBaseChangeMap`. I opened `Derived.UpperLowerStar`: its
   `leftDerivedUpperStarSquareIso` is
   `(leftDerivedUpperStarComp A f' g).symm`, then congruence for the square
   equality, then `leftDerivedUpperStarComp A g' f`. This is exactly
   Lf'^* Lg^* -> Lg'^* Lf^*, with the required orientation.
6. **Ordinary exchange.** The same source defines `derivedBaseChangeMap`
   by `mateEquiv` using the canonical two derived adjunctions and theta.hom.
   I opened Mathlib's `mateEquiv` and `mateEquiv_counit`: the formula inserts
   the unit for f', applies theta, and applies g'^* to the counit for f,
   all under Rf'_*. Its transpose is the node's two-arrow composite. The
   output is a natural transformation, not an asserted isomorphism.
7. **Chosen compactification.** `c : Compactification f` is the existing
   structure with open immersion c.i, proper morphism c.g and
   `c.comm : f = c.i ≫ c.g`. I opened `Compactification.ofIsPullback`:
   its middle scheme is the pullback of c.g and g; its open arrow is the
   lift using g' and f'. Thus `c.ofIsPullback sq` is exactly c'. Quasi-
   compactness of the open arrow follows from the supplied quasi-compactness
   of f and the proper factor; no extra compactification datum is imposed.
8. **Open extension and beta.** `Rf_!(c)` expands to termwise open extension
   followed by the total right-derived proper image. The second component
   invokes `rightDerivedLowerShriekOfCompactificationBaseChangeMap`, whose
   body applies proper-square exchange to j_! and then the inverse of
   `derivedOpenImmersionLowerShriekBaseChangeIso`, inserting the standard
   identifications of exact inverse image with its derived functor. The
   inverse is beta in the node's direction. Neither boundedness nor an
   etale-origin condition is imposed on this chosen-composite map.
9. **Tensor comparison and pi.** The third component is
   `projectionMapOfCompactification`. Its proper factor is
   `rightDerivedLowerStarProjectionMap`; I followed this to
   `Adjunction.rightAdjointProjectionMap`. That definition transposes mu
   followed by tensoring the counit with the identity. Its component is
   consequently the node's `Ru_*(a) ∘ eta`. The Noetherian coefficient
   instance needed by the upstream flat-pullback API follows from `Finite`;
   no Noetherian hypothesis on a scheme is required.
10. **Gamma and PF.** The remaining factors of that same definition are
    proper image of the inverse open projection isomorphism, then proper
    image of the pullback-composition identification for c.i and c.g.
    Their order is exactly the two arrows in gamma and then the displayed
    PF composite. The source and target are the existing two curried
    bifunctors named in `finiteExchangeProjection`.
11. **Objects and domains.** The transformations' components are defined
    for arbitrary K and L in those ambient derived categories. In
    particular, evaluation on bounded constructible K and finite-Tor L is
    included; preservation of either subcategory is not inferred here.
    `IntrinsicFiniteTorsionConstructibility` and `FiniteTorAmplitude` use
    the same actual quotient coefficients and add predicates, not different
    finite operations. No clause asserts invertibility of the three maps.
12. **Supplied higher-stage data.** `ExchangeProjectionStage` records the
    six supplied domains, operation functors, ordinary and proper-factor
    adjunctions, square comparisons, beta, mu, gamma, and both chosen-
    compactification identifications. Closure is required by the functor
    types. Its `exchange`, `compactExchange`, and `projection` definitions
    expand to exactly the three recipes above, with the endpoint
    identifications inserted. These generic recipes can be instantiated on
    the prescribed full domains; they assert no existence of operations on
    all bounded constructible objects over arbitrary S. In particular they
    do not substitute ordinary tensor for completed integral tensor.
13. **Finite reductions and scalar comparisons.**
    `ExchangeProjectionAdjunctionComparison.unit` and `.counit` write the
    two required transported adjunction equations. Applying
    `ExchangeProjectionComparisonPreserves` to theta, proper theta, beta,
    mu, and gamma writes preservation of the structural comparisons.
    These interfaces are parameterized by the supplied coefficient functors,
    so at the integral stage they apply at every m ≥ 1, not just the fixed
    n. `ExchangeProjectionScalarCocycle` retains identity and composition
    equations for every i ≤ j ≤ k, including equal indices; applied to the
    opposite order of positive exponents it gives transition compatibility.
    The three recipes themselves need only the operation data; the separate
    comparison interfaces express admissibility of coefficient passage.
14. **Rational and common-field components.**
    `exchangeProjectionCoefficientRepresentative` is precisely inclusion
    applied to the component, conjugated by the supplied endpoint
    isomorphisms. Taking inclusion to be rationalization gives the rational
    component; taking it to be the common-stage inclusion gives the common-
    field morphism class. The normalization/cocycle and unit/counit
    interfaces above are the stipulated scalar-comparison requirements.
    This helper introduces no choice of an arbitrary transformation and no
    rational-to-finite reduction functor.
15. **Choice and separate theorems.** The compactification remains an input,
    or is retained through the supplied higher-stage identifications. No
    definition supplies compactification-independence, refinement
    intertwining, higher-stage preservation, or an existence theorem.

I checked the pre-existing stage-1 correction against the original blueprint
first. Its distinction between ambient finite maps and supplied higher-stage
domains is necessary: the disjoint family of projections P^r -> Spec(k) over
the infinite disjoint base has no uniform bound on the direct-image amplitude.
Also the compactification-coherence node compares functors on its etale-origin
domain, not the three transformations on every ambient object. The correction
retains the source's explicit composites and leaves these additional assertions
as theorem obligations. I opened two audited citers: `def-sf-pf` now explicitly
uses the chosen-compactification map and separately cites its invertibility
theorems, so its `holds: true` verdict is justified; the inverse arrow in
`def-pur-affine-line-purity-comparison` still needs a projection-formula theorem,
so its recorded `holds: false` verdict remains justified. No new correction or
change to a target/unit statement was made.

For H13 I independently read both dependency nodes and their source modules.
`lem-cbc-proetale-extension-zero-base-change` is exactly the canonical open
square base-change isomorphism, after taking the inverse of the published
orientation, with arbitrary complexes and finite constant coefficients.
`lem-cbc-extension-zero-projection-formula` is exactly the inverse of the
published canonical open projection isomorphism, again on arbitrary complexes.
The former had no record; the latter had an incomplete attachment. Their
repairs change only `lean`, reuse the published declarations, and explain the
old interface failure in `lean.note`. There are no new nodes or dependency
source files to review.

Edge cases: n=0 is intentionally excluded and n=1 is included. Empty schemes,
zero complexes, the zero finite ring in the generic helper, identity square
maps, identity coefficient changes, and arbitrary towers remain allowed.
There is no finite-index or nonempty-index assumption. All six abstract
category object and Hom universes are independent. The finite API keeps
`Scheme.{u}`, its actual small pro-etale site, and `ModuleCat.{u+1}`; it does
not identify the site's object and morphism universes. The residue-field
invertibility condition excludes exactly the prohibited characteristics.

Independent searches used different wording from the author's:

- LeanFinder: "Beck Chevalley mate of inverse image square and shriek tensor
  projection morphism for adic sheaves" returned general pullback and
  condensed-module adjunction results, not this whole construction.
- Loogle: `CategoryTheory.mateEquiv` returned the actual mates API, whose
  signature and definition I opened and checked as above.
- Mathlib grep: `BeckChevalley|baseChange.*[Pp]rojection|projection.*[Cc]omparison`
  returned no hit. Local searches of `WeilConjectures` and `lean/Sheaf` for
  the three operations, common-field representatives, coefficient-comparison
  equations, and the proposed helper names found the existing finite pieces
  that the module already reuses, but no existing declaration covering the
  entire finite and supplied-stage node.
- LeanSearch: the query describing a square of adjunctions and compact-support
  projection failed with the service's Internal Server Error. This is recorded
  as unavailable, not as evidence that no declaration exists.

I found no remaining mismatch requiring a mathematical or Lean edit. I retained
the author's module and node records rather than rewriting valid definitions.
All declarations have source/blueprint docstrings; this definition node has no
proof steps. There are no new theorem proofs, axioms, hollow data, local
notations, private copies, or unbound parameters. The primary `lean.statement`
is verbatim the declaration signature from `def` to `:=`.

Validation: `scompile.py NG def-exchange-projection
lean/Sheaf/Paper/ExchangeProjection.lean` passed without warnings in sandbox
form (16.0 seconds) and under its delivered module name (13.4 seconds). The
delivery wrapper additionally checks the two existing dependency attachments.
Only this independent-reading section was added by the second reader.
