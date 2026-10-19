## Worker report

The module `Sheaf.Paper.DerivedPullbackTensorHom` records the finite and integral
parts of the operation package in `WeilConjectures.DerivedPullbackTensorHomPackage`
and defines its canonical instance `WeilConjectures.derivedPullbackTensorHom`.
`finiteCoefficientRing` is the quotient coefficient ring at exponent `n+1`.
`finiteDerivedPullback` is the intrinsic exact inverse image on the small pro-etale
site. `finiteDerivedTensor` and `finiteDerivedInternalHom` are the canonical
K-flat derived tensor and monoidal-closed internal Hom on the corresponding
finite coefficient module category, and `finiteDerivedTensorHomAdjunction` is the
canonical parameterized tensor--Hom adjunction. The integral fields are exactly
`integralDerivedPullback`, `integralCompletedTensor`, and
`integralDerivedInternalHom`, i.e. the normalized finite-reduction descents.
The scalar-localized and common-stage categories are supplied by the imported
`sfRationalConstructibleCategory` and
`generalAlgebraicallyClosedConstructibleCategory` constructions and retain the
same objectwise operations.

The finite coefficient hypothesis is rendered by
`[Fact l.Prime]`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
`[FiniteDimensional ℚ_[l] E]`. The scheme and morphism data are
`X Y : Scheme.{u}` and `f : X ⟶ Y`. The finite pullback clause is the field
`∀ n, proEtaleDerivedCategory Y A_{E,n+1} ⥤
proEtaleDerivedCategory X A_{E,n+1}`. The finite tensor and internal-Hom clauses
are the two functors in `finiteDerivedTensor` and
`finiteDerivedInternalHom`; their canonical evaluation/currying compatibility
is the `finiteDerivedTensorHomAdjunction` field. The integral pullback, tensor,
and internal-Hom clauses are the three corresponding functor fields over
`integralTowerModules`. The package constructor fills these fields with the
recorded canonical constructions, with no arbitrary map or `Nonempty` choice.

Dependency declarations used are: `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`
(`AlgebraicGeometry.Scheme.sfIntrinsicDerivedPullback`),
`WeilConjectures.SixFunctors.ProEtale.Derived.Tensor`
(`AlgebraicGeometry.ProEtale.derivedTensor`),
`WeilConjectures.SixFunctors.ProEtale.Derived.Hom`
(`AlgebraicGeometry.ProEtale.derivedHom` and
`AlgebraicGeometry.ProEtale.derivedTensorHomAdjunction₂`), and
`Sheaf.Paper.IntegralDerivedOperations`
(`integralDerivedPullback`, `integralCompletedTensor`,
`integralDerivedInternalHom`). Coefficient quotients use
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` through
`Padic.coefficientExtensionRing` and its positive-level finiteness theorem.

Edge cases checked: the finite index is represented as `n + 1`, so the stated
positive condition is enforced even at `n = 0`; the finite ring's `Finite`
instance is supplied by `Padic.finite_coefficientExtensionRing`; the zero and
identity morphisms are covered by the functor and adjunction interfaces; and the
small pro-etale site keeps object universe `u+1` and morphism universe `u`.
No coefficient flatness or equality of these site universes is added.

Searches made before writing: `msearch.py ... leanfinder` for derived pullback,
tensor and internal Hom on pro-etale sheaves (only underived/fixed-scalar hits);
`msearch.py ... loogle` for `totalLeftDerived`, `totalRightDerived`, and
monoidal closed derived operations (only generic derived-functor declarations);
`rg` in `WeilConjectures/` and `lean/Sheaf/` for
`def-weil-derived-pullback-tensor-hom`, `derivedPullback`, `derivedTensor`, and
`derivedHom` (found the published finite tensor/Hom and integral operation
interfaces used above, but no declaration of this complete package).

The maintenance repair note was read. In particular, the package exposes finite
 tensor and Hom together with the canonical parameterized adjunction, rather than
a pullback-only alias. The finite tensor/Hom are the same small pro-etale site
construction and the integral operations are the normalized reductions; no
extra hypothesis or arbitrary comparison is introduced.

## Earlier second reading (a previous round; superseded)

I reread the node and module independently. The prime, coefficient-extension,
and scheme/morphism binders are all explicit. The finite clause uses positive
levels `n+1`, and the pullback, tensor, internal-Hom, and tensor--Hom adjunction
are each present. The integral clause has pullback, completed tensor, and
completed internal Hom with the recorded tower categories. The imports expose
the scalar-localized and common-stage coefficient categories named by the node.
The declaration compiles with `autoImplicit false`; no mismatch or omitted
hypothesis was found.

## Second reading by Q118

This reading supersedes the earlier second reading, which did not check the rational
or common-stage operations and accepted a fixed-scalar finite tensor/Hom in place of
the node's intrinsic ones. I read the node's complete current statement, its blueprint
source at sec-smooth-purity/sk-def-sf-operations/order 1467, Stacks
sites-cohomology.tex (06YL/06YV and 08J7--08J9), and proetale.tex (099N), together
with the maintenance repair note and the invalidated finite-Hom binding. The source's
finite operations concern ambient module categories. Its integral operations use
completed coefficients and ambient resolutions. Neither the source nor this node
asserts finite-level constructible preservation, or constructibility of every integral
internal Hom. The node's own statement is correct; no statement correction is made.

My statement checklist, with the actual Lean rendering and verdict, is:

1. Prime ell; finite E/Q_ell; its valuation ring, uniformizer and positive quotients.
   The binders are `l`, `[Fact l.Prime]`, `E`, `[Field E]`, `[Algebra ℚ_[l] E]`,
   `[FiniteDimensional ℚ_[l] E]`. `finiteCoefficientRing` abbreviates the existing
   `Padic.coefficientExtensionRing`, and every finite operation uses exponent `n+1`.
   The valuation ring and uniformizer in the rational formulas are the existing
   `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`.
   Verdict: same objects, every positive exponent, no new coefficient construction.
2. Schemes X,Y, ell invertible, and arbitrary f:X→Y. The pullback binders are
   `{X Y : Scheme.{u}} (f : X ⟶ Y)`, and each constructible pullback has
   `[∀ x : X, Invertible (l : X.residueField x)]` and the corresponding Y binder.
   Constructible tensor has the same binder on W. Hom is defined on its explicit
   permitted-pair domain. Ambient finite and scalar constructions are available more
   generally and impose no extra geometric assumptions. Verdict: the stipulated
   locus is covered without quasi-compactness, Noetherian, smoothness or finiteness
   assumptions on f or on the schemes.
3. Small pro-etale sites and intrinsic constant-ring module derived categories.
   Finite tensor's displayed type is `proEtaleDerivedCategory W A ×
   proEtaleDerivedCategory W A ⥤ proEtaleDerivedCategory W A`. I opened this
   declaration and `normalizedDVRDerived`/`integralCoefficientSheaf`; they are the
   same standard localization of sheaves of modules over the actual constant
   quotient ring sheaf. The site has object universe u+1 and arrow universe u.
   Verdict: actual intrinsic categories, without a site-universe equality.
4. Finite pullback along the canonical constant-section coefficient isomorphism,
   exact and computable termwise. `finiteDerivedPullback` uses the existing
   `Scheme.sfIntrinsicDerivedPullback`, supplying only the known finiteness of the
   positive coefficient quotient. I read its signature and exact ordinary inverse
   image construction. Verdict: the recorded canonical intrinsic inverse image,
   not an arbitrary functor or a fixed-scalar stand-in.
5. Finite derived tensor and its K-flat normalization, functoriality and canonical
   resolution comparison. `finiteIntrinsicClosed` uses the newly landed
   `coefficientDerivedSystemEvaluationCalculus`; `finiteIntrinsicDerivedTensor` is
   its finite closed tensor on the intrinsic category. `finiteIntrinsicTensorModels`
   exposes `CoefficientTensorModels`: a natural comparison from localized total
   tensor on K-flat pairs, with `uncurry_model` fixing its evaluation on ordinary
   sheafified tensor generators. I read both structures and the calculus theorem.
   Verdict: the actual derived tensor and normalized representative maps; finite
   constructibility preservation is not required or asserted.
6. Finite internal Hom, ambient K-injective resolutions, evaluation and currying.
   `finiteIntrinsicDerivedInternalHom` is literally the existing
   `coefficientFiniteInternalHom`, hence `derivedInternalHomOfUniverses` over the
   finite coefficient sheaf. `finiteIntrinsicEvaluation` and
   `finiteIntrinsicTranspose` are this closed structure's counit and Hom bijection.
   The tensor model fixes that transpose against the recorded K-injective Hom
   comparison. Verdict: the existing intrinsic Hom with canonical evaluation and
   currying, not merely an unspecified adjunction.
7. Repair-note consumer for A_(E,m+1)→A_(E,n+1), n≤m. The declaration
   `finiteIntrinsicReductionHom` uses the *same* selected calculus's
   `quotientCalculus` and `coefficientFiniteQuotientHomComparison`. I opened the
   latter: it is `coefficientBaseChangeHom`, namely the unique closed transpose of
   reduced evaluation after the inverse tensor comparison. Its quotient calculus
   fixes the ordinary unit, derived unit, and tensor comparison on K-flat pure
   tensors (`ordinary_unit`, `unit_model`, `tensor_model`). Thus this consumer works
   on the recorded intrinsic Hom for every quotient, including nonflat quotients,
   with independent small-site universes and with no extra adjunction hypothesis.
   Verdict: this supplies the concrete reduced-evaluation transpose missing from
   the first worker's delivery. Existing etale/pro-etale comparisons are untouched.
8. Integral categories are the existing `sfIntegralConstructibleCategory`, full
   subcategories of the actual completed-ring derived category. I read
   `sfIntegralConstructible`: derived completeness, constructible finite reductions,
   and one common bounded cohomological interval. Verdict: the advertised intrinsic
   bounded constructible category, without a finite-field datum or termwise
   constructibility assumption on resolutions.
9. Integral pullback and completed tensor are the normalized strict finite-reduction
   Roos descents. `constructibleIntegralPullback` and `constructibleIntegralTensor`
   are `ObjectProperty.lift` restrictions of `integralDerivedPullback` and
   `integralCompletedTensor`, with preservation supplied by the actual
   `integralOperations_preserve_constructible`. I read the ambient operations and
   their representative comparisons and preservation theorem. Their data are the
   original same-representative reductions, strict transitions and diagonal shifted
   cone construction. The maps of each restriction are the ambient maps. Verdict:
   actual restrictions of exactly the recorded constructions, available for either
   W=X or W=Y.
10. Integral Hom is ambient derived Hom, used as a constructible operation only on
    permitted pairs. `constructibleIntegralHomPairs` says precisely that the
    ambient `integralDerivedInternalHom` output is `sfIntegralConstructible`.
    `constructibleIntegralHom` lifts that ambient functor on the full subcategory.
    The first variable is opposite. Verdict: exactly the node's restriction, without
    a false assertion that every constructible pair has constructible Hom.
11. Rational categories are the recorded raw scalar localization, with unchanged
    integral objects. The three `rationalDerived..._existsUnique` specifications
    prescribe those integral output objects and every morphism map. Pullback is
    additive and sends `c ⊗ u` to `c ⊗ f*(u)`. Tensor is bilinear and sends the two
    pure tensors to `(c*d) ⊗ tensor.map (u,v)`. Hom uses the permitted rational-pair
    full subcategory and sends the contravariant/covariant maps to
    `(c*d) ⊗ Hom.map (a.op,b)`, with the displayed source and target in the correct
    order. Coefficients are written in `Localization.Away varpi`, the implementation's
    coefficient-first tensor coordinates; the existing `sfRationalCoefficientEquiv`
    canonically identifies this with E. Verdict: all the node's rational object,
    balancing, linearity, variance and additive-extension clauses, with no Karoubi
    completion.
12. Canonical scalar comparisons must precede common-stage descent. The old
    dependency's `IntegralScalarOperations.Comparisons` asserted existence of
    coherent operation isomorphisms, but did not normalize the pullback/tensor/Hom
    components on representatives. Its literal coefficient subfields also lived
    in the scheme universe. Selecting these existential isomorphisms would not
    define the canonical operation. Under §1(B), the supplementary dependency module
    `IntegralOperationsScalarComparisons` now defines the finite generator maps,
    strict tower maps, and both Roos coordinates, then uniquely localizes them.
    The ordinary Hom map is the actual transpose of extended evaluation using a
    pure-tensor-normalized ordinary derived scalar tensor comparison. Completion
    maps are uniquely fixed by the existing quotient-completion chain map.
    `scalarPullbackCompleted`, `scalarTensorCompleted` and `scalarHomCompleted`
    conjugate by those normalized completion isomorphisms, using the inverse
    first-variable Hom comparison. Complete Hom is not required to be constructible;
    `scalarInternalHom_complete` and `scalarHomCompleteInputs` retain that full
    dependency scope. Ordinary naturality, coefficient-tower and unit identities
    are stated explicitly. Verdict: prescribed canonical maps, not arbitrary
    isomorphisms or data chosen from bare nonemptiness.
13. Rationalized comparisons are the ones used in common-stage formulas.
    `integralPullbackScalarComparison`, `integralTensorScalarComparison` and
    `integralHomScalarComparison` lift precisely those completed ambient maps.
    Their rational comparisons are uniquely specified by the localization of
    every integral component. Permitted Hom pairs remain permitted after extension
    by an *integral* isomorphism, not by inferring integral constructibility from a
    rational isomorphism. Verdict: the comparisons actually come from the repaired
    scalar dependency, followed by rationalization as the node requires.
14. Algebraic closure Omega and finite coefficient fields. The common-stage section
    uses `Ω : Type v` independently of `Scheme.{u}`, `Index l Ω`, and the existing
    equivalent small models `Coefficient.{u} l Ω E`. The category is exactly
    `generalAlgebraicallyClosedConstructibleCategory`, whose actual upstream
    `StageSystem.PairCategory` objects and quotient morphisms I opened. Verdict:
    arbitrary algebraic closure, actual finite subfields and actual existing pair
    category, with no extra algebraic-closure universe restriction.
15. Common-stage object formulas. `commonStagePullbackObject` retains the stage.
    `commonStageTensorObject` uses the actual `finiteCoefficientCompositum` and
    extends both inputs to it before tensoring. `commonStageHomObject` does the
    same with Hom, on exactly `commonStageHomPairs`, which tests constructibility
    of the integral Hom at that compositum. Verdict: all three literal pair
    formulas, no replacement by an ambient realization or a retract completion.
16. Common-stage morphisms and independence. Each of the three
    `commonStageDerived..._existsUnique` specifications gives the functor's object
    formula and its image of *every* common-stage representative. The formula is
    source theta.hom, the rational operation over L applied to the representative,
    then target theta.inv. Tensor uses a common L above both endpoint composita;
    this is exactly a field containing the four input fields. Hom has an arrow
    from the target first input to the source first input, applies `.op`, and a
    covariant second arrow. Its `commonStageHomComparison` uses the inverse first
    scalar associator. The selected stage system is opaque: its transitions are
    propositionally, not definitionally, the published rational scalar functors.
    `operationStageTransitionIso` uses the recorded equality of those functors,
    and the three common-stage comparisons include that identification and the
    actual scalar associators. Verdict: typed canonical conjugation on the existing
    quotient, for every representative, hence compatible with enlargement,
    eventual equality, identities and composition. The complete construction proofs
    are in the existence theorem docstrings.

Edge cases: `n=0` in Lean means positive coefficient exponent one, and every positive
exponent occurs. The quotient consumer includes equal levels and arbitrary successive
or nonsuccessive quotients. Zero objects, zero maps, and identity maps are covered by
the functor and normalized closed structure interfaces. Empty schemes have vacuous
invertibility binders and the same module/derived constructions. There is no input
index set required to be inhabited; the coefficient index is the existing nonempty
directed finite-subfield system, with its recorded base-field object. No residue
characteristic is fixed beyond the stated invertibility of ell; ell=2 is included.
K-flat resolutions can be unbounded ambient complexes and need not be constructible
termwise. Site objects u+1 and morphisms u stay independent; Omega's universe v is
also independent. The small coefficient models follow the existing constructible
category size convention, rather than forcing the site's two universes equal.

Independent searches: I used LeanFinder for "Derived tensor internal Hom canonical
equivalence constant ring sheaf modules" and "scalar extension derived internal Hom
finite free tensor evaluation"; hits were ordinary ModuleCat tensor-Hom and scalar
adjunctions, not this four-level definition. Loogle on
`CategoryTheory.ParametrizedAdjunction` found the generic adjunction transport API;
Loogle on `CategoryTheory.ScalarLocalization` found no Mathlib declaration under that
name (the localization is project-specific). I also searched with `rg` for tensor,
internal Hom, closed structures, scalar comparisons and common-stage operations in
Mathlib, the slopmaster2 `WeilConjectures` tree, the current side framework and
`lean/Sheaf`. This found partial fixed-scalar upstream operations, the normalized
integral descents, the raw rational/common-stage categories, and the newer intrinsic
coefficient evaluation calculus and tensor-Hom models, all of which I opened. No
existing declaration supplies these constructible rational/common-stage operation
maps. The new names `commonStageDerivedPullback`, `commonStageDerivedTensor`,
`commonStageDerivedInternalHom`, `scalarPullbackChain`, `scalarTensorChain` and
`scalarHomOrdinary` have no collision in those trees. The earlier worker's fixed-scalar
transport aliases were removed in favor of the already recorded intrinsic Hom and
normalized intrinsic coefficient calculus.

Mismatches repaired: missing intrinsic finite tensor/Hom/evaluation; missing quotient
transpose consumer; omitted invertibility binders; absent integral constructible
restrictions and permitted-Hom domain; entirely absent rational morphism maps;
entirely absent common-stage object and representative maps; underdetermined and
universe-specialized scalar comparison dependency; missing identification between
opaque recorded stage transitions and rational scalar functors; and incomplete
source/blueprint docstrings. No correct dependency definition or mathematical node
statement was rewritten. The old worker report remains above as required, but its
claims of a complete package and of a quotient at exponent n+1 were not accurate.

Every newly postponed theorem is named, listed in its owning node's
`lean.declarations`, and has the source/blueprint marker and a complete construction
proof in its docstring. Choices are made only from the normalized closed universal
property or uniquely prescribed localization, component, object and morphism formulas.
There is no definition whose data is sorry. All new proofs remain postponed; this is
stage 2. No new definition node, private category copy or target statement change is
needed.

## Dependency modules

`lem-pur-integral-operations-scalar-extension`: the recorded module remains imported
unchanged. Its existential comparison predicate did not expose the canonical
representative normalization needed by the owning definition, and could not directly
serve the independent-universe small coefficient models of the recorded general
common-stage category. The supplemental module
`Sheaf.Paper.IntegralOperationsScalarComparisons` repairs this interface under §1(B).
I checked it against the dependency statement and its source proof steps 1--9: finite
free coefficients, actual completed ring maps, cofinal uniformizer filtrations,
strict finite generator maps, product-cone maps with both coordinates fixed, localization,
ordinary tensor associativity, evaluation-transposed Hom, completion on all complete
inputs, and naturality/tower/unit compatibility. It strengthens the usable canonical
interface without changing the dependency's mathematical statement or any other node
field. The owning node also cites the already landed normalized coefficient tensor-Hom
model and coefficient evaluation calculus; their dependency paths do not lead back to
this item.

A final declaration-name search checked all 88 delivered names across Mathlib, both
source trees, and the side library. The only basename match was
`AlgebraicGeometry.Scheme.finiteCoefficientRing` in
`ContinuousCoefficientImmersionRestriction`: I opened it. It is a lifted bundled
`CommRingCat` at positive exponent n+1, whereas this module's existing
`WeilConjectures.finiteCoefficientRing` is only an abbreviation for the unlifted
published `Padic.coefficientExtensionRing` at exponent n. There is no qualified-name
collision or new quotient construction; neither declaration is the four-level
operation package.

Validation: the prescribed `scompile.py Q118 def-weil-derived-pullback-tensor-hom`
compiled both delivered sibling modules separately and cleanly. Final library checks
were 32.8 seconds for `IntegralOperationsScalarComparisons` and 47.1 seconds for
`DerivedPullbackTensorHom`, within the unchanged 60-second limit. There were no errors
or non-sorry warnings. All theorem-header bounds and the source/target objects of
representative maps are explicit; all universes are declared and `autoImplicit` is
false. Both `lean.statement` fields are verbatim signatures from their respective
files. The item changes only `lean` and adds the two already landed coefficient-model
nodes to `stmt_deps`; the dependency node changes only `lean`.

Resumed second reading, 2026-10-17: retained this review and reread both complete
delivery modules against the current node records, blueprint source, Stacks
06YL/06YV/08J7/08J9/099N, and the archived maintenance binding. Reopened the current
intrinsic pullback, coefficient closed structure and tensor models, quotient-Hom
transpose, normalized integral operations, constructible predicate, raw rational
localization, general common-stage system, and old scalar-comparison predicate.
The old predicate still lacks representative normalization for its operation
comparisons; the supplemental module remains necessary. The existing upstream
fixed-scalar and condensed module-object tensor/Hom signatures use different
presentations and do not replace this intrinsic four-level interface. No further
Lean mismatch was found, and no Lean file or mathematical statement was changed
in this resumption. Both recorded main signatures occur verbatim in their files;
all 88 declaration names remain accounted for. The item/dependency field deltas
are still exactly those described above.

Repeated independent searches with Loogle `CategoryTheory.ParametrizedAdjunction`,
LeanSearch "derived tensor product internal Hom sheaves of modules coefficient
localization", LeanFinder "Canonical derived internal Hom tensor scalar extension
completed coefficients common finite extension category", and `rg` on Mathlib,
the upstream project and the current side library. Results are generic adjunction,
ordinary module localization/evaluation, and the partial presentations already
reviewed; no existing complete operation package or collision was found. The
positive-exponent, equal-level quotient, empty-scheme, zero-object, Hom-variance,
and independent site/algebraic-closure universe checks above still apply.
