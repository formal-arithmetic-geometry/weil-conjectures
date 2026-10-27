## Worker report

The module `Sheaf.Paper.SfPackageCoefficientDomains` states this node in seven public
named theorems, all with proof `sorry`. It introduces no definitions and does not change
the node's statement, proof, or proof dependencies. The repair adds the two existing
definition owners requested by the maintainer to `stmt_deps`. The node's
`lean.declarations` lists every theorem; the primary signature is copied verbatim.

Sources read: the current `literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-package/prop-functor-package.md` and its proof, especially the opening domain
paragraph and clause (1). Also read the target's complete accepted nine-step proof,
its nine statement-dependency nodes and their recorded source declarations/docstrings,
and the resolved stage-1 repair note. The latter asks to preserve the accepted split;
this delivery leaves it unchanged. The CompactObject example is now a withdrawn module
with no declarations; the current operation-datum modules supply the active conventions.

Hypotheses and clauses, matched explicitly:

- The global algebraic closure of a finite field, characteristic p, and prime l different
  from p are `D : FiniteFieldDatum` and `C : D.CoefficientDatum`; the latter contains
  `prime`, `different`, and the algebraic closure `Qbar` of `Padic C.l`.
- The finite coefficient field is `E : Type u`, `[Field E]`, `[Algebra (Padic C.l) E]`,
  `[FiniteDimensional (Padic C.l) E]`. The valuation ring, fixed uniformizer and quotients
  are the dependency's `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionUniformizer`, and `Padic.coefficientExtensionRing`.
  Index `n` means exponent `n+1`, including exponent one and every positive exponent.
- The operation datum is the explicitly bound `SixFunctorOperationDatum D C E
  (n+1) (Nat.succ_pos n)`. Clauses which only need canonical ambient operations
  retain it as `_operations`/`_S`; no arbitrary maps or extra normalization hypotheses
  replace those operations.
- `X Y : SixFunctorSpace D` are the existing full-subcategory encoding of finite-type
  schemes over `Spec D.k`. Their finite-type property contains both locally finite
  type and quasi-compactness, with the same structure map. `[IsSeparated X.obj.hom]`
  and `[IsSeparated Y.obj.hom]` give separation over k. `f : X ⟶ Y` retains the
  k-morphism condition, and its three morphism instances give separated finite type.
- The finite category is the full subcategory defined by `finiteTorConstructible`.
  `sfPackageFiniteDomains` asserts preservation by `finiteDerivedPullback`,
  `finiteIntrinsicDerivedTensor`, `proEtaleConstantDerivedDirectImage` and
  `sfIntrinsicCompactSupport`, for every compactification. These are the canonical
  intrinsic pro-etale constructions normalized by the operation datum.
- Its third conjunct gives internal-Hom preservation in both finite-Tor inputs,
  using `finiteIntrinsicDerivedInternalHom`. Tor intervals are the recorded
  `HasProEtaleTorAmplitude`, which already includes the ordering a ≤ b.
  With `d : ℕ` and `topologicalKrullDim X.obj.left ≤ (d : WithBot ℕ∞)`, the output
  endpoints are exactly `c - b - 2 * (d : ℤ)` and `e - a + 2 * (d : ℤ)`.
  `IsFiniteCoefficientSitePerfect` alone guards both `IsIso` of the canonical
  `ringedSiteDualEvaluation` and the sharp interval `[c-b,e-a]`. The dual is Hom
  into the coefficient unit; the map is the transpose of
  `(L tensor K-dual) tensor K ≅ L tensor (K-dual tensor K) → L tensor unit ≅ L`.
  This is the braiding-free order of the canonical comparison in
  `prop-sf-dualizable-hom`, rather than existence of an unspecified isomorphism.
  No site-perfectness premise is imposed on the general Hom clause.
- `sfPackageFiniteHomReduction` uses `n m : ℕ`, `h : m ≤ n`, corresponding to
  n+1 ≥ m+1 ≥ 1. `FiniteHomEvaluation` states the evaluation square and uniqueness
  of its transpose for the actual quotient tensor comparison.
  `IsIso (finiteIntrinsicReductionHom ... h K L)` is the displayed finite Hom
  coefficient comparison, for all finite-Tor constructible K and L.
- Integral objects are exactly `sfIntegralConstructibleCategory`, the recorded
  complete integral objects with constructible positive reductions bounded in a
  single cohomological interval. `sfPackageIntegralDomains` states preservation
  under `integralDerivedPullback` and `integralCompletedTensor` (the completed
  operations), and `sfCompletedDerivedDirectImage`. For compact support it uses
  the actual terms `sfCompactSupportTerm`, quotient/restriction-of-scalars
  transitions `sfCompactSupportTransition`, and any vertex M satisfying
  `IsDerivedLimit`; M is then `sfIntegralConstructible`. The `HasProduct` binder
  is the product needed to type this Roos presentation; the canonical countable
  product construction supplies it, so it does not restrict the geometric inputs.
  This asserts ambient constructibility rather than repeating a bundled output's
  subtype property.
- The last integral conjunct asserts membership of the actual ambient
  `integralDerivedInternalHom` for every pair and invertibility of
  `integralHomReductionComparison` for every positive quotient. The latter's
  definition is the transpose of changed evaluation, with the canonical inverse
  tensor comparison; its endpoints are exactly the two sides of the integral
  formula. No perfectness premise is introduced.
- `sfPackageFieldHomDomains` asserts that `constructibleRationalHomPairs` and
  `commonStageHomPairs` hold for all bounded constructible pairs. These are the
  existing domains of the recorded Hom functors, so this extends their actual
  permitted-pair interfaces to precisely the entire categories in the statement.
- `sfPackageFieldValues` identifies rational pullback/tensor with localization of
  their completed integral object values. It identifies rational Hom with the
  localization of `constructibleIntegralHom`, and its next clause states `HEq`
  between rational evaluation and localization of the normalized completed
  integral evaluation. `HEq` only accommodates the published object equalities;
  no evaluation equation is weakened to existence of an isomorphism.
  Rational direct image is the localization of `S.higher.integral.direct`;
  rational compact support is `sfRationalCompactSupportValue`.
  At the algebraic closure the outputs are `commonStagePullbackObject`,
  `commonStageTensorObject`, `commonStageHomObject`; tensor and Hom use the
  compositum of the input fields, so mixed coefficient stages are included.
  The direct-image value on every finite-stage inclusion is the inclusion of
  the recorded rational direct image, and compact support is exactly
  `sfQbarCompactSupportValue` on every finite integral representative.
  The instance lambda is immediately applied to the explicit
  `sfStabilityResidueInvertible D C.l C.different` constructions; it adds no
  invertibility hypothesis and introduces no local instance or statement `let`.
- `sfPackageScalarExtensionExact` treats every finite extension `ι : E →ₐ[Padic C.l] F`.
  It concludes existence of the scalar functor's shift comparison and
  `Functor.IsTriangulated` for that comparison, i.e. exact triangulated scalar
  extension; the choice is a conclusion, not a hypothesis.
- `sfPackageCommonStageDomains` quantifies over both separated finite-type
  schemes T,S, an arbitrary coefficient closure Ω in its own universe w, and
  every `StageSystem.CoherentExactMorphism` between their recorded systems.
  This interface contains the exact finite-stage functors, natural scalar
  comparisons, and identity/associator/shift equations. `DescentSpec F.base`
  gives exact descent, its representative arrow formula, descent of all
  compatible transformations, equality of transformations from equality of
  finite components, and identity/composition equations. The two final
  conjunctions state triangulation, idempotent completeness, and exactness
  of every finite-stage inclusion, for both common-stage categories.

Recorded statement dependencies used (all source signatures and docstrings read):

- `Sheaf.Paper.SixFunctorOperationDatum`, `WeilConjectures.SixFunctorOperationDatum`,
  and its finite, higher, normalized integral, and common-stage constructions.
- `Sheaf.Paper.SitePerfectComplex`, `WeilConjectures.IsFiniteCoefficientSitePerfect`.
- `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`
  and `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`, `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalScalarExtension`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`,
  `generalAlgebraicallyClosedConstructibleCategory`, `Stage`, `stageSystem`, `inclusion`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`, `finiteTorConstructible` and the recorded
  `HasProEtaleTorAmplitude`; the field finite-Tor category is the same constructible
  category by `finiteTorFieldCoefficientCategory`.
- `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`, defined by strict chains
  in `IrreducibleCloseds`, including the bottom dimension of the empty scheme.
- `Sheaf.Paper.IntegralHomReductionComparison`,
  `WeilConjectures.integralHomReductionComparison`, owned by the added dependency
  `def-sf-integral-hom-reduction-comparison`.
- `Sheaf.Paper.PbcDescentInterfaces`, `CategoryTheory.StageSystem.CoherentExactMorphism`,
  owned by the added dependency `def-weil-pbc-descent-interfaces`.

The comparisons and operations are reused from `DerivedPullbackTensorHom`,
`FiniteCoefficientHomChange`, `IntegralConstructibleInternalHom`, and
`DerivedAutomorphismHomEvaluation`; the descent interface is the existing
`StageSystem.Morphism.DescentSpec` of `PbcDescentFunctors`. Proof imports include
all available recorded proofs needed by the node. The proof dependency
`lem-sf-package-field-operation-realization` has no Lean declaration in the read
repository; it is only a future proof input, and no new notion is required to
state this package. It is therefore not duplicated here.

Edge cases checked: the empty scheme (dimension bottom, d=0 valid), zero complexes
(any ordered interval), exponent one, identity quotient m=n, arbitrary negative
interval endpoints, d=0 versus d>0, the absence of site-perfectness for general
Hom, identity f, all compactifications of f, E=F and the identity scalar map,
different fields of definition for two common-stage inputs, repeated stages,
and independent scheme/coefficient-closure universes in the descent clause.
No nonemptiness, smoothness, properness, extra dimension bound or site-perfectness
has been added to the unconditional clauses. No statement dispute or correction.

Searches actually run with msearch.py for Q130 and this item:

- LeanFinder: `Constructible six functor package finite Tor integral rational coefficient
  internal Hom scalar descent` returned 8 hits (Tor/Tor', light condensed monoidal
  and internal-projectivity facts). None states this constructible coefficient package.
- Loogle: `CategoryTheory.Functor.IsTriangulated` returned 12 hits, the general exact
  functor interface and elementary transfer lemmas. Used as the exactness notion;
  no package statement is supplied by it.
- Mathlib grep: `constructible.*(rational|Tor)|six.?functor|adic.*scalar` returned
  9 ordinary module-descent/adic-completion/constructible-subset hits; none matches.
- LeanSearch: `Constructible sheaf derived internal Hom coefficient change and six operations`
  returned 8 sheafHom and ordinary sheaf-Hom interface hits, not derived coefficient change.
- Project/upstream rg: `coefficient-domain-realization|package.*coefficient|Package.*Coefficient`,
  and the item id and proposed theorem names. Existing hits are distinct tower-comparison,
  Verdier-realization and descent nodes, and upstream's ordinary-etale functor package;
  none states this node on all the recorded finite/integral/raw-rational/common-stage
  domains. The existing operations and comparison notions were reused throughout.

## Repair of return 56c9422e3cd4

H2: added `def-sf-integral-hom-reduction-comparison` and
`def-weil-pbc-descent-interfaces` to `stmt_deps`, read both node records and their
recorded definitions, and imported their owning modules explicitly.

H3: replaced the site-perfect `Nonempty` isomorphism assertion with `IsIso` of
`CategoryTheory.ringedSiteDualEvaluation`, from
`Sheaf.CategoryTheory.RingedSiteDualityMaps`. Its full definition was read: it is
exactly the transpose of the associator/evaluation/right-unitor composite requested
by the return, with the coefficient unit identified by `Iso.refl`. The source is
L tensor K-dual; symmetry gives the conventional K-dual tensor L order.
The zero complex, empty scheme, exponent one and arbitrary second argument still
use this same canonical map, without additional hypotheses.

The advisory theorem-owned helpers remain reused, with explicit provenance:
`FiniteHomEvaluation` from `FiniteCoefficientHomChange`,
`sfStabilityResidueInvertible` from `FiniteTorStability`, and
`podRationalClosed` / `podIntegralClosed` from `DerivedAutomorphismHomEvaluation`.
No private copies or new notions were introduced. All other clauses are unchanged.

Compared the retained sandbox node with the current read-only live node: before
repair only `lean` differed; the returned module is not present in the current live
clone. The delivery wrapper rebases the repaired packet onto current live sources.
Validation: the prescribed `scompile.py` passed both the sandbox module (36.1 s)
and library module (26.9 s), with no errors or warnings. The seven theorem proofs
remain `sorry`, as required for stage 2. `deliver2.py --no-push` reported
`OK (dry run): commit d5ee07109b9 passes the preflight and compiles; nothing pushed`.
Final delivery repeats these checks through the authorized wrapper. No direct Git
command, global build, live-source edit, or agent delegation was performed.

## Second reading by Q130

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
