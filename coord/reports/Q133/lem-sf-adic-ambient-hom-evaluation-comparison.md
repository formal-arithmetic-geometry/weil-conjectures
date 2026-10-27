## Worker report

The module `Sheaf.Paper.AdicAmbientHomEvaluationComparison` states
`WeilConjectures.AdicQbarRealization.AmbientHomEvaluation.adic_ambient_hom_evaluation_comparison`.
Its proof is the only `sorry` in the delivered module. The statement returns `Laws`,
a Prop structure whose fields spell out every conclusion, including equalities of
specified maps rather than existence of unspecified internal-Hom isomorphisms.
All helper definitions have actual data. No definition node or dependency module
is replaced, and the item's informal statement and proof are unchanged.

Hypothesis correspondence:

* `D : FiniteFieldDatum.{u}` supplies the fixed finite field and its algebraic closure;
  `l`, `[Fact l.Prime]`, and `hl : l ≠ D.p` supply the coefficient prime. The fixed
  algebraic closure of the coefficient field is the existing `PadicAlgCl l`.
* `T : Over (Spec (CommRingCat.of D.k))`, `[IsSeparated T.hom]`,
  `[LocallyOfFiniteType T.hom]`, and `[QuasiCompact T.hom]` say exactly that T is
  separated and of finite type over k. The invertibility instance is the standard
  encoding of l invertible on this geometric scheme, a consequence of l ≠ p.
* The site's objects remain `T.left.ProEt : Type (u+1)` with arrows in universe u.
  The module section universe is u+1. No object/morphism universe equality is imposed.
* `R : LocallyFiniteAdicRealization.Realization l T.left` is the existing data interface
  for the assumed normalized realization: `R.J` is additive, triangulated and fully
  faithful with precisely the bounded locally finite free constructible image;
  `R.coefficient` supplies the integral completion, finite quotients, rational
  localization and inclusion; `R.integral` identifies its restrictions to integral
  representatives; `R.common_field` fixes transition comparisons by completion and
  balanced scalar multiplication. It is a parameter, not a chosen existence result.
  Thus the hypothesis is an exact equivalence with specified balanced finite-stage
  comparisons, represented on the existing native module presentation.
* The canonical section-module presentation is `sectionFunctor l T.left R`;
  `presentation : ... .IsEquivalence` identifies the two presentations. It asserts
  the canonical internal/sectionwise module equivalence, not any extra condition on
  the scheme or the coefficient sheaf. The ordinary functor called rho in the node
  is `ordinary l T.left R` (R.J followed by this exact derived presentation).
* `ring`, `modules` and `ambientHom` are existing declarations, not copied definitions.
  The ring is the section-ring reconstruction of the native finite-subextension-valued
  continuous coefficient. In particular the module does not substitute all continuous
  functions into the valuation-topological algebraic closure or a discrete constant ring.
* The raw categories are `sfRationalConstructibleCategory` and
  `generalAlgebraicallyClosedConstructibleCategory`, unchanged. A permitted pair is
  `P : (commonStageHomPairs l (PadicAlgCl l) X).FullSubcategory`; its entries are M,N,
  and H is `(commonStageDerivedInternalHom l (PadicAlgCl l) X).obj P`.
* `A : TensorInput l T.left R` packages the symmetric strong tensorator hypothesis:
  ambient closed structure, specified K-flat model and signed monoidal coherence,
  natural tensorator, coefficient unit, associativity, both unitors and symmetry.
  Its tensorator has orientation rho H tensor rho M -> rho(H tensor M).
  The existing `At` cannot be used as a hypothesis here because its last field
  **assumes the desired Hom-isomorphism conclusion**. `TensorInput` is the input-only
  helper of this lemma; it assumes no such conclusion and introduces no second tensor.
* `source : PodPartialClosed ...` supplies the assumed natural additive transpose
  equivalence for every test object and permitted pair. Its evaluation is the inverse
  transpose of the identity, so it is precisely the right evaluation. The hypothesis
  `source_normalized : PodCommonTransposeNormalization ... source` says that every
  inverse transpose is the finite rational transpose conjugated by the **recorded**
  stage tensor and rational Hom comparisons. This retains all localized morphisms and
  is the given finite rational scalar compatibility, without a site-perfectness input.

Conclusion correspondence (the fields of `Laws`):

* `comparison` is defined to be `A.closed.transpose` applied to
  `realizedEvaluation`, which is exactly mu followed by rho(e).
* `bounded` states Q belongs to the existing transported
  `AdicQbarRealization.boundedConstructible` predicate. This is bounded cohomology
  with finite locally closed stratifications and locally finite free restrictions,
  transported through the exact section-module presentation. On the quasi-compact
  scheme T, the upstream affine-local convention is the finite global convention.
* `isIso` states invertibility of this very `comparison` in the ambient unbounded
  derived category; it does not merely give an isomorphic object.
* `postcomposition` states bijectivity of postcomposition with c on every realized
  constructible test object. `transpose` states the required pointwise equality:
  taking a:L->H through evaluation, rho and ambient transposition gives rho(a) >> c.
  Since full faithfulness and source transposition are bijections, this identifies
  exactly the bijection in the node, including every arrow in the directed Hom colimit.
* `naturality` quantifies over all morphisms of the full permitted-pair subcategory.
  Its first component is contravariant and its second covariant.
* `evaluation` is tensor(c,id) >> ambient evaluation = mu >> rho(e).
* `signed_symmetry` is the corresponding left-evaluation identity, with the actual
  source braiding and actual ambient braiding. `A.coherence` fixes their native
  complex normalization, including the Koszul sign (-1)^(pq).
* `finiteM`, `finiteN`, `finiteH` are actual realized finite rational objects at F.
  `gammaM` and `gammaN` are rho applied to `stageSystem.isoToStage`.
  `gammaH` additionally applies `commonStageHomComparison`, including the specified
  rational Hom scalar map and inverse first-variable scalar associator. The literal
  object equality in `gammaH` is obtained from the owning functor's uniqueness
  specification; no new object or unrelated comparison is selected.
* `finiteEvaluation` uses the actual rational evaluation, first the realization
  tensorator and then inverse `stageTensor` to reach its domain. `finiteComparison`
  transposes this evaluation. It is not defined by transporting an arbitrary chosen
  internal-Hom isomorphism. `finite_evaluation` states the normalized pairing square;
  `finite_comparison` is its transposed comparison square with c.
* `homTransition` uses gammaH at the two stages, so includes the prescribed rational
  Hom comparison; `ambientTransition` uses RHom(gammaM inverse,gammaN).
  `extension` equates c_G after the H transition with the ambient transition after c_F.
  `tower` equates direct and successive H and ambient transition maps for every
  F <= G <= K. `identity` says both transitions at F=F are the actual identity maps.
  Together these are the direct/successive/identity equations for the specified c's,
  under the balanced scalar maps already retained by R and the source normalization.

Dependency declarations read and used:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and its inverse-limit coefficient interface.
* `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing` and `padicAlgClRingObj`.
* `Sheaf.Paper.CompletedCondensedCoefficients`: `completedCoefficient`,
  `completedCondensedIntegral`, rational/algebraic-closure comparisons. Publicly
  imported by the existing native data interface.
* `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `inclusion`, `stageSystem`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`.
* `Sheaf.Paper.DerivedPullbackTensorHom`: common/rational tensor and internal Hom,
  permitted pairs, `commonStageHomPairAtStage`, `commonStageHomComparison`, and
  the unchanged-object specification of the common Hom functor.
* `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` reexports the recorded
  generic `derivedInternalHomOfUniverses` actually used by `ambientHom`.
* `Sheaf.Paper.NativeAdicRealizationData`: `ring`, `modules`, `ordinary`,
  `sectionFunctor`, `boundedConstructible`, `ambientHom`.
* `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization`: `Realization`, including
  `CoefficientPresentation`, exactness, image and balanced common-field normalization.
* `Sheaf.Paper.DerivedAutomorphismHomEvaluation`: `PodPartialClosed`, its evaluation,
  `PodCommonTransposeNormalization` and `podRationalClosed`.
* `Sheaf.Paper.CommonStageInclusionTensorComparison`: `stageTensor`.
* Proof imports retain the recorded native tensor, tensor-Hom adjunction, bounded
  constructibility predicate, and module-object closed tensor/constructible setting.
  `lem-sf-adic-finite-realization-cocone` and `lem-sf-adic-common-stage-hom-transpose`
  have no recorded Lean module. The recorded
  `Sheaf.Paper.BoundedConstructibleHomFiniteness` source is absent both locally and
  under `scompile.py --source` (which returned "Module source unavailable"). No
  nonexistent module is imported; this is a proof-only input, not needed to state
  this lemma. The complete seven-step proof and its original DAG uses are retained
  in the theorem docstring and node, for stage 3.

Edge cases: the empty scheme permits empty strata; no nonemptiness or connectedness
is assumed. Zero M,N,H and zero finite ranks remain permitted. Test L is arbitrary
in the actual common-stage category. Finite stages may repeat; identity and repeated
steps in towers are included explicitly. Coefficient extensions may be ramified.
No perfectness, dualizability, extra Tor amplitude, completeness on the ambient Q,
or equality of the site object and morphism universes is introduced. Every parameter
and universe is bound explicitly with `autoImplicit false`.

Sources read: BS PDF Lemma 3.4.11 (p.22) gives the completed adjunction as the ordinary
adjunction followed by the completion universal property; Remark 6.8.15 (p.62)
states that the ambient operations restrict under the stated finiteness conditions.
HRS Theorem 7.7, Lemma 7.9 and Remark 7.10 give the rational/common-field comparison
and six-functor context. The map normalization and two-test-object inverse argument
are the agent-written seven steps in this node, not claimed as a verbatim theorem
of those papers. The current blueprint directory was searched, not an old snapshot.

Searches actually run with msearch.py (Q133, this item):

* leanfinder: "A fully faithful monoidal realization identifies the evaluation
  transpose with ambient internal Hom" -> 8 hits, including `expComparison_ev`,
  `ihom.ev`, and groupoid functor-category evaluation lemmas; no exact adic statement.
* loogle: "CategoryTheory.ihom, CategoryTheory.expComparison" -> 10 hits for the
  Cartesian closed comparison API. This concerns Cartesian tensor, not the stated
  permitted-pair adic internal Hom or its finite coefficient maps.
* grep: `internalHom.*[Ee]quivalence|[Ee]quivalence.*internalHom` in CategoryTheory
  -> 0 hits.
* leansearch: "Evaluation transpose internal Hom comparison for constructible adic
  realization is invertible and respects coefficient towers" -> 8 hits on ihom,
  vector-space transpose/contraction, matrix invertibility and adic completion;
  none states this lemma.
* Local rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id found only the
  parent theorem's proof docstring. Searches for ambient Hom and adic realization
  found the existing native data interface, whose At includes the conclusion and
  therefore cannot be used circularly to prove this item.

Only the lean binding and additions of four **landed definition interfaces** to
stmt_deps are delivered. These dependency additions have no path back to the item
(the source dependency graph was read and checked). No statement correction or
STATEMENT-DISPUTED flag is needed.

## Second reading by Q133

The dispatcher explicitly prohibits starting other agents. This section records the
worker's final clause-by-clause reread, not an independent-agent review; the
maintainer's independent review remains the review specified by the assignment.

The reread checked the orientation of mu, right evaluation and both signed swaps;
that c is defined rather than existentially chosen; that boundedness precedes the
two-test-object invertibility argument; that all pair morphisms are quantified; that
finiteEvaluation uses rational evaluation itself; that gammaH includes rational Hom
comparison; that the first coefficient argument uses the inverse; and that identity
and tower laws are equations of maps. The circular At.hom_isIso interface was excluded
from the hypothesis. Explicit helper result types were added to prevent repeated
elaboration of the entire scalar-transition implementation. No mathematical clause
was removed for elaboration speed.

Validation: the complete delivered module compiled cleanly via scompile.py in both
sandbox (14.5 s) and library (18.2 s) modes. Every definition has data, and the
only postponed proof is the named main theorem. All lines are at most 100 characters.
