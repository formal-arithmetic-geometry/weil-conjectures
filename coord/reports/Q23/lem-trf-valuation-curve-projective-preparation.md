## Worker report

The module `Sheaf.TraceFormula.ValuationCurveProjectivePreparation` states
`AlgebraicGeometry.Temkin.valuation_curve_projective_preparation`, with exactly one postponed
proof. Six fully written proposition-valued definitions expand its clauses; they introduce
no chosen schemes or maps. The theorem docstring carries all 23 DAG proof steps and their
dependency ids. No statement correction, new node, or dependency repair was needed.

Hypothesis and clause correspondence:

1. The base is `B : HorizontalValuationBase.{u}`. Its fields give a commutative valuation
   domain `B.V`, fraction field `B.K`, `IsSepClosed B.K`, finite prime spectrum and its
   linear prime chain. The injective fraction-field algebra map realizes V as a subring
   of K; using an abstract isomorphic valuation domain adds no hypothesis. `B.T` is
   `Spec (.of B.V)` and `B.genericMap` is the actual map induced by that algebra map.
2. A T-curve is the existing `RelativeCurve p`: flatness, local finite presentation,
   quasi-compactness and quasi-separatedness, and `Scheme.IsPureDimension 1` on every
   ordinary fibre. Its pure-dimension predicate uses `topologicalKrullDim` of every
   irreducible component, including the empty scheme. Smooth generic fibre is
   `Smooth (pullback.snd p B.genericMap)`.
3. `ValuationNormalizationPreparation B` uses `(pullback.fst p B.genericMap).normalization`
   and its actual `.fromNormalization`, not an existentially selected normalization.
   `QuasiCompact` and `QuasiSeparated` needed by Mathlib's construction are existential
   conclusions. Mathlib constructs the integral closure of the target sheaf in sections
   on the generic fibre. That fibre is normal by smoothness, so this is exactly its
   integral closure in the product of its component function fields: an element integral
   over the target is integral over the generic normal rings and thus already a generic
   section. This covers reducible schemes as well as the integral normalization in
   `def-sc-normalization`. The source is required to be finite, an `EtaModification`,
   stalkwise normal, a `RelativeCurve`, and `GeometricallyReduced` over the base.
4. The same clause quantifies over every normal source `Y` and eta-modification `g` and
   concludes `∃! a, a ≫ fromNormalization = g`. It imposes no curve or integrality
   hypothesis on this general source.
5. `ValuationProjectivePreparation B` quantifies over normal affine T-curves with the
   same smooth generic fibre and produces `j : X ⟶ C`, `IsOpenImmersion j`, `j ≫ c = p`,
   `IsProjective c`, `RelativeCurve c`, `GeometricallyReduced c`, and stalkwise normal C.
   `IsProjective` is the dependency's finite-projective-space convention, not an
   arbitrary projective bundle. It requires no Noetherian base.
6. `ValuationLocalPreparation B` assumes both original curves normal and with smooth
   generic fibres and `EtaModification B.genericMap f p`. A reduced closed immersion
   `l : L ⟶ X` represents the modification locus. Its range is exactly the points
   where `f` fails to be invertible on every neighbourhood. `range l` is finite;
   `LocallyOfFiniteType (l ≫ p)`, `QuasiCompact (l ≫ p)` and finiteness of all scheme
   fibres express the stipulated meaning of quasi-finite over T.
7. For each closed point x in this range, the actual localization map
   `Spec (Localization.AtPrime (p x).asIdeal) ⟶ B.T` is an `IsOpenImmersion`.
   The existential open U contains x. Its structure morphism v factors `U.ι ≫ p`
   through that localization, and ηs factors the original `B.genericMap` through it.
   Since localization is an open immersion this ηs is uniquely fixed, not an
   arbitrary generic map. U is affine and connected, `RelativeCurve v`, and its
   restricted modification locus has x as its only closed point.
8. Over this localized base the clause produces a normal projective curve C and open j,
   together with a normal proper relative curve D and eta-modification `g : D ⟶ C`.
   Both curves have `GeometricallyReduced` structure morphisms. The square
   `IsPullback i (pullback.snd f U.ι) g j` identifies the restriction with the given f.
   On every open disjoint from the image of the original restricted locus, g is an
   isomorphism. This is identity extension up to its specified open-chart identification.
9. Every normal intermediate factorization `D → Z → C` by eta-modifications restricts
   to an eta-modification diagram over U. The conclusion explicitly includes the
   restricted intermediate curve's `RelativeCurve`, stalkwise normality, and both
   restricted eta-modification properties. No finite-presentation assumption on Z
   was added to this intermediate-diagram input.
10. `ValuationGluingPreparation B` spells out the compatible gluing clause for the chosen
    connected affine neighbourhood, with x its only closed modification point. It takes
    closed W with `x ∈ W`, `W ⊆ U` and both specified complement inclusions quasi-compact.
    The local normal intermediate curve is a relative curve over T and both maps are
    eta-modifications. The input
    `IsIso (hU ∣_ (kU ⁻¹ᵁ (U.ι ⁻¹ᵁ complement)))` is exactly invertibility on U minus W.
    The output contains normal Z, eta-modifications h and k, `h ≫ k = f`, and
    `IsPullback j kU k U.ι` with `pullback.fst f U.ι ≫ h = hU ≫ j`.
    These equations recover the specified local diagram on the entire neighbourhood
    of the inverse image of x and therefore its specified overlap isomorphism.
    h is an isomorphism above X minus W. The final implication explicitly renders
    support over generalizations, `W ⊆ {z | z ⤳ x}`. Identity on f's old isomorphism
    locus is never used as a replacement for the overlap hypothesis.
11. `ValuationMarkingPreparation B` takes an embedded generic marking `jη` with étale,
    quasi-compact structure map to Spec K. These are exactly the finite étale generic
    markings: over a field a quasi-compact étale scheme is finite étale. They include
    the generic marking of every input `MultipointedCurve`, and no marking is assumed
    nonempty. The conclusion supplies the existing `FlatClosure`: its defining ideal is
    the scheme-theoretic-image kernel, with the prescribed embedded generic fibre,
    flat finite-presentation and pure relative dimension zero. Uniqueness and
    `ClosureRestrictionStable` enforce the same actual closures on overlaps. Compatible
    eta-modification maps between models induce unique proper eta-modifications of these
    markings. Equality of ideals under restriction gives their compatible gluing.
12. `ValuationMarkedModificationPreparation B` also handles the possibly nonnormal
    ORIGINAL multipointed target P. It assumes its smooth generic curve and étale
    generic marking; for any normal eta-modification source it supplies its relative
    curve, actual generic-marking closure, and marking map back to P.D.
    `horizontalClosurePairMap ... .IsEtaModification B.genericMap` checks both maps,
    their commutative marking square, properness, schematic density and generic
    isomorphisms. Thus normalization does not lose the original marked target.
13. Normality everywhere means `∀ x, IsDomain (X.presheaf.stalk x) ∧
    IsIntegrallyClosed (X.presheaf.stalk x)`. The existing `IsNormalScheme` additionally
    requires X integral, so it would exclude disjoint and empty curves and is deliberately
    not used here. Semistability/stability in the node's final explanatory terminology
    already use `MultipointedCurve.IsSemistable`/`.Hom.IsStable`; the theorem makes no new
    semistability assertion. The completed node ring and power-series terminology are
    inherited from those existing definitions, not redefined.

Dependency declarations read and reused:

- `Sheaf.TraceFormula.ValuationHorizontalCurveModels`: `HorizontalValuationBase`, its T and
  genericMap, `RelativeCurve`, `FlatClosure`, `ClosureRestrictionStable`,
  `horizontalGenericMarkingι`, `horizontalClosurePairMap`.
- `Sheaf.TraceFormula.Modification`: `SchemeModification`, `EtaModification`, using the
  canonical slice-category base-change map and schematically dense opens on both sides.
- `Sheaf.TraceFormula.MultipointedCurve`: `MultipointedCurve`.
- `Sheaf.AlgebraicGeometry.MultipointedCurveModification`: `MultipointedCurve.Hom`,
  `.Hom.IsEtaModification`, and the existing semistability/stability terminology.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: integral
  `Scheme.normalization`/`Scheme.fromNormalization`. Their underlying general construction
  is `Scheme.Hom.normalization`/`.fromNormalization` in
  `Mathlib.AlgebraicGeometry.Normalization`, which is used directly for the normal generic
  fibre, allowing multiple components and the empty scheme.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsProjective`, `IsHProjective`.
- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`; `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` through `RelativeCurve`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback` and projections;
  geometric fibres are the recorded pullback scheme, not a set of geometric lifts.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed` together
  with `IsDomain` for the node's stalkwise normal-ring condition.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- Adic completion and multivariable power series remain the recorded `AdicCompletion`
  and `MvPowerSeries`, imported for the node's explanatory semistability dependencies.
  No new copy of either notion is introduced.

The already landed definition nodes for modifications, multipointed curves, their
modifications and pure dimension, and the landed horizontal-curve interface node are added
to stmt_deps, as permitted by brief-stage2 §5. All old dependencies and proof data remain.
Every recorded proof-dependency module is imported without `public` unless its interface
is needed by the statement. In particular the horizontal-curve module is a public import.

Edge cases checked: empty X satisfies the pure-dimension and normality predicates
vacuously and its relative normalization is empty; disconnected normal curves do not acquire
an integrality hypothesis; V may itself be a field, so normalization and modifications can
be identities and the modification locus can be empty; local preparation then has no x to
choose. Empty markings remain empty schematic closures. Finite prime chains of any rank
are allowed, including nondiscrete and non-Noetherian valuation rings. No perfection or
algebraic closedness is substituted for separable closedness. All schemes, rings and base
change maps use the same explicit ambient universe u. The gluing support W may be strictly
smaller than the modification locus, but must contain x and satisfy the stated overlap and
quasi-compactness conditions.

Searches (msearch.py, group Q23/item id; original outputs retained by that wrapper):

- leansearch: “normalization of a curve over a valuation ring with separably closed
  fraction field admits a normal projective compactification”: eight hits, including
  `Scheme.Hom.normalization`, `.fromNormalization`, `.normalizationDesc` and the relative
  normalization API. Reused these constructions; no full preparation statement.
- leanfinder: “normalization projective compactification curve over valuation ring
  separably closed fraction field modification locality”: eight hits, principally
  Weierstrass minimal/reduction results and Proj's valuative criterion; no match.
- loogle: `AlgebraicGeometry.Scheme.normalization, ValuationSubring`: zero hits;
  unknown identifier for the upstream-only normalization name.
- Mathlib grep: `EtaModification|Multipointed|valuation.*[Cc]urve` in AlgebraicGeometry:
  only three Weierstrass valuation/discriminant hits; no preparation statement.
- rg in upstream WeilConjectures and lean/Sheaf for valuation curves, multipointed curves,
  eta-modifications and schematic density: found the existing landed interfaces listed
  above, which are used. Searching the exact item id upstream found no declaration.
- rg of the theorem and six helper names in upstream, side sources and
  dag/lean_names_upstream.json: no pre-existing declaration of any delivered name.

Source verification: read https://arxiv.org/pdf/0707.3953v3, Lemma 4.4.1(i),(ii), the
locality observation following Lemma 4.2.1 and the reduction in Proposition 4.4.6. The DAG
already contains the explicit compatible-overlap and generic-étale-marking repairs; those
are preserved. No new mathematical dispute was found.

Validation: scompile.py compiled this module as both sandbox and library module, with
no errors or warnings after the unused-binder and line-width repairs. One theorem uses
`sorry`; every helper definition has its complete body.

## Second reading by Q23

I reopened the node and complete final file for a separate clause-by-clause pass. The
per-item dispatcher explicitly prohibits starting another agent, so this is a second pass
by the worker, not a claimed independent second reader; the maintainer supplies the
independent review. The pass found and repaired these concrete mismatches before delivery:
normality must be stalkwise rather than the integral-only `IsNormalScheme`; the general
normal-source factorization and restriction of intermediate diagrams must not acquire
extra curve hypotheses; the marking on normalization needs a map to the original possibly
nonnormal target, now supplied by `ValuationMarkedModificationPreparation`; and gluing is
stated in the connected affine neighbourhood of the chosen closed modification point.
The numbered correspondence above records the final checks for every hypothesis and clause.
