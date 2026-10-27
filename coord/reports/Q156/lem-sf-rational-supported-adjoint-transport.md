## Worker report

Item: lem-sf-rational-supported-adjoint-transport. The delivery adds
`Sheaf.Paper.SfRationalSupportedAdjointTransport`, namespace `WeilConjectures`.
The node's statement, dependencies and proof are unchanged. Four theorem statements,
all with `sorry`, express its clauses; the node's `lean.declarations` records all
four and their data-packaging helpers. No separate missing mathematical notion or
dependency repair was needed. No statement dispute was found.

### Hypotheses and their Lean rendering

- A prime ell is `(l : ℕ) [Fact l.Prime]`. The finite coefficient extension is
  `(E : Type e) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. Its valuation ring and chosen uniformizer are
  the recorded `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionUniformizer l E`. They are never replaced by an
  abstract ring with assumed properties.
- The three linear triangulated categories are the independently universe-bound
  `X : Type u`, `Z : Type x`, `U : Type z`, with `Category.{v}`, `Category.{y}`,
  `Category.{w}`, respectively, `Preadditive`, `Linear R`, `HasZeroObject`,
  `HasShift _ ℤ`, all shifts additive, `Pretriangulated` and `IsTriangulated`.
  The explicit `[(shiftFunctor _ (1 : ℤ)).Linear R]` binders spell out the linear
  shift in “linear triangulated category”, exactly as the recorded raw
  scalar-triangulation dependency requires. They impose no relation among the
  three categories' object or morphism universes. Negative shifts then inherit
  linearity from the inverse equivalence; all integer shifts inherit it from
  compositions, as in that dependency's `all_shift_linear` construction.
- `SfSupportedAdjunctions R X Z U` packages precisely the supplied input. Its
  `closedPush`, `closedPull`, `exceptional`, `openPull`, `openPush` are i_*,
  i^*, i^!, j^*, j_*. Each has `Additive`, `Linear R`, `CommShift ℤ`, and
  `IsTriangulated` fields. These are the exact linear functors with their
  supplied shifts, rather than adjoints whose exactness is assumed later.
- `closedAdj : closedPull ⊣ closedPush`,
  `exceptionalAdj : closedPush ⊣ exceptional`, and
  `openAdj : openPull ⊣ openPush` are the three ordinary adjunctions.
  Their `Adjunction.CommShift ℤ` fields require both units and counits to
  commute with the supplied exact shifts.
- `closedCounitIso : IsIso closedAdj.counit` and
  `openCounitIso : IsIso openAdj.counit` are exactly the two invertible
  restriction counits; natural-transformation invertibility is equivalent to
  invertibility at every object.
- `zeroComposite : ∀ P : Z, IsZero (openPull.obj (closedPush.obj P))` expresses
  j^* i_* = 0, without choosing a new zero functor or an arbitrary isomorphism.
- `boundary K` has source j_*j^*K and target (i_*i^!K)[1]. The field
  `distinguished K` says that `Triangle.mk (exceptionalAdj.counit.app K)
  (openAdj.unit.app K) (boundary K)` is distinguished. Thus the first two
  arrows are the specified counit and unit, not merely maps isomorphic to them.
  Naturality or uniqueness of boundary is not assumed in this input.

### Conclusions and their Lean rendering

1. `sfRationalSupportedAdjointTransport` concludes
   `Nonempty (SfSupportedAdjunctionTransport R varpi X Z U S)` for those
   precise coefficients. `Nonempty` is the logical existence assertion of the
   node, not a definition that selects data from an undetermined existence.
   Every non-theorem definition in the file has explicit data.
2. `rawX`, `rawZ`, `rawU` supply triangulations on the already published
   `ScalarLocalization R _ varpi`. Their objects remain single wrappers of
   the original objects and Homs remain the published tensor modules.
   `SfSupportedRawTriangulation.tensorShift` fixes each shift as the tensor
   extension of the original shift; `identityComparison` fixes the localization
   shift comparison; `imageTriangles` characterizes exactly the triangles
   isomorphic to images of original distinguished triangles. Localization is
   exact. There is no Karoubi envelope, new idempotent, or abstract substitute
   for the raw category. The class merely records the structures and
   normalizations supplied by the scalar-localization dependency.
3. `localized` supplies all five exact linear functors and all three
   shift-compatible adjunctions on these same raw categories, with the two
   invertible counits, zero composite and distinguished supported triangles.
   Each of the five `*Normalization` fields fixes its functor's objects,
   every pure-tensor morphism, and its shift comparisons.
   `closedAdjUnit`, `closedAdjCounit`, `exceptionalAdjUnit`,
   `exceptionalAdjCounit`, `openAdjUnit`, `openAdjCounit` fix all six
   adjunction transformations as images under the actual localization functor.
   `boundaryNormalization` fixes the connecting map as the image of the given
   integral map followed by the canonical comparison to shift by one.
   `HEq` is used only where endpoint equalities are supplied by these object
   normalizations; it states equality of actual maps, not an unconstrained map.
4. `originalConsequences` and `localizedConsequences` assert the identical
   `SfSupportedConsequences` predicate before and after localization.
   `orthogonal` quantifies over every P, N and integers m, n and asserts
   `Subsingleton (i_*P[m] ⟶ j_*N[n])`, the correct zero-Hom-group assertion.
   `uniqueMorphism` is `∃! τ : S.triangle K ⟶ S.triangle L, τ.hom₂ = f`
   for every K, L, f. `components` identifies hom₁ and hom₃ with i_*i^!f
   and j_*j^*f. In particular it rules out any unspecified choice of outer maps.
   Uniqueness also supplies the identity/composition functoriality of triangle
   morphisms, since both composites have the same middle component.
5. `uniqueBoundary` quantifies over every candidate connecting arrow whose
   triangle with these exact first two maps is distinguished and equates it to
   `S.boundary K`. `natural` is the connecting-map naturality square with those
   specified outer maps. `signedShift` states the signed rule for every integer
   n, using `n.negOnePow`, both composite functors' `commShiftIso`, and the
   explicit interchange `shiftFunctorComm X 1 n`. The order of this interchange
   converts (A[1])[n] into (A[n])[1]. At n=1 the connecting arrow changes sign;
   the node's supplied proof explicitly requires this sign.
6. `exceptionalOpenZero : ∀ N, IsZero (exceptional.obj (openPush.obj N))`
   is i^!j_*N=0. `exceptionalUnitIso : ∀ P, IsIso
   (exceptionalAdj.unit.app P)` is Q -> i^!i_*Q invertible. Both occur in
   both original and localized consequences.
7. `sfSupportedRationalHomCoordinates` gives the unique additive equivalence
   from the raw Hom to `(K.obj ⟶ L.obj) ⊗[R] E` taking every `a ⊗ₜ f`
   to `f ⊗ₜ sfRationalCoefficientEquiv l E a`. Thus tensor-factor order and
   the canonical coefficient-field identification are explicit. No freeness,
   finite generation or faithfulness of tensoring is imposed.
8. `sfSupportedKernelRightAdjoint` accepts an ordinary `adj : F ⊣ G` with
   F additive, R-linear and exact, and concludes G additive and R-linear,
   the unique coherent `G.CommShift ℤ` compatible with that adjunction,
   exactness for `adj.rightAdjointCommShift ℤ`, and scalar linearity of
   `adj.homEquiv P K`. Neither G's exact structure nor Hom linearity is
   an extra input. The additive part of the Hom adjunction follows from
   additive F, G by Mathlib's `Adjunction.homAddEquiv`.
9. For the scheme clause, `sfSupportedIntegralCategoryIdentification` binds
   `(k : Type u) [Field k]`, `hl : IsUnit (l : k)`,
   `[T.Over (Spec (.of k))]`, `[LocallyOfFiniteType (T ↘ Spec (.of k))]`,
   `[QuasiCompact (T ↘ Spec (.of k))]` and
   `[IsSeparated (T ↘ Spec (.of k))]`. These are precisely a separated
   finite-type scheme over a field with ell invertible. No Noetherian,
   dimension, smoothness, characteristic-p or finite-field assumptions are added.
   Noetherianity and finite dimension are consequences used in its proof plan.
10. `sfSupportedCompletePresentation` and `sfSupportedPerfectPresentation`
    are just preimages of the existing
    `PbcIsBoundedConstructibleComplete` and `IsIntegralStratifiedPerfect`
    predicates under the published `integralDetailedTransport T l E`.
    They introduce no new completion or constructibility notion. The transport
    is restriction along `integralDetailedCoefficientComparison`, whose
    uniquely specified normalization is compatibility with every quotient
    projection. This keeps the detailed category's `E : Type u` and the
    small site's coefficient universe u+1 through the published ULift
    convention, without imposing a site-universe equality.
11. The scheme theorem concludes an equality `h` from the recorded
    `sfIntegralConstructible l E T` to the complete presentation, followed by
    equality of the complete and perfect presentations. These predicates
    select literally the same objects in the same ambient detailed category;
    as full subcategories they also have literally the same Homs.
    `sfSupportedRawPredicateEquivalence` is equality elimination applied to
    `CategoryTheory.Equivalence.refl`, hence the raw identity identification.
    The two remaining clauses explicitly assert its object map and its action
    on every `a ⊗ₜ f`. They preserve the underlying K and the underlying
    `f.hom`, with only membership proofs transported. Composing with the
    complete=perfect predicate equality gives the same identification for
    stratified-perfect objects. Equality elimination likewise transports the
    integral shifts/triangles and hence their raw structures. The source
    rational category `sfRationalConstructibleCategory` unfolds to the raw
    scalar localization on the left; no idempotent completion is inserted.

### Dependency declarations and source inspection

All statement dependencies were read, including their complete statements and
Lean records / Mathlib matches, and the relevant declaration signatures and
docstrings. The source read was
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sf-localization/prop-sf-localization-all-stages.proof.md`,
especially Vanishing, Integral stage, Rational stage, and Consequences.
The node's seven-step proof is included in the four theorem docstrings with its
dependencies, including the signed shift argument and coefficient comparison.

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its public coefficient constructions
  in `Sheaf.NumberTheory.Padics.CoefficientExtension` supply the actual ring,
  uniformizer and finite extension, used unchanged.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `.Triangulated`,
  `.Functor`: `Pretriangulated`, `IsTriangulated`, `Functor.IsTriangulated`.
- `Mathlib.CategoryTheory.Linear.LinearFunctor`: `Functor.Linear`, together
  with `Functor.Additive`, as the exact recorded linear-functor match requires.
- `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleCategory`, `sfRationalCoefficientEquiv`, and its
  published raw structures. `Sheaf.CategoryTheory.ScalarLocalization`:
  `ScalarLocalization`, `.mk`, `.map`, `.localization`.
- `Sheaf.Paper.SfIntegralConstructible`:
  `sfIntegralConstructible`, `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.IntegralUniformCoefficient` preserves the recorded
  `PbcIsBoundedConstructibleComplete` and `PbcBoundedConstructibleComplete`.
  Its larger-universe specialization is not forced onto the detailed
  category; the existing `pbcIntegralDatum` uses the canonical lifted ring.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `IsIntegralStratifiedPerfect`, `integralStratifiedPerfectCharacterization`,
  `integralStratifiedPerfectDetailed`, `integralDetailedTransport`, and the
  quotient-normalized `integralDetailedCoefficientComparison`.
- Proof imports retain
  `ScalarLocalization.exists_triangulated_scalarLocalization`
  (`Sheaf.CategoryTheory.ScalarLocalizationTriangulated`) and
  the tensor functor/adjunction transport API
  (`Sheaf.CategoryTheory.SemilinearScalarLocalization`).
- The shift/right-adjoint clauses use
  `Adjunction.rightAdjointCommShift`, `Adjunction.CommShift` and its
  compatibility/uniqueness lemmas (`Mathlib.CategoryTheory.Shift.Adjunction`),
  `Adjunction.isTriangulated_rightAdjoint`
  (`Mathlib.CategoryTheory.Triangulated.Adjunction`),
  `Adjunction.right_adjoint_additive` and `.homAddEquiv`, and
  `Adjunction.right_adjoint_linear`
  (`WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor`). The last
  is already present upstream even though its newly extracted proof-only
  node `lem-sbc-linear-right-adjoint` has no Lean record; no duplicate is added.
- Other retained proof imports provide
  `Pretriangulated.triangle_morphism_extension`
  (`WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension`),
  `Adjunction.fullyFaithfulROfIsIsoCounit` and
  `Adjunction.unit_isIso_of_L_fully_faithful`
  (`Mathlib.CategoryTheory.Adjunction.FullyFaithful`), and
  `AlgebraicGeometry.exists_topologicalKrullDim_le`
  (`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`).
  The finite-type Noetherian Mathlib instances are public through
  `IntegralUniformCoefficient`'s `Mathlib.AlgebraicGeometry.Noetherian` import.

### Edge cases checked

- Orthogonality covers arbitrary integers, including 0 and negative shifts.
  The signed comparison has positive and negative parity and the correct n=0
  normalization. Neither category is assumed essentially small, Abelian, or
  bounded. All six category universes remain independent.
- Zero objects and zero functors satisfy the typed input and conclusions;
  zero Homs are `Subsingleton`, and zero objects are `IsZero`. Tensoring
  torsion Hom modules is allowed to kill them: no faithful localization is used.
- Nonfaithful scalar localization, infinitely generated Hom modules and
  non-idempotent-complete categories are allowed. The normalized tensor
  formulas specify all arrows because pure tensors generate the Hom modules.
- The scheme theorem allows the empty scheme and arbitrary characteristic
  subject only to ell being a unit; the Krull-dimension lemma allows bottom
  dimension for the empty scheme. No closed/open subscheme is presumed nonempty.
- `E = Padic l` is allowed. The actual chosen valuation-ring uniformizer is
  used, as in the coefficient node, with no assumption that it is literally l.
- The right adjoint is supplied merely as a functor plus ordinary adjunction;
  its compatible shifts and coefficient linearity are conclusions.

### Searches

The sandbox search journal records the msearch calls and returned results.
No declaration with the whole statement exists.

- `msearch.py`, leanfinder,
  “Raw scalar localization preserves adjunctions and unique supported
  distinguished triangle morphisms”: eight hits, principally
  `CategoryTheory.Triangulated.Localization.complete_distinguished_triangle_morphism`,
  `.pretriangulated`, `.isTriangulated`, and homological-functor localization.
  These concern components of the argument; none preserves all supplied
  adjunction data and states supported uniqueness and the integral identification.
- `msearch.py`, loogle,
  `CategoryTheory.Adjunction, CategoryTheory.Triangle`: unknown identifier
  `CategoryTheory.Triangle`, no hits. The repeated query adding
  `CategoryTheory.ScalarLocalization` had the same result; this was not
  treated as evidence of absence on its own.
- `msearch.py`, grep, `supported.*triangle|localiz.*[Aa]djunction`,
  subdirectory `CategoryTheory`: six hits including localization adjunction
  and Bousfield modules; none is this supported scalar-transport statement.
- `msearch.py`, grep,
  `supported.*adjunction|rationalSupported|supportedTriangle|SupportedTriangle`,
  subdirectory `CategoryTheory`: no hits. Leanfinder with
  “Scalar localization preserves adjunctions supported distinguished triangles
  unique triangle morphisms recollement” returned eight component results,
  including the triangulated-adjoint theorems used here.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` with those supported-data
  patterns, the node id, and the proposed declaration names: no existing exact
  statement or colliding proposed name. Existing
  `SfSupportedLocalization` in `Sheaf.Paper.SfLocalizationAllStages` was opened:
  it is an ambient realization package whose fields already include uniqueness
  and orthogonality; it neither states the generic scalar transport nor packages
  this node's input, and cannot be used as its hypotheses. Specialized supported
  sheaf/kernel statements likewise do not state this theorem.
- `rg` of `dag/lean_names_upstream.json` for `SfSupported|sfSupported`:
  no match. The source's recorded scalar-localization and coefficient
  declarations were reused rather than duplicated.

### Validation

The only proofs postponed in this module are
`sfRationalSupportedAdjointTransport`, `sfSupportedRationalHomCoordinates`,
`sfSupportedKernelRightAdjoint`, `sfSupportedIntegralCategoryIdentification`.
Each is a clause of the owning node and has its source and natural-language
proof plan in its docstring. Definitions, structure data and equality transport
have real terms. `autoImplicit false` is enabled; all universes and variables
are explicit. Every Lean line is at most 100 characters.

All compilation uses the prescribed server `scompile.py` wrapper, one file,
against the live published library, with the default 60-second limit. An initial
qualification error in equality transport was repaired by the fully qualified
`CategoryTheory.Equivalence.refl (C := ...)` term. Final compilation and the
`deliver2.py --no-push` preflight are run before the push.

## Second reading by Q156

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
