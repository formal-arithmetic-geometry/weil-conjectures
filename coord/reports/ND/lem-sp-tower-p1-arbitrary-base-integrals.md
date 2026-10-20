## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals` states
`AlgebraicGeometry.Etale.exists_arbitraryBaseFiniteP1Integrals`. Its sole postponed proof
is `by sorry`; the docstring gives the node's seven-step universal-base proof. All
supporting definitions contain real data. Only the item's `lean` record changes.
There is no statement correction, dependency repair, or new independent notion.

The source read is main-20261015, sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-p1.proof.md, especially its levelwise finite diagonal check.
The full mathematical node and each statement dependency's recorded statement/interface
were read. The previous ArbitraryBaseFiniteP1Integrals and ArbitraryBaseP1Integrals
modules are empty withdrawn modules; this delivery uses a fresh module path.
There is no repair-notes entry for this item. The neighboring tower-adjunction node's
repair entry is not this item's repair handoff.

Hypothesis and clause correspondence:

* The positive integer is `(N : ℕ) (hN : 0 < N)`, retaining N=1. The coefficient ring
  is `(A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)`. This is exactly
  a finite commutative ring annihilated by N, without a nonzero-ring hypothesis.
* Each base is `(S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))`. The family `d` ranges
  over every such scheme, with no Noetherian, finite-type, qcqs or field assumption.
  This universal formulation is equivalent to the node's “for every T over S”:
  every such T is N-invertible, and conversely take S=T and its identity structure map.
  The same observation applies to all base morphisms, including those over a fixed S.
* The ordinary small-etale unbounded module category is the dependency's
  `DerivedCategoryModule A S`. `ordinaryFiniteUnit` is A_S in degree zero and
  `ordinaryFiniteLine A N hA S` is the concrete scalar-extended mu_N Tate sheaf in
  degree zero. `⟦(2 : ℤ)⟧` is the required shift. No pro-etale or inverse-limit
  construction enters these objects.
* `ProjectiveLine S` is `ProjectiveSpace (ULift (Fin 2)) S`; `ProjectiveLine S ↘ S`
  is its structural first projection. The lift preserves precisely two homogeneous
  coordinates and works at every explicit universe u.
* The existential `t : OrdinaryFiniteTwistTransport A N hA` is normalized by its
  roots inclusion and pure-tensor equations, rather than an arbitrary orientation.
  The splitting record's `chern_spec` is `ordinaryFiniteP1ChernSpec`: its abelian
  realization is the actual scalar Kummer boundary of the existing O(1), including
  the prescribed transition convention. Invertibility on P is derived from hS,
  not assumed separately. The derived Chern arrow is therefore constrained.
* `decomposition` is exactly the isomorphism b from the ordered biproduct
  A_S(1)[2] plus A_S to Rr_* A_P(1)[2]. `decomposition_hom` fixes its hom to
  `biprod.desc (ordinaryFiniteP1Unit ...) (ordinaryFiniteP1ChernPushforward ... chern)`.
  Those are the shifted twisted adjunction unit and the Chern adjunct h.
* `ArbitraryBaseFiniteP1Splitting.trace` is definitionally
  `d.decomposition.inv ≫ biprod.snd`, the required pr2 b inverse. There is no free
  trace parameter. `ArbitraryBaseFiniteP1BaseChange` quantifies over all
  `(f : S' ⟶ S)` and contains precisely the two required equations: inverse image
  of b followed by proper exchange and shifted-line identification equals the
  source-biproduct comparison followed by b'; inverse image of the trace followed
  by the constant comparison equals the same exchange/line comparison followed by t'.
* W is `pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)`. The existing
  `projectiveLineDiagonalProjection S false/true` are p1/p2 and the existing
  `projectiveLineDiagonalChart` identifies them canonically with P1 over P.
* The conclusion supplies `hI : (pullback.diagonal ...).ker.IsInvertible`, precisely
  the recorded locally regular-principal Cartier-ideal predicate. The diagonal is
  already a closed immersion by separatedness of projective space.
* The supported class is an Ext witness κ from the ordinary closed direct image of
  A_P to the concrete Tate line on W, constrained by `SupportedKummerBoundary`.
  This is the dependency's relative Kummer boundary with the canonical off-divisor
  trivialization, hence fixes the sign. The recorded
  `ordinary_supported_kummer_uniqueBoundary` gives its uniqueness, and the original
  `ordinary_supported_kummer` gives its unit/Chern equation c_D u_D = c1(O(D)).
  `supportedExactDerivedMap` is exactly its derived realization with source
  RDelta_* A_P, using exactness of closed direct image; it is not an arbitrary map.
* `projectiveLineDiagonalAlpha A S a` is the existing composite of the two canonical
  units, namely the canonical derived-composition source identification for
  p_i Delta = id. `IsIso` explicitly retains the node's isomorphism assertion.
* `arbitraryBaseFiniteP1DiagonalTrace` transports this family's own trace at P along
  the existing chart using the chart adjunction unit, `rightDerivedLowerStarComp`,
  `rightDerivedLowerStarCongr`, and the normalized shifted-line pullback. It is the
  canonical meaning of the node's instruction to identify p_i with r_P, not a trace
  chosen independently or the Noetherian-only `projectiveLineTrace`.
* For each `a : Bool`, the displayed composite is alpha, Rp_i of the supported
  Kummer map, then that trace, and equals `𝟙 (ordinaryFiniteUnit A (ProjectiveLine S))`.
  Thus both i=1 and i=2 identities, with the same κ and same family of splittings,
  are stated together. Composition order is Lean's left-to-right `≫` convention.

The small record is only a package for this theorem's witnesses. The existing
`OrdinaryFiniteP1Datum` also asserts an adjunction and its counit normalization,
which this node does not assert, so using that whole record would strengthen the
statement. The existing source-biproduct comparison is reused without redefining it.

Dependency declarations used (directly or through the recorded interface imports):

* Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
* Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, its two
  projections and its diagonal.
* WeilConjectures.AlgebraicGeometry.DerivedCategories and
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, the ordinary coefficient encoding.
* WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: `Etale.upperStar` and
  `Etale.upperStarLowerStarAdjunction`, used by the normalized derived arrows.
* WeilConjectures.SixFunctors.Etale.Derived.Tensor: `Etale.derivedTensor`, the tensor
  underlying the existing finite-line and ordinary finite-arrow interfaces.
* WeilConjectures.AlgebraicGeometry.ProjectiveSpace: `ProjectiveSpace`,
  `ProjectiveLine`, `ProjectiveSpace.map`, `ProjectiveSpace.isPullback_map`, properness.
* WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist: `ProjectiveSpace.twist`,
  used in the actual Kummer class; WeilConjectures.AlgebraicGeometry.Sites.Kummer:
  `Scheme.kummerSequence_shortExact`, used by its connecting map.
* Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback: `Scheme.etaleFiniteTwistPullback`;
  its roots and pure-tensor normalization is retained by `OrdinaryFiniteTwistTransport`.
* Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer: `ordinaryFiniteConstant`,
  `ordinaryFiniteUnit`, `ordinaryFiniteLine`, `ordinaryFiniteP1ChernSpec`,
  `ordinaryFiniteP1KummerClass`.
* Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows: `OrdinaryFiniteTwistTransport`,
  `ordinaryFinitePullback`, `ordinaryFinitePushforward`, `ordinaryFiniteP1Unit`,
  `ordinaryFiniteP1ChernPushforward`, `ordinaryFiniteShiftedLinePullback`,
  `ordinaryFiniteUnitPullback`, `ordinaryFiniteP1Exchange`.
* Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data:
  `ordinaryFiniteP1DecompositionSourceMap` (the existing canonical biproduct map).
* Sheaf.AlgebraicGeometry.ExactUnboundedExchange: `exactDerivedBaseChangeMap`,
  used inside `ordinaryFiniteP1Exchange` with the existing exact/left-derived transport.
* WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible:
  `Scheme.IdealSheafData.IsInvertible`; WeilConjectures.AlgebraicGeometry.EffectiveCartier:
  the divisor-line construction (proof dependency).
* Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer:
  `ordinary_supported_kummer`, `ordinary_supported_kummer_uniqueBoundary`, and its
  imported `SupportedKummerBoundary`, `supportedExactDerivedMap`, `supportedDerivedUnit`.
* Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals:
  `projectiveLineDiagonalProjection`, `projectiveLineDiagonalChart`,
  `projectiveLineDiagonalAlpha`, and the Noetherian-only
  `projectiveLine_diagonal_integrals` used in proof step 5.
* Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition:
  `ringedToposDerivedPushforwardComposition` (proof dependency); the explicit ordinary
  derived chart composition uses the existing `rightDerivedLowerStarComp`.
* Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction and ProjectiveLineTrace:
  `exists_ordinaryFiniteP1Adjunction`, `projectiveLineTrace` (proof on Spec Z[1/N]).
* Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange: the proper torsion exchange
  interface (proof dependency); ProjectiveSpaceStandardCharts:
  `ProjectiveSpace.projectiveSpace_standardCharts`; Mathlib.AlgebraicGeometry.Pullbacks:
  `pullbackSpecIso`; Mathlib.CategoryTheory.Adjunction.Mates: mate-pasting identities.

Edge cases checked before writing: N=1 forces A to be the zero ring, which is
allowed; the empty scheme imposes no nonemptiness requirement and all relevant
identities remain identities on its zero coefficient objects. Zero coefficients
for other N are allowed. Neither S nor its projective line is required to be
Noetherian. All maps f, including identities and maps from empty schemes, occur in
the base-change quantifier. Both Boolean values are included. No algebraic-closure,
characteristic-zero, regularity, coefficient-flatness or base-flatness assumption is
present. All variables and universe u are explicit (`autoImplicit false`).

Searches made:

* msearch leanfinder: “projective line finite coefficient Kummer splitting diagonal
  integrals over arbitrary base scheme”: eight hits concerning integral morphisms,
  affine space, elliptic curves and proper Proj; none state this theorem.
* msearch loogle: “CategoryTheory.Limits.biprod.desc, AlgebraicGeometry.ProjectiveSpace”:
  zero hits, unknown identifier AlgebraicGeometry.ProjectiveSpace (project declaration).
* msearch grep: “Kummer|diagonal.*trace|trace.*diagonal”, AlgebraicGeometry: zero hits.
* Direct Mathlib rg with the same regex: no matching finite Kummer integral theorem.
* Project rg in WeilConjectures and Sheaf for finiteP1, projective-line integral/
  splitting and ArbitraryBaseFiniteP1: the existing Noetherian
  ProjectiveLineDiagonalIntegrals theorem was found and read; no arbitrary-base theorem.
  Both old arbitrary-base modules are withdrawn stubs with no declarations.
* Exact node-id search in WeilConjectures: no match. In Sheaf it appears in the
  tower-adjunction proof prose, not as an attached arbitrary-base statement.
* Upstream-name/DAG name search for ArbitraryBaseFiniteP1 found no extant declaration
  with the new names. Existing notions are reused as listed above.

Validation: scompile.py compiled the delivered contents in sandbox mode (32.3 s)
and library mode (31.3 s), with no errors or warnings. The final module path is fresh
to avoid treating a withdrawn stub as an active owned module. The required dry run
and final delivery compile the final path again. No STATEMENT-DISPUTED issue found.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
