## Worker report

The module `Sheaf.Paper.KummerAdditivity` states the finite Kummer first Chern class
identity and its pullback and killing-exponent compatibilities. It constructs the class
from the ordinary Kummer boundary, rather than from a tensor product of G_m with A.
All three new theorem proofs are `sorry`; all definitions contain real constructions.

Hypotheses and clauses, matched with the node:

- The global finite-field datum, prime ell distinct from its characteristic, fixed
  coefficient closure, finite subextension E and positive coefficient level are the
  fields of `P : WeilConjectures.PurityFiniteSetting`. The coefficient is exactly
  `P.Coefficient`, the standard universe lift of O_E/(varpi_E^P.level). No divisibility
  condition on `P.level` or its ramification index occurs.
- `N : ℕ`, `hN : 1 ≤ N` and `hA : ((P.coefficients.l ^ N : ℕ) : P.Coefficient) = 0`
  render the chosen killing exponent and m=ell^N. Such an exponent always exists:
  the already published `P.diagonalExponent_annihilates` uses N=P.level.
- `T : Scheme`, `a : T ⟶ Spec (.of P.field.k)`, `IsSeparated a`,
  `LocallyOfFiniteType a` and `QuasiCompact a` mean exactly a separated finite-type
  k-scheme. Mathlib expresses finite type as the last two properties together.
  `kummerPower_isUnit` supplies invertibility on T from the field datum; invertibility
  is not an additional hypothesis on T.
- A line bundle up to isomorphism is `M : T.Pic`. Its group product `M * Q` is the
  tensor product of invertible O_T-modules, by `Scheme.Pic.mul_def`/`mulIso`.
  Every actual invertible module is represented by `Pic.ofIsInvertible`, so no line
  bundles are excluded by using isomorphism classes. `Pic.map f` is the canonical
  pullback of those classes, rather than a newly chosen operation.
- `Pic.toCohomologicalPicardGroup T M` is alpha_T(M): its definition is precisely
  `Sheaf.Torsor.classH1` of `M.etaleTorsorClass`, the frame torsor Isom(O,M).
- `T.kummerδ₁ m hT` is the ordinary Kummer H¹-to-H² boundary. In the recorded
  Ext presentation it is `Sheaf.H.δSucc`, Yoneda composition with the short exact
  Kummer extension. This is the usual positive connecting convention; the imported
  horseshoe theorem is the injective-resolution naturality input of the proof.
- `ordinaryFiniteRootMap A m hA T` is phi, the existing coefficient-insertion map.
  It sends a root z to 1 tensor z in A tensor μ_m; tensor symmetry identifies this
  with z tensor 1 in the node's μ_m tensor A. The target is the already defined
  `finiteEtaleTateLine`, not a second twist construction. The module-coefficient
  dependency is imported as required, and the existing A-linear scalar-extension
  presentation supplies its specialization to a coefficient ring A.
- `Etale.kummerFirstChernAbelian` is verbatim H²(phi)(delta(alpha(M))).
  `Etale.kummerFirstChern` is its unique lift under `ordinaryFiniteClass`.
  `kummerFirstChernRealization_bijective` states the degree-two comparison implicit
  in the node's instruction to interpret the class as a derived morphism. Its inverse
  determines the class uniquely; it does not choose data from mere existence.
- `ProEtale.kummerFirstChern` applies the recorded exact comparison inverse image
  termwise. Its source and target are nu*(A_T[0]) and nu*(L_m,A,T[2]). These are the
  finite-root coordinates of A_T and A_T(1)[2] already reexported by
  `PbcCoefficientTwists` through `FixedFinitePositiveCoefficientTwist`.
  In particular `diagonalTwistEtale`/`diagonalTwist` use this same finite-root
  presentation at N=P.level, with the harmless derived tensor-unit identification
  in their one-factor tensor. The root-tower reduction is the one of the recorded
  `pur_twist_sheaf_locally_free`, not an arbitrary line or a choice of generator.
- Conjuncts one and two of `kummer_additivity` assert the requested tensor additivity
  for the etale derived class and for its pro-etale realization. The abelian etale
  equality is the same equality under the bijective realization map.
- Conjunct three is etale naturality for every scheme morphism f:T'→T, with T' also
  separated finite type over k. There is no condition f≫a=a': even morphisms not
  over the displayed base are included, as in the node's 'every morphism' clause.
  It uses the published `ordinaryFiniteUnitPullback` and
  `ordinaryFiniteShiftedLinePullback`. The argument `t` ranges over normalized
  `OrdinaryFiniteTwistTransport`, not arbitrary twist isomorphisms. That structure
  specifies the root inclusion and the action on all pure tensors; its existence
  is supplied by the recorded `etaleFiniteTwistPullback` theorem.
- Conjunct four is the actual pro-etale inverse image of the pro-etale derived class.
  `kummerComparisonPullback` derives the existing canonical square
  `comparisonUpperStarCompUpperStarIso` and identifies its etale factor with the
  published derived pullback. `kummerCoefficientPullback` composes that square
  with the same unit and twist comparisons. Thus it states f*c₁(M)=c₁(f*M) with
  the canonical constant and Tate comparisons, rather than an unspecified map
  between cohomology groups. Base-change projections are special cases of these
  unrestricted scheme-morphism clauses; there is no flatness or smoothness condition.
- The final conjunct compares N'≥N. It provides a roots map q and an A-linear
  twist isomorphism e. The first normalization equation identifies q with the
  power ell^(N'-N), by its monic roots inclusion. The second equation says e
  carries insertion of each root to insertion of its image under q. A-linearity
  then determines e on all local generators, hence on the sheaf. The two remaining
  equations give independence for the etale and pro-etale classes. For any two
  killing exponents, compare each to their maximum; this is full independence,
  and includes equal and noncomparable initial choices.

Dependency interfaces read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `Coefficient` and the
  finite-field/coefficient fields.
- `Sheaf.Paper.PbcCoefficientTwists`, including its reexported
  `FixedFinitePositiveCoefficientTwist`: the finite root presentation valid at every
  positive level, and `diagonalExponent_annihilates`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`;
  via the recorded Picard encoding.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`: `rootsOfUnitySheaf`,
  `kummerSequence_shortExact`, `kummerδ₁`.
- `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`: the recorded
  `nonempty_equiv_quotient_torsor` and the canonical
  `Pic.toCohomologicalPicardGroup` frame-class construction in the same module.
- `WeilConjectures.CategoryTheory.Sites.Torsor`: `Sheaf.Torsor.classH1` and the
  recorded `nonempty_equiv_H_one_torsor`.
- `Sheaf.AlgebraicGeometry.KummerModuleCoefficients`: the recorded
  `kummerModuleTwist`/`kummerCoefficientInsertion` tensor description.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`: `ordinaryFiniteRootMap`,
  `ordinaryFiniteClass`, `ordinaryFiniteUnit`, `ordinaryFiniteLine`.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows`: `OrdinaryFiniteTwistTransport`,
  `ordinaryFiniteUnitPullback`, `ordinaryFiniteShiftedLinePullback`.
  Both owning nodes already have landed records and were added to `stmt_deps`.
- `Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget`:
  `nonempty_etaleModuleCohomology_forgetIso`.
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`:
  `rhom_global_sectionsOfUniverses`; no equality of site object and morphism universes.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `proEtaleSiteComparison`;
  its underlying `ProEtale.comparisonUpperStar` is used directly.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus`; the file uses its unbounded ambient exact
  `comparisonUpperStar.mapDerivedCategory`, since both Chern objects are bounded below.
- `Sheaf.Paper.PurTwistSheafLocallyFree`: `pur_twist_sheaf_locally_free` and its
  projection-defined root-tower reductions.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: `etaleFiniteTwistPullback`.
- The remaining stated proof-dependency modules are imported without `public` as the
  stage-3 proof plan requires. The convention-only morphism-properties node has no
  declaration of its own. `det-prop-sfb-cartesian-coefficients-twists` has no recorded
  module; the actual finite comparison square is given explicitly here instead.

Edge cases checked before and after writing: empty scheme (zero global ring is allowed,
no nonempty or connected assumption); trivial line bundle; torsion line bundles;
positive coefficient level one, including ramified E with ramification index not dividing
that level; N=1 when it kills A; arbitrary larger exponents and N'=N (identity transition);
identity f; nonflat f and base-change projections; zero coefficient rings in the generic
realization helper. Level zero and N=0 are excluded precisely where the node excludes
them. All site coefficients have universe u+1; pro-etale objects u+1 and arrows u remain
distinct.

Searches for an existing complete statement:

- `msearch.py ... leanfinder "The Kummer first Chern class is additive under tensor
  product of line bundles and natural under scheme pullback"`: eight hits, chiefly
  additive module pullback and scheme fibre-product formulas; no Chern-class theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.gmSheaf"`: no hits, unknown identifier
  in the remote Mathlib-only index.
- `msearch.py ... leansearch "The first Chern class defined by the Kummer boundary is
  additive for tensor products of line bundles"`: eight hits, tensor linear-map
  additivity and tensor-functor additivity; no Kummer Chern class.
- `msearch.py ... grep "firstChern|kummer.*add|Kummer.*add"`: zero Mathlib hits.
- `rg` in the source `WeilConjectures` and project `lean/Sheaf` for Kummer/Chern/c1:
  the upstream KummerClass module treats degree-one unit classes as a parameter,
  not this degree-two class of a line bundle. The project has actual projective-line
  and supported-Cartier specializations in `OrdinaryFiniteP1Kummer` and
  `OrdinarySupportedKummerBoundary`; their general root-insertion and realization
  helpers are reused, without duplicating either specialization.
- Identifier grep for the node id in upstream and `dag/lean_names_upstream.json`:
  no existing declaration of this node. No repair note is present for this item.

No statement correction, new independent definition node, dependency repair or
STATEMENT-DISPUTED flag is needed. This follows the node's reviewed 2026-10-17
coefficient correction, rather than reinstating the older blueprint's G_m tensor A
(which is zero on the etale site when a unit exponent kills A).

## Second reading by NV

Independent reading (replaces the author's self-check that stood here; H11), done by
the maintainer's reviewer on the immutable delivery 755305c8. The node, its 17 stmt_deps,
the dependency modules and the delivered module were read side by side.

Node statement as a list, with the Lean that renders it and the verdict:

1. Purity conventions, A = A_{E,n}, any n >= 1: `P : PurityFiniteSetting`, `P.Coefficient`
   (ULift of O_E/varpi^level, `level_pos`). No e | n condition. OK.
2. Killing exponent N >= 1 with l^N A = 0, m = l^N: `N`, `hN : 1 ≤ N`, `hA` with the
   natural-number power cast. OK; such N exists (`diagonalExponent_annihilates`).
3. T separated finite type over k: `a : T ⟶ Spec k`, `IsSeparated a`,
   `LocallyOfFiniteType a`, `QuasiCompact a`. Exact Mathlib encoding. OK.
4. m invertible on T: derived, not assumed (`kummerPower_isUnit`, sorry'd theorem with
   proof docstring; true since l is a unit in k and l ≠ p). OK.
5. Line bundles M, P, tensor product: `T.Pic`, `M * Q` (Pic multiplication is tensor
   product); the class depends only on the isomorphism class. OK.
6. alpha_T(M), frame torsor class: `Pic.toCohomologicalPicardGroup` = `classH1` of the
   frame torsor Isom(O, M) (upstream GmPicard). OK.
7. delta_{m,T}: `kummerδ₁` = `Sheaf.H.δSucc` of `kummerSequence_shortExact`, the same
   boundary used by the landed `ordinaryFiniteP1KummerClass` and `supportedKummerChern`.
   OK (see the observation on sign conventions below; no clause depends on the sign).
8. phi : mu_m -> L = mu_m ⊗ A, z -> z ⊗ 1: `ordinaryFiniteRootMap` (z -> 1 ⊗ z in
   A ⊗ mu, target `finiteEtaleTateLine`); tensor symmetry. OK.
9. c^et_{1,A}(M) = H^2(phi)(delta(alpha(M))): `Etale.kummerFirstChernAbelian`, verbatim. OK.
10. As a morphism A_T -> L[2] in D(T_et, A): `Etale.kummerFirstChern`, the inverse of the
   recorded realization `ordinaryFiniteClass` (forget, then precompose with Z_T -> A_T)
   under the named theorem `kummerFirstChernRealization_bijective` (sorry, with proof
   docstring; true by Stacks 03FD/08JA: Ext^2_A(A_T, F) = H^2(T, F) = Ext^2_Z(Z_T, F)).
   The def depends on a named theorem, not on an inline sorry (H5). Data is unique since
   the map is injective. OK.
11. Pullback through nu_T and the identification nu^*L ≅ A_T(1): `ProEtale.kummerFirstChern`
   = `comparisonUpperStar.mapDerivedCategory.map`. Source nu^*(A_T[0]), target
   nu^*(L[2]): the finite-root presentation of A_T(1)[2] recorded under
   def-coefficient-twists-detailed (`diagonalTwist` = nu^* of `affineLinearBaseCoefficient`,
   which at d = 1 is this line up to the derived tensor unitor). OK.
12. Additivity of c_{1,A} and of c^et: conjuncts 1 and 2, equalities in the Hom groups. OK.
13. Pullback f^* c(M) = c(f^* M) for every f : T' -> T, T' separated finite type, under
   canonical constant and Tate comparisons: conjuncts 3 (etale, `ordinaryFiniteUnitPullback`,
   `ordinaryFiniteShiftedLinePullback` with normalized `OrdinaryFiniteTwistTransport`,
   which is unique: roots fixed by the monic kernel inclusion, line by its values on the
   generators a ⊗ z) and 4 (pro-etale, `kummerCoefficientPullback` through the canonical
   square `comparisonUpperStarCompUpperStarIso`). Types match: both sides go from
   g^*(unit_T) to the line on T' shifted by two. OK. No f ≫ a = a' premise: this is more
   general than morphisms over k, but still true (Kummer, frame and coefficient
   naturality only need m invertible on T and T'), and the over-k case is an instance.
14. Base-change projections: special case of 13. OK.
15. Independence of N: conjunct 5, for N' >= N an existentially given q, e, each pinned
   down by its normalization (q ≫ ι_N = l^(N'-N) • ι_{N'}; e ∘ phi_{N'} = phi_N ∘ q, and A-linear
   e is determined on generators), plus the etale and pro-etale equalities
   c_{N'} ≫ e[2] = c_N. Direction checked against the map of Kummer sequences
   (power d on mu and the middle G_m, identity on the right G_m). Comparing two
   exponents with their maximum gives full independence. OK.

Edge cases: empty T (zero ring; allowed, invertibility holds), trivial bundle, N' = N,
identity f, non-flat f, level 1 with ramified E, zero coefficient ring in the generic
helpers. Universes: T and k in u, coefficients u+1, pro-etale site objects u+1 and arrows
u kept distinct. No unbound variables.

Searches: grep of the side Lean and upstream for `kummerδ₁`, `Chern`, `ordinaryFiniteClass`:
only the P^1 and supported-Cartier specializations (`ordinaryFiniteP1KummerClass`,
`supportedKummerChern`) and curve-level uses; no general class and no bijectivity of
`ordinaryFiniteClass`. The new declarations are not duplicates.

Records: node changed only in `lean` and in `stmt_deps` by two landed nodes
(def-asd-ordinary-finite-p1-kummer-class, def-asd-ordinary-finite-p1-arrows), allowed by
STMT_DEPS MAY GAIN LANDED NODES; `lean.statement` is verbatim in the file. Lines <= 100.

Compile: `nt_compile.py` of lean/Sheaf/Paper/KummerAdditivity.lean, 34.2 s and 39.7 s, exit 0,
no errors or warnings.

Observation: the node names the injective-resolution (horseshoe) convention for delta;
the Lean uses the Ext Yoneda boundary `δSucc`, as the landed P^1 and supported classes do.
A possible sign difference does not affect any clause (additivity, pullback, exponent
independence are sign invariant).

Changed: this section only.

## Validation

The prescribed scompile.py check accepted the final module in both sandbox and
library-module modes (34.1 s and 35.8 s), with no errors or warnings. The node
record was checked against the exact final signature. Only lean and the two
authorized landed-node additions in stmt_deps differ from the repository node.
