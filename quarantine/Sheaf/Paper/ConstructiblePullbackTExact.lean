/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.Paper.ConstructibleTruncations
public import Sheaf.Paper.FiniteCoefficientPoint
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Sheaf.Paper.FieldDerivedScalarTower

import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.SfImmersionCompletedPullbackComparison
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
public import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
public import Sheaf.Paper.SfConstructibleHeart
import Sheaf.Paper.CompletedPullbackTriangles
import Sheaf.CategoryTheory.SemilinearScalarLocalization
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Paper.PointSectionsScalarExtension
import Sheaf.Paper.LocalizedTStructure

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.IntegralPullbackCompletedComparison
import Sheaf.Paper.IntegralPullbackComposition

/-! # T-exact constructible pullback and geometric-point fibres

Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3),
Proposition 6.8.14(2) and Remark 6.8.15
(blueprint: lem-a1-constructible-pullback-t-exact).

The comparison data below package the clauses of this node. Their cohomology maps
are explicitly the composites of the truncation comparisons and the shift comparison.
The scalar square is an equality of those maps, rather than an existence of unrelated
isomorphisms. The categories and the standard pairs are the recorded intrinsic ones.

## Main statements

- `constructible_pullback_t_exact`: t-exact pullback, exact hearts and canonical cohomology.
- `constructible_pullback_scalar_compatibility`: finite and common-stage scalar squares.
- `constructible_pullback_point_fibre`: the point cohomology and degree-zero clauses.
- `constructible_point_scalar_compatibility`: the point-evaluation scalar squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v uC vC uB vB uD vD uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry

namespace WeilConjectures

/-- Clause package: preservation of both standard halves, the exact restriction to
specified full hearts, and the canonical truncation and cohomology comparisons.
Source: Bhatt--Scholze 6.8.11(3), 6.8.15; BBD 1.3.3--1.3.6
(blueprint: lem-a1-constructible-pullback-t-exact). -/
structure ConstructiblePullbackComparison
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    (t : TStructure C) (s : TStructure B)
    (P : ObjectProperty C) (Q : ObjectProperty B) (F : C ⥤ B) where
  tExact : F.IsTExact t s
  heart : P.FullSubcategory ⥤ Q.FullSubcategory
  heart_fac : heart ⋙ Q.ι = P.ι ⋙ F
  heart_limits : PreservesFiniteLimits heart
  heart_colimits : PreservesFiniteColimits heart
  commShift : F.CommShift ℤ
  truncLE : ∀ n : ℤ, t.truncLE n ⋙ F ≅ F ⋙ s.truncLE n
  truncLE_counit : ∀ (n : ℤ) (K : C),
    (truncLE n).hom.app K ≫ (s.truncLEι n).app (F.obj K) =
      F.map ((t.truncLEι n).app K)
  truncGE : ∀ n : ℤ, t.truncGE n ⋙ F ≅ F ⋙ s.truncGE n
  truncGE_unit : ∀ (n : ℤ) (K : C),
    F.map ((t.truncGEπ n).app K) ≫ (truncGE n).hom.app K =
      (s.truncGEπ n).app (F.obj K)
  cohomology : ∀ j : ℤ, constructibleTruncationCohomology t j ⋙ F ≅
    F ⋙ constructibleTruncationCohomology s j
  cohomology_formula : ∀ (j : ℤ) (K : C),
    (cohomology j).app K =
      (fun [_cs : F.CommShift ℤ] ↦ (F.commShiftIso j).app
          ((t.truncGE j).obj ((t.truncLE j).obj K))) (_cs := commShift) ≪≫
        (shiftFunctor B j).mapIso
          ((truncGE j).app ((t.truncLE j).obj K) ≪≫
            (s.truncGE j).mapIso ((truncLE j).app K))

/-- The scalar compatibility equation for cohomology in a naturally commuting square.
Both routes start with T(F(H^j K)) and end with H^j(G(S K)).
Source: Bhatt--Scholze 6.8.14(2), common-stage convention
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def ConstructiblePullbackScalarSquare
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A] [HasShift A ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    {t : TStructure C} {s : TStructure B} {r : TStructure D} {a : TStructure A}
    {P : ObjectProperty C} {Q : ObjectProperty B}
    {R : ObjectProperty D} {U : ObjectProperty A}
    {F : C ⥤ B} {G : D ⥤ A} {S : C ⥤ D} {T : B ⥤ A}
    (dF : ConstructiblePullbackComparison t s P Q F)
    (dG : ConstructiblePullbackComparison r a R U G)
    (dS : ConstructiblePullbackComparison t r P R S)
    (dT : ConstructiblePullbackComparison s a Q U T)
    (β : F ⋙ T ≅ S ⋙ G) : Prop :=
  ∀ (j : ℤ) (K : C),
    T.map ((dF.cohomology j).hom.app K) ≫
        (dT.cohomology j).hom.app (F.obj K) ≫
          (constructibleTruncationCohomology a j).map (β.hom.app K) =
      β.hom.app ((constructibleTruncationCohomology t j).obj K) ≫
        G.map ((dS.cohomology j).hom.app K) ≫
          (dG.cohomology j).hom.app (S.obj K)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- The residue-field inverse required by the recorded pullback interface, extracted
from constructibleTruncations_exists. Invertible structures are subsingletons, so the
postponed theorem determines these data uniquely; no invertibility hypothesis is added.
Source: finite-field convention and Bhatt--Scholze 6.8.15
(blueprint: lem-a1-constructible-pullback-t-exact). -/
abbrev constructiblePullbackResidueUnits (Y : Scheme.{u})
    [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))] :
    ∀ y : Y, Invertible (l : Y.residueField y) :=
  (constructibleTruncations_exists D l hl Y
    (AlgebraicClosure (Padic l))).choose_spec.choose_spec.choose

/-- The comparison clause at a finite coefficient field, using exactly the recorded
standard t-structures and full constructible hearts.
Source: Bhatt--Scholze 6.8.11(3), 6.8.14(2), 6.8.15
(blueprint: lem-a1-constructible-pullback-t-exact). -/
abbrev ConstructibleRationalPullbackComparison
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {W X : Scheme.{u}} [W.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (h : W ⟶ X) :=
  letI := constructiblePullbackResidueUnits D l hl W
  letI := constructiblePullbackResidueUnits D l hl X
  ConstructiblePullbackComparison
    (sfRationalStandardTStructure l E X D hl) (sfRationalStandardTStructure l E W D hl)
    (sfRationalHeartProperty l E X) (sfRationalHeartProperty l E W)
    (rationalDerivedPullback l E h)

/-- The same clauses at the common-stage algebraically closed coefficient category.
The closure universe is independent of the scheme universe.
Source: Bhatt--Scholze 6.8.14(2), 6.8.15 and the common-stage convention
(blueprint: lem-a1-constructible-pullback-t-exact). -/
abbrev ConstructibleCommonStagePullbackComparison
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {W X : Scheme.{u}} [W.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (h : W ⟶ X) :=
  letI := constructiblePullbackResidueUnits D l hl W
  letI := constructiblePullbackResidueUnits D l hl X
  ConstructiblePullbackComparison
    (sfCommonStageStandardTStructure l X Ω D hl)
    (sfCommonStageStandardTStructure l W Ω D hl)
    (sfCommonStageHeartProperty l X Ω) (sfCommonStageHeartProperty l W Ω)
    (commonStageDerivedPullback l Ω h)

/-- Pullback preserves both standard halves, restricts to an exact heart functor,
and has the cohomology comparison induced by the canonical truncation maps.
Source: Bhatt--Scholze 6.8.10, 6.8.11(3), 6.8.14(2), 6.8.15
(blueprint: lem-a1-constructible-pullback-t-exact).

Proof plan, following the node step by step:

1. Put $R=\mathcal O_E$, $\pi=\varpi_E$, $A_n=R/\pi^n$, and $B_T=\varprojlim_n(A_n)_T$. First work
   integrally. The schemes $X,W$ are Noetherian and finite-dimensional: apply [lem-weil-pbc-finite-
   type-over-noetherian] and [lem-fin-finite-type-fibre-dimension-bound] to their structure maps to
   $\operatorname{Spec}k$, whose one-point space is quasi-compact and whose field coordinate ring is
   Noetherian. Also $\ell$ is invertible since $\ell\ne p$. Thus [lem-weil-pbc-integral-stratified-
   perfect-characterization] applies to exactly the integral category used here, including its
   uniform reduction bounds. For $K\in D^b_c(X,R)$, [lem-pur-integral-operations-preserve-
   constructible](1) ensures $Lh^*K\in D^b_c(W,R)$ with the specified finite reductions. We will
   prove that any cohomological interval $[a,b]$ for $K$ is also an interval for $Lh^*K$.

2. Choose the finite constructible locally closed stratification $i_\alpha:S_\alpha\to X$ and pro-
   etale covers $v_{\alpha t}:V_{\alpha t}\to S_\alpha$ in [lem-weil-pbc-integral-stratified-
   perfect-characterization](ii). Write $K|_{V_{\alpha t}}\cong B_{V_{\alpha t}}\otimes_R P_{\alpha
   t}^\bullet$, with $P^\bullet$ bounded finite projective. Restrictions here are ordinary exact
   inverse images, and they agree with the item's integral pullback. By [lem-a1-integral-pullback-
   completed-comparison] the integral pullback of [def-weil-derived-pullback-tensor-hom] along any
   morphism is naturally isomorphic to the strict-tower completed pullback, compatibly with the
   finite reductions; for immersions [lem-sf-immersion-completed-pullback-comparison] identifies the
   latter with the exact ordinary inverse image. For $v_{\alpha t}$, [lem-weil-proetale-weakly-
   etale-localization] identifies $V_{\alpha t,\mathrm{proet}}$ with the localized site and [lem-
   sfb-proetale-object-inverse-image-restriction](3) identifies the module inverse image $v_{\alpha
   t}^*$ with restriction to it, which is exact by [lem-weil-pbc-site-restriction-exact].
   Restriction evaluates a sheaf on the same objects, so it preserves the sectionwise products of
   [lem-weil-proetale-countable-products-exact] and the inverse limit defining $B$. Applying it to
   both coordinates of the Roos cone in [lem-sf-strict-roos-derived-limit-comparison] therefore also
   commutes with completed pullback. In particular these restrictions commute with cohomology by
   [lem-weil-pbc-exact-functor-complex-cohomology]; hence $K|_{V_{\alpha t}}$ still has cohomology
   only in $[a,b]$.

3. Here is the scalar-model calculation needed for these chosen $P^\bullet$. Its completed-
   coefficient representative is bounded and termwise projective, hence K-flat by [lem-pc-bounded-
   above-flat-kflat-site]. For a morphism $g:V'\to V$, the reduction of $B_V\otimes_RP^\bullet$ is
   $(A_n)_V\otimes_RP^\bullet$ by [lem-weil-pbc-completed-constant-sheaf-reduction]. Its finite
   pullback is $(A_n)_{V'}\otimes_RP^\bullet$: the constant-section comparison of [prop-weil-pbc-
   proetale-constant-ring-map] preserves each scalar matrix, and the finite module pullback is exact
   by [prop-weil-pbc-proetale-constant-exact]. Consequently the defining reduction-tower formula in
   [def-weil-derived-pullback-tensor-hom] gives $$Lg^*(B_V\otimes_RP^\bullet)\cong
   R\varprojlim_n((A_n)_{V'}\otimes_RP^\bullet)\cong B_{V'}\otimes_RP^\bullet.$$ For the last
   equality, each projective term is a summand of a finite free module. The tower of that term has
   epimorphic transitions, so [det-pe-milnor-epimorphic] computes its derived limit as its ordinary
   limit. Finite sums and projectors commute with the limit, and the exact functor $R\lim$ of [lem-
   weil-pbc-ringed-strict-tower-homotopy-limit] commutes with the finitely many cones constructing
   the bounded complex. Thus the same differential matrices occur after the limit. All maps used are
   the constant-section and quotient maps, so this calculation respects their transitions.

4. Base change the chosen strata and covers to $W$. By [lemma-constructible-pullback-
   stratification], $S'_\alpha=W\times_XS_\alpha\to W$ is a finite stratification; its strata are
   constructible by [lem-pur-scheme-constructible-preimage]. The base changes $V'_{\alpha
   t}=W\times_XV_{\alpha t}\to S'_\alpha$ cover in the pro-etale topology, by its base-change-stable
   covering definition [def-weil-pbc-proetale-site]. Let $g_{\alpha t}:V'_{\alpha t}\to V_{\alpha
   t}$ be the projection. The two factorizations of $V'_{\alpha t}\to X$, together with the
   composition comparison [lem-pod-integral-pullback-composition], identify $$(Lh^*K)|_{V'_{\alpha
   t}}\cong Lg_{\alpha t}^*(K|_{V_{\alpha t}})\cong B_{V'_{\alpha t}}\otimes_RP_{\alpha
   t}^\bullet.$$ The first isomorphism uses the exact immersion and site restrictions just
   established in Step 2; the second is Step 3. Empty base-changed strata contribute no condition.
   This uses actual fibre-product strata and their projection morphisms.

5. Fix one of the models in Step 4, abbreviating it by $P^\bullet$ on $V$, and put
   $N^j=H^j(P^\bullet)$. The constant-sheaf functor $M\mapsto\underline M$ is exact, since it is
   sectionwise exact by [lem-weil-pbc-constant-module-section-properties](1), so
   $H^j(\underline{P^\bullet})=\underline{N^j}$; tensoring with $B_T$ is exact by flatness of $B_T$
   over the constant ring $R$ in [lem-weil-pbc-completed-constant-sheaf-reduction]. Applying [lem-
   weil-pbc-exact-functor-complex-cohomology] to these two exact functors gives
   $$H^j(B_T\otimes_RP^\bullet)=B_T\otimes_R\underline{N^j}_T\quad(T=V,V').$$ For $j\notin[a,b]$ the
   expression at $V$ is zero by Step 2. Its underived ringed pullback along $g:V'\to V$ is
   $B_{V'}\otimes_R\underline{N^j}_{V'}$: on balanced tensors the identification is
   $b'\otimes(b\otimes n)\mapsto b'g^\sharp(b)\otimes n$, with inverse $b'\otimes n\mapsto
   b'\otimes(1\otimes n)$. Constant sheaves pull back to the same constant module; this follows by
   applying the constant functor and inverse image to a presentation, both being left adjoints, or
   directly from their constant-section universal property [def-weil-pbc-constant-sheaf, def-weil-
   proetale-inverse-image]. Underived pullback sends the zero module to zero. Therefore the
   expression at $V'$ is zero as well. This only uses scalar flatness over $R$, and does not require
   flatness of $B_{V'}$ over $g^{-1}B_V$.

6. The exact restrictions to $S'_\alpha$ and $V'_{\alpha t}$ commute with cohomology as in Step 2.
   For $j\notin[a,b]$, Steps 4-5 show that every such restriction of $\mathcal H^j(Lh^*K)$ vanishes.
   Apply [lem-weil-pbc-noetherian-stratum-detection] on the Noetherian scheme $W$ to its underlying
   abelian sheaf: $\mathcal H^j(Lh^*K)=0$. Thus integral pullback preserves every cohomological
   interval $[a,b]$. In particular if $K$ is in the integral nonpositive half, choose a lower bound
   $a$ and take $b=0$; if it is in the nonnegative half choose an upper bound $b$ and take $a=0$.
   The integral standard classes in [def-weil-constructible-standard-tstructure] are therefore
   preserved. No restriction is imposed on the geometric fibres of $h$.

7. Pass to $E$. Integral pullback is $R$-linear by its termwise scalar action. By [lem-a1-integral-
   pullback-completed-comparison] it is naturally isomorphic on derived complete objects, in
   particular on $D^b_c$, to the strict-tower completed pullback, which preserves shifts and
   distinguished triangles of complete objects by [lem-cbc-completed-pullback-triangles];
   transporting that shift comparison along the natural isomorphism, the integral pullback is exact
   on $D^b_c(X,R)\to D^b_c(W,R)$. Its extension on fractions is precisely the rational pullback of
   [def-weil-derived-pullback-tensor-hom]; [lem-pur-semilinear-scalar-localization] shows it is
   again exact. An object in either rational standard half is, by [def-weil-constructible-standard-
   tstructure], isomorphic after rationalization to an integral object in that half. Applying $Lh^*$
   to this isomorphism and using Step 6 puts its image in the same rational half. This proves both
   required inclusions for $E$. The argument uses the isomorphism closures in the definition, and
   does not infer an integral bound from an arbitrary rational representative.

8. At $\Qlb$, use the objects $(F,M)$ and common-stage morphisms of [def-weil-algebraically-closed-
   coefficients]. Pullback sends this object to $(F,Lh_F^*M)$, and acts on arrows by the scalar-
   extension comparison specified in [def-weil-derived-pullback-tensor-hom]. An object of either
   standard half is isomorphic to such a pair with $M$ in that half at a finite field $F$, by [def-
   weil-constructible-standard-tstructure]. Step 7, applied to $F$, sends it into the required half.
   The functor is exact: a distinguished triangle has a representative at one common finite field,
   and its image there is distinguished by Step 7, hence also in the pair category. This proves
   t-exactness at $\Qlb$.

9. By [prop-constructible-truncations], both standard pairs are bounded t-structures. Steps 7-8 and
   shift compatibility give preservation of both halves at every integer. Apply [lem-pod-texact-
   truncation-comparison] to the exact functor $Lh^*$. Its unique comparisons commute with the
   canonical truncation maps, hence their composite and the shift comparison give the stated natural
   isomorphism $\mathcal H^j(Lh^*K)\cong Lh^*\mathcal H^j(K)$. T-exactness also sends the
   intersection of the two halves into their intersection, the hearts of [def-weil-constructible-
   heart]. A short exact heart sequence gives a distinguished triangle by [lem-weil-heart-short-
   exact-triangles](4); its image is a distinguished triangle with all vertices in the target heart,
   hence is a short exact sequence by the same clause. The heart functor is therefore exact.

10. These comparisons respect finite coefficient extension. Indeed [lem-pur-integral-operations-
   scalar-extension] supplies the natural pullback comparison and its tower compatibility, while
   [prop-constructible-truncations] gives the corresponding compatibility of truncations and their
   natural maps. The natural-transformation and composition assertions of [lem-pod-texact-
   truncation-comparison] imply that the two truncation comparisons obtained by extending the field
   satisfy the same characterizing equations and coincide. The same holds for their composite
   defining $\mathcal H^j$. Thus every map and equality at $\Qlb$ is represented at a common finite
   field and is unchanged upon further extension. No compatibility of arbitrarily chosen splittings
   is needed.

11. Finally let $\bar x:s=\operatorname{Spec}k\to X$ be as in the statement. This is a morphism
   between finite-type $k$-schemes, so apply Step 9 to it. Sections on $s_{\mathrm{proet}}$ are
   exact and commute with cohomology by [lem-weil-point-proetale-sections-exact]. The functor
   $\operatorname{Fib}_s$ is, at $E$, exactly sections followed by tensor with $E$ as in [def-weil-
   finite-coefficient-point]. Tensor with $E=R[1/\pi]$ is exact by [lem-weil-pbc-localization-
   module-exact], so [lem-weil-pbc-exact-functor-complex-cohomology] identifies its cohomology with
   the fibre of the integral cohomology, and the same remains true after rationalization: [prop-
   weil-localized-tstructure] identifies rational truncations with localized integral truncations.
   Combining this with the pullback/cohomology comparison gives $$\operatorname{Fib}_s(L\bar
   x^*\mathcal H^jK)\cong H^j(\operatorname{Fib}_s(L\bar x^*K)).$$ If $K=\mathcal F$ is in the
   heart, $L\bar x^*\mathcal F$ is in the point heart and the same exact functors put its fibre in
   degree zero. At $\Qlb$ apply this at a common finite field; [lem-weil-point-sections-scalar-
   extension] provides the fibre scalar comparisons with their identity and composition
   compatibility. Together with Step 10 these give exactly the final scalar-extension clause. -/
theorem constructible_pullback_t_exact
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : AlgebraicallyClosedCoefficients.Index l Ω)
    {W X : Scheme.{u}} [W.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (h : W ⟶ X) :
    Nonempty (ConstructibleRationalPullbackComparison D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) h) ∧
      Nonempty (ConstructibleCommonStagePullbackComparison D l hl Ω h) := by
  sorry


open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion stageTransition)

/-- The complete finite-scalar and common-stage compatibility clause for the
pullback comparisons. The beta at a common-stage inclusion has the object equality
specified by the recorded pullback, so it cannot be replaced by an arbitrary map.
Source: Bhatt--Scholze 6.8.14(2), 6.8.15; common-stage coefficients
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def ConstructiblePullbackScalarCompatibility
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {W X : Scheme.{u}} [W.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (h : W ⟶ X) : Prop :=
  letI := constructiblePullbackResidueUnits D l hl W
  letI := constructiblePullbackResidueUnits D l hl X
  ∃ (d : ∀ E : Index l Ω,
      ConstructibleRationalPullbackComparison D l hl (Coefficient.{u} l Ω E) h)
    (e : ConstructibleCommonStagePullbackComparison D l hl Ω h),
    (∀ (E L : Index l Ω) (a : E ≤ L),
      ∃ (sX : ConstructiblePullbackComparison
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) X D hl)
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω L) X D hl)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω E) X)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω L) X)
          (sfRationalScalarExtension l (Coefficient.{u} l Ω E) X 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L a)))
        (sW : ConstructiblePullbackComparison
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) W D hl)
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω L) W D hl)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω E) W)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω L) W)
          (sfRationalScalarExtension l (Coefficient.{u} l Ω E) W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
            (coefficientInclusion l Ω E L a))),
        ConstructiblePullbackScalarSquare (d E) (d L) sX sW
          (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
            (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L a) h)) ∧
    (∀ E : Index l Ω,
      ∃ (iX : ConstructiblePullbackComparison
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) X D hl)
          (sfCommonStageStandardTStructure l X Ω D hl)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω E) X)
          (sfCommonStageHeartProperty l X Ω)
          (inclusion (l := l) (Ω := Ω) (Y := X) E))
        (iW : ConstructiblePullbackComparison
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) W D hl)
          (sfCommonStageStandardTStructure l W Ω D hl)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω E) W)
          (sfCommonStageHeartProperty l W Ω)
          (inclusion (l := l) (Ω := Ω) (Y := W) E))
        (β : rationalDerivedPullback l (Coefficient.{u} l Ω E) h ⋙
            inclusion (l := l) (Ω := Ω) (Y := W) E ≅
          inclusion (l := l) (Ω := Ω) (Y := X) E ⋙ commonStageDerivedPullback l Ω h),
        (∀ K : Stage l Ω X E,
          β.symm.app K = eqToIso
            ((commonStageDerivedPullback_existsUnique l Ω h).exists.choose_spec.1
              ((inclusion (l := l) (Ω := Ω) (Y := X) E).obj K))) ∧
        ConstructiblePullbackScalarSquare (d E) e iX iW β)

/-- All pullback cohomology maps descend from a common finite coefficient field,
and remain the same after any further extension, including identity extensions.
Source: Bhatt--Scholze 6.8.14(2), 6.8.15
(blueprint: lem-a1-constructible-pullback-t-exact).
Proof: use Steps 1--9 of constructible_pullback_t_exact at each finite field.
The integral scalar comparisons commute with towers. Uniqueness of the truncation
counit and unit comparisons makes both routes in every scalar square equal.
Compose with the coherent shift comparisons. The recorded common-stage pullback
has the displayed object equality and conjugated representative maps, so these
same comparisons descend, with the prescribed inclusion beta. This is Step 10
of the node, and applies also to equal fields and repeated extensions. -/
theorem constructible_pullback_scalar_compatibility
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {W X : Scheme.{u}} [W.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (h : W ⟶ X) : ConstructiblePullbackScalarCompatibility D l hl Ω h := by
  sorry

/-- The rational point fibre, followed by its recorded fully faithful inclusion in
D(E). This is the given fibre functor, not a new evaluation construction.
Source: blueprint order 1509, clause 3
(blueprint: lem-a1-constructible-pullback-t-exact). -/
abbrev constructiblePointRationalRealization
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :=
  pointRationalFibre D l hl E ⋙ (DerivedCategory.pointFiniteDimensional E).ι

/-- The common-stage point fibre with its recorded faithful realization in D(Ω).
Source: blueprint order 1509, clause 4
(blueprint: lem-a1-constructible-pullback-t-exact). -/
abbrev constructiblePointCommonStageRealization
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :=
  pointQbarFibre D l hl Ω ⋙ DerivedCategory.pointFdQbarRealization l Ω

/-- Exact point evaluation, the natural point-fibre cohomology formula, and the
assertion that a pulled-back heart object has no nonzero-degree point cohomology.
The cohomology on D(E) is for its usual standard t-structure, so is the ordinary
cohomology module regarded as a degree-zero complex.
Source: Bhatt--Scholze Example 6.5.2, 6.8.11(3), 6.8.14(2)
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def ConstructiblePointRationalComparison
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (x : Spec (.of D.k) ⟶ X) : Prop :=
  letI := constructiblePullbackResidueUnits D l hl X
  letI := constructiblePullbackResidueUnits D l hl (Spec (.of D.k))
  ∃ (d : ConstructibleRationalPullbackComparison D l hl E x)
    (f : ConstructiblePullbackComparison
      (sfRationalStandardTStructure l E (Spec (.of D.k)) D hl)
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} E))
      (sfRationalHeartProperty l E (Spec (.of D.k)))
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} E)).heart
      (constructiblePointRationalRealization D l hl E)),
    (∀ j : ℤ, ∃ γ :
        constructibleTruncationCohomology (sfRationalStandardTStructure l E X D hl) j ⋙
          rationalDerivedPullback l E x ⋙ constructiblePointRationalRealization D l hl E ≅
        rationalDerivedPullback l E x ⋙ constructiblePointRationalRealization D l hl E ⋙
          constructibleTruncationCohomology
            (DerivedCategory.TStructure.t (C := ModuleCat.{u} E)) j,
      ∀ K : sfRationalConstructibleCategory l E X,
        γ.app K = (constructiblePointRationalRealization D l hl E).mapIso
            ((d.cohomology j).app K) ≪≫
          (f.cohomology j).app ((rationalDerivedPullback l E x).obj K)) ∧
    ∀ (F : sfRationalHeart l E X) (j : ℤ), j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} E) j).obj
        ((constructiblePointRationalRealization D l hl E).obj
          ((rationalDerivedPullback l E x).obj F.obj)))

/-- The same point-fibre clauses at the actual common-stage coefficient category.
The realization is fully faithful, hence expresses the isomorphism of fibre complexes.
Source: Bhatt--Scholze 6.8.14(2) and the common-stage convention
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def ConstructiblePointCommonStageComparison
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (x : Spec (.of D.k) ⟶ X) : Prop :=
  letI := constructiblePullbackResidueUnits D l hl X
  letI := constructiblePullbackResidueUnits D l hl (Spec (.of D.k))
  ∃ (d : ConstructibleCommonStagePullbackComparison D l hl Ω x)
    (f : ConstructiblePullbackComparison
      (sfCommonStageStandardTStructure l (Spec (.of D.k)) Ω D hl)
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω))
      (sfCommonStageHeartProperty l (Spec (.of D.k)) Ω)
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω)).heart
      (constructiblePointCommonStageRealization D l hl Ω)),
    (∀ j : ℤ, ∃ γ :
        constructibleTruncationCohomology (sfCommonStageStandardTStructure l X Ω D hl) j ⋙
          commonStageDerivedPullback l Ω x ⋙ constructiblePointCommonStageRealization D l hl Ω ≅
        commonStageDerivedPullback l Ω x ⋙ constructiblePointCommonStageRealization D l hl Ω ⋙
          constructibleTruncationCohomology
            (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω)) j,
      ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω X,
        γ.app K = (constructiblePointCommonStageRealization D l hl Ω).mapIso
            ((d.cohomology j).app K) ≪≫
          (f.cohomology j).app ((commonStageDerivedPullback l Ω x).obj K)) ∧
    ∀ (F : sfCommonStageHeart l X Ω) (j : ℤ), j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Ω) j).obj
        ((constructiblePointCommonStageRealization D l hl Ω).obj
          ((commonStageDerivedPullback l Ω x).obj F.obj)))

/-- The point-fibre formula and the degree-zero assertion at both coefficient levels.
Source: Bhatt--Scholze Example 6.5.2, 6.8.11(3), 6.8.14(2)
(blueprint: lem-a1-constructible-pullback-t-exact).
Proof: Steps 1--10 above apply to x, which need not respect the chosen k-structure.
Exact point sections commute with cohomology. Tensoring with E is exact localization;
prop-weil-localized-tstructure identifies the localized integral cohomology and its
truncation maps. Compose this comparison with the canonical pullback comparison.
For a heart object, t-exactness of both functors gives degree-zero concentration.
At the algebraically closed level compute at a common finite field; the given
point-section scalar comparisons preserve the identity and tower comparisons,
so the same point maps descend. This is Step 11 of the node. -/
theorem constructible_pullback_point_fibre
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Index l Ω)
    {X : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (x : Spec (.of D.k) ⟶ X) :
    ConstructiblePointRationalComparison D l hl (Coefficient.{u} l Ω E) x ∧
      ConstructiblePointCommonStageComparison D l hl Ω x := by
  sorry


/-- Point comparison data at a finite stage, in the existing small coefficient model.
Source: Bhatt--Scholze 6.8.14(2); blueprint point-fibre clause
(blueprint: lem-a1-constructible-pullback-t-exact). -/
abbrev ConstructibleRationalPointData
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :=
  ConstructiblePullbackComparison
    (sfRationalStandardTStructure l E (Spec (.of D.k)) D hl)
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} E))
    (sfRationalHeartProperty l E (Spec (.of D.k)))
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} E)).heart
    (constructiblePointRationalRealization D l hl E)

/-- Common-stage point comparison data, with the actual fibre realization.
Source: Bhatt--Scholze 6.8.14(2); blueprint point-fibre clause
(blueprint: lem-a1-constructible-pullback-t-exact). -/
abbrev ConstructibleCommonStagePointData
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :=
  ConstructiblePullbackComparison
    (sfCommonStageStandardTStructure l (Spec (.of D.k)) Ω D hl)
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω))
    (sfCommonStageHeartProperty l (Spec (.of D.k)) Ω)
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω)).heart
    (constructiblePointCommonStageRealization D l hl Ω)

/-- The standard-t-structure comparison data for the recorded exact field extension.
Source: Bhatt--Scholze 6.8.14(2), exact scalar extension
(blueprint: lem-a1-constructible-pullback-t-exact). -/
abbrev ConstructibleFieldScalarData {E L : Type u} [Field E] [Field L] (a : E →+* L) :=
  ConstructiblePullbackComparison
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} E))
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} L))
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} E)).heart
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} L)).heart
    (DerivedCategory.fieldDerivedScalarExtension a)

/-- The finite-stage point square is exactly the recorded sections/scalar comparison,
with the full-subcategory inclusions and transition identification inserted.
Source: blueprint order 1509, point-section scalar comparison
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def constructiblePointFiniteScalarBeta
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E L : Index l Ω) (a : E ≤ L) :
    constructiblePointRationalRealization D l hl (Coefficient.{u} l Ω E) ⋙
        DerivedCategory.fieldDerivedScalarExtension
          (coefficientInclusion l Ω E L a).toRingHom ≅
      stageTransition l Ω (Spec (.of D.k)) E L a ⋙
        constructiblePointRationalRealization D l hl (Coefficient.{u} l Ω L) :=
  Functor.associator
      (pointRationalFibre D l hl (Coefficient.{u} l Ω E))
      (DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω E)).ι
      (DerivedCategory.fieldDerivedScalarExtension
        (coefficientInclusion l Ω E L a).toRingHom) ≪≫
    Functor.isoWhiskerLeft (pointRationalFibre D l hl (Coefficient.{u} l Ω E))
      ((DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω L)).liftCompιIso
        ((DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω E)).ι ⋙
          DerivedCategory.fieldDerivedScalarExtension
            (coefficientInclusion l Ω E L a).toRingHom)
        (fun K ↦ DerivedCategory.fieldDerivedScalarExtension_preserves
          (coefficientInclusion l Ω E L a).toRingHom K.obj K.property)).symm ≪≫
    (Functor.associator (pointRationalFibre D l hl (Coefficient.{u} l Ω E))
      (DerivedCategory.pointFdScalarExtension (coefficientInclusion l Ω E L a).toRingHom)
      (DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω L)).ι).symm ≪≫
    Functor.isoWhiskerRight
      (pointRationalFibreScalarIso D l hl (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L a)).symm
      (DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω L)).ι ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight
      (operationStageTransitionIso l Ω (Spec (.of D.k)) E L a).symm _

/-- The recorded coefficient-model equivalence, with its source carrier explicit.
Source: blueprint common-stage coefficient convention; Shrink.algEquiv
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def constructiblePointCoefficientMap
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Index l Ω) : Coefficient.{u} l Ω E →+* E.val :=
  (Shrink.algEquiv (Padic l) E.val).toRingHom

/-- The actual common-stage fibre object's defining identification after realization.
Source: blueprint order 1509, clause 4; pointQbarFibre's defining object formula
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def constructiblePointCommonStageObjectIso
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Index l Ω) (K : Stage l Ω (Spec (.of D.k)) E) :
    (constructiblePointCommonStageRealization D l hl Ω).obj
        ((inclusion (l := l) (Ω := Ω) (Y := Spec (.of D.k)) E).obj K) ≅
      (DerivedCategory.fieldDerivedScalarExtension E.val.subtype).obj
        ((DerivedCategory.fieldDerivedScalarExtension
          (constructiblePointCoefficientMap l Ω E)).obj
            (((pointRationalFibre D l hl (Coefficient.{u} l Ω E)).obj K).obj)) :=
  (DerivedCategory.pointFdQbarRealization l Ω).mapIso
    (eqToIso ((pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.1
      ((inclusion (l := l) (Ω := Ω) (Y := Spec (.of D.k)) E).obj K)))

/-- The canonical finite-stage to common-stage point comparison component.
It first expands the field tensor tower, then uses the recorded fibre object formula.
Source: blueprint order 1509, clause 4, and Bhatt--Scholze 6.8.14(2)
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def constructiblePointCommonStageScalarComponent
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : Index l Ω) (K : Stage l Ω (Spec (.of D.k)) E) :
    (DerivedCategory.fieldDerivedScalarExtension
        (E.val.subtype.comp (constructiblePointCoefficientMap l Ω E))).obj
          ((constructiblePointRationalRealization D l hl (Coefficient.{u} l Ω E)).obj K) ≅
      (constructiblePointCommonStageRealization D l hl Ω).obj
        ((inclusion (l := l) (Ω := Ω) (Y := Spec (.of D.k)) E).obj K) :=
  (DerivedCategory.fieldScalarTower (K := Coefficient.{u} l Ω E) (L := E.val)
    (M := Ω) (constructiblePointCoefficientMap l Ω E) E.val.subtype).symm.app
      (((pointRationalFibre D l hl (Coefficient.{u} l Ω E)).obj K).obj) ≪≫
    (constructiblePointCommonStageObjectIso D l hl Ω E K).symm

/-- The scalar compatibility of point cohomology, at finite extensions and from a
finite field to the closure. The latter beta is fixed by the actual fibre object
identity and the canonical field tensor tower map. Thus the Qbar point comparison
is the scalar extension of the finite-stage comparison, not an unrelated isomorphism.
Source: Bhatt--Scholze 6.8.14(2); point-sections scalar-extension convention
(blueprint: lem-a1-constructible-pullback-t-exact). -/
def ConstructiblePointScalarCompatibility
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] : Prop :=
  ∃ (f : ∀ E : Index l Ω, ConstructibleRationalPointData D l hl (Coefficient.{u} l Ω E))
    (g : ConstructibleCommonStagePointData D l hl Ω),
    (∀ (E L : Index l Ω) (a : E ≤ L),
      ∃ (s : ConstructiblePullbackComparison
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) (Spec (.of D.k)) D hl)
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω L) (Spec (.of D.k)) D hl)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω E) (Spec (.of D.k)))
          (sfRationalHeartProperty l (Coefficient.{u} l Ω L) (Spec (.of D.k)))
          (stageTransition l Ω (Spec (.of D.k)) E L a))
        (t : ConstructibleFieldScalarData (coefficientInclusion l Ω E L a).toRingHom),
        t.commShift = (inferInstance :
          (DerivedCategory.fieldDerivedScalarExtension
            (coefficientInclusion l Ω E L a).toRingHom).CommShift ℤ) ∧
        ConstructiblePullbackScalarSquare (f E) (f L) s t
          (constructiblePointFiniteScalarBeta D l hl Ω E L a)) ∧
    (∀ E : Index l Ω,
      ∃ (s : ConstructiblePullbackComparison
          (sfRationalStandardTStructure l (Coefficient.{u} l Ω E) (Spec (.of D.k)) D hl)
          (sfCommonStageStandardTStructure l (Spec (.of D.k)) Ω D hl)
          (sfRationalHeartProperty l (Coefficient.{u} l Ω E) (Spec (.of D.k)))
          (sfCommonStageHeartProperty l (Spec (.of D.k)) Ω)
          (inclusion (l := l) (Ω := Ω) (Y := Spec (.of D.k)) E))
        (t : ConstructibleFieldScalarData
          (E.val.subtype.comp (constructiblePointCoefficientMap l Ω E)))
        (β : constructiblePointRationalRealization D l hl (Coefficient.{u} l Ω E) ⋙
            DerivedCategory.fieldDerivedScalarExtension
              (E.val.subtype.comp (constructiblePointCoefficientMap l Ω E)) ≅
          inclusion (l := l) (Ω := Ω) (Y := Spec (.of D.k)) E ⋙
            constructiblePointCommonStageRealization D l hl Ω),
        t.commShift = (inferInstance :
          (DerivedCategory.fieldDerivedScalarExtension
            (E.val.subtype.comp (constructiblePointCoefficientMap l Ω E))).CommShift ℤ) ∧
        (∀ K : Stage l Ω (Spec (.of D.k)) E,
          β.app K = constructiblePointCommonStageScalarComponent D l hl Ω E K) ∧
        ConstructiblePullbackScalarSquare (f E) g s t β)

/-- The finite-stage and algebraically closed point comparisons satisfy the canonical
scalar squares, including identity and arbitrary further common-stage enlargements.
Source: Bhatt--Scholze 6.8.14(2); point-sections scalar-extension convention
(blueprint: lem-a1-constructible-pullback-t-exact).
Proof: exact sections followed by exact localization gives the rational comparison.
The given pointRationalFibreScalarIso is the normalized sections/tensor map, so
uniqueness of the truncation comparisons identifies the two routes in its square.
For a pair (E,K), pointQbarFibre has the specified pointStageFibre object, realized
by extension from the Shrink coefficient model through E to Ω. The canonical
fieldScalarTower is exactly that identification. Its unit and tower coherence,
and the identical coherence of point-section scalar extension, identify the
comparisons after every further common field. Thus these fibre comparisons,
composed with the scalar-compatible pullback comparisons above, are precisely
the point-fibre maps of the node's last clause (Step 11, following Step 10). -/
theorem constructible_point_scalar_compatibility
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :
    ConstructiblePointScalarCompatibility D l hl Ω := by
  sorry

end WeilConjectures
