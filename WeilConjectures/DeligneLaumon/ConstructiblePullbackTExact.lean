/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.ConstructiblePullbackComparisonData
public import WeilConjectures.DeligneLaumon.ConstructiblePointComparisonData
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.DeligneLaumon.ConstructibleTruncations
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldDerivedScalarTower

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfConstructibleHeart
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.DeligneLaumon.PointRealizationHeartExact
import WeilConjectures.DeligneLaumon.PointRealizationStandardCohomology
import WeilConjectures.DeligneLaumon.PointScalarBetaNormalization
import WeilConjectures.DeligneLaumon.PointFiniteScalarCohomology
import WeilConjectures.DeligneLaumon.PointCommonScalarCohomology

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
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v uC vC uB vB uD vD uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry

namespace WeilConjectures

-- Keep the point targets in their published small derived Hom universe when the chart API
-- imports the residue-lisse standard-size localization instance. This preference is file-local.
attribute [local instance 2000] HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local irreducible] sfRationalStandardTStructure sfCommonStageStandardTStructure
  pointRationalFibre
  DerivedCategory.TStructure.t ModuleCat.extendScalars

private theorem square_of_point
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
    (pF : PointRealizationComparison t s F) (pG : PointRealizationComparison r a G)
    (pS : PointRealizationComparison t r S) (pT : PointRealizationComparison s a T)
    (hF : dF.cohomology = pF.delta) (hG : dG.cohomology = pG.delta)
    (hS : dS.cohomology = pS.delta) (hT : dT.cohomology = pT.delta)
    (β : F ⋙ T ≅ S ⋙ G)
    (h : PointRealizationCohomologySquare pF pG pS pT β.symm) :
    ConstructiblePullbackScalarSquare dF dG dS dT β := by
  intro j K
  rw [hF, hG, hS, hT]
  let H := constructibleTruncationCohomology a j
  have hh := congrArg
    (fun f ↦ β.hom.app ((constructibleTruncationCohomology t j).obj K) ≫
      f ≫ H.map (β.hom.app K)) (h j K)
  simpa [H, Category.assoc, ← H.map_comp] using hh.symm

private theorem module_shift_additive (E : Type u) [Field E] :
    ∀ n : ℤ, (shiftFunctor (DerivedCategory (ModuleCat.{u} E)) n).Additive := by
  intro n
  infer_instance

attribute [local instance] module_shift_additive

section Composite

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasZeroObject A]
  [HasShift A ℤ] [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
  {t : TStructure C} {s : TStructure B} {r : TStructure A}
  {P : ObjectProperty C} {Q : ObjectProperty B} {U : ObjectProperty A}
  {F : C ⥤ B} {G : B ⥤ A}

private theorem comparison_composite_cohomology
    (d : ConstructiblePullbackComparison t s P Q F)
    (e : ConstructiblePullbackComparison s r Q U G) (j : ℤ) :
    ∃ γ : constructibleTruncationCohomology t j ⋙ F ⋙ G ≅
        F ⋙ G ⋙ constructibleTruncationCohomology r j,
      ∀ K : C, γ.app K = G.mapIso ((d.cohomology j).app K) ≪≫
        (e.cohomology j).app (F.obj K) := by
  refine ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (d.cohomology j) G ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F (e.cohomology j), ?_⟩
  intro K
  apply Iso.ext
  simp

private theorem comparison_composite_heart
    (d : ConstructiblePullbackComparison t s P Q F)
    (e : ConstructiblePullbackComparison s r Q U G) (K : P.FullSubcategory) :
    U (G.obj (F.obj K.obj)) := by
  have hd : (d.heart.obj K).obj = F.obj K.obj :=
    congrArg (fun H : P.FullSubcategory ⥤ B ↦ H.obj K) d.heart_fac
  have he : (e.heart.obj (d.heart.obj K)).obj = G.obj ((d.heart.obj K).obj) :=
    congrArg (fun H : Q.FullSubcategory ⥤ A ↦ H.obj (d.heart.obj K)) e.heart_fac
  rw [← hd, ← he]
  exact (e.heart.obj (d.heart.obj K)).property

end Composite

section PointComparison

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
  [IsTriangulated B]
  {t : TStructure C} {s : TStructure B} {F : C ⥤ B}

private theorem comparison_of_point
    (d : PointRealizationComparison t s F) (P : ObjectProperty C) (Q : ObjectProperty B)
    (hP : t.heart = P) (hQ : s.heart = Q) :
    ∃ e : ConstructiblePullbackComparison t s P Q F,
      e.commShift = d.commShift ∧ e.cohomology = d.delta := by
  subst P Q
  let e : ConstructiblePullbackComparison t s t.heart s.heart F :=
    { tExact := d.tExact
      heart := pointRealizationHeartFunctor d
      heart_fac := rfl
      heart_limits := (pointRealizationHeart_exact d).1
      heart_colimits := (pointRealizationHeart_exact d).2
      commShift := d.commShift
      truncLE := d.upper
      truncLE_counit := d.upper_counit
      truncGE := d.lower
      truncGE_unit := d.lower_unit
      cohomology := d.delta
      cohomology_formula := by
        intro j K
        apply Iso.ext
        change (d.delta j).hom.app K = _
        simp [PointRealizationComparison.delta, constructibleTruncationCohomology] }
  exact ⟨e, rfl, rfl⟩

end PointComparison

private theorem derived_heart_homology_zero
    {E : Type u} [Field E] (K : DerivedCategory (ModuleCat.{u} E))
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{u} E)).heart K)
    (j : ℤ) (hj : j ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} E) j).obj K) := by
  have : K.IsLE 0 := ⟨hK.1⟩
  have : K.IsGE 0 := ⟨hK.2⟩
  rcases lt_or_gt_of_ne hj with h | h
  · exact DerivedCategory.isZero_of_isGE K 0 j h
  · exact DerivedCategory.isZero_of_isLE K 0 j h

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
attribute [local irreducible] constructiblePullbackResidueUnits
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion stageTransition)

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
  obtain ⟨d, e, _⟩ := constructible_pullback_scalar_compatibility D l hl Ω h
  exact ⟨⟨d E⟩, ⟨e⟩⟩


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
  classical
  obtain ⟨P⟩ := pointRealizationStandardCohomology D l hl Ω
  have hf := fun E : Index l Ω ↦ comparison_of_point
    (P.finite (Coefficient.{u} l Ω E))
    (sfRationalHeartProperty l (Coefficient.{u} l Ω E) (Spec (.of D.k)))
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} (Coefficient.{u} l Ω E))).heart
    (sfRationalHeart_properties l (Coefficient.{u} l Ω E) (Spec (.of D.k)) D hl).1 rfl
  choose f _hfshift hfcoh using hf
  obtain ⟨g, _, hgcoh⟩ := comparison_of_point P.common
    (sfCommonStageHeartProperty l (Spec (.of D.k)) Ω)
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω)).heart
    (sfCommonStageHeart_properties l (Spec (.of D.k)) Ω D hl).1 rfl
  refine ⟨f, g, ?_, ?_⟩
  · intro E L a
    obtain ⟨s₀, hs₀⟩ := pointFiniteScalarCohomology D l hl Ω
      P.toPointRealizationFiniteCohomologyData E L a
      (constructiblePointFiniteScalarBeta D l hl Ω E L a)
      (pointFiniteScalarBeta_normalization D l hl Ω E L a)
    obtain ⟨s, _, hs⟩ := comparison_of_point s₀
      (sfRationalHeartProperty l (Coefficient.{u} l Ω E) (Spec (.of D.k)))
      (sfRationalHeartProperty l (Coefficient.{u} l Ω L) (Spec (.of D.k)))
      (sfRationalHeart_properties l (Coefficient.{u} l Ω E) (Spec (.of D.k)) D hl).1
      (sfRationalHeart_properties l (Coefficient.{u} l Ω L) (Spec (.of D.k)) D hl).1
    obtain ⟨t, htshift, ht⟩ := comparison_of_point
      (pointFieldComparison (coefficientInclusion l Ω E L a).toRingHom)
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} (Coefficient.{u} l Ω E))).heart
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} (Coefficient.{u} l Ω L))).heart
      rfl rfl
    refine ⟨s, t, htshift.trans ?_, ?_⟩
    · exact (pointExactDerivedComparison_existsUnique
        (ModuleCat.extendScalars.{u, u, u}
          (coefficientInclusion l Ω E L a).toRingHom)).exists.choose_spec.1
    · exact square_of_point (f E) (f L) s t _ _ _ _
        (hfcoh E) (hfcoh L) hs ht _ hs₀
  · intro E
    obtain ⟨t₀, β, ht₀, hβ, hsq⟩ := pointCommonScalarCohomology D l hl Ω P E
    obtain ⟨s, _, hs⟩ := comparison_of_point (P.inclusion E)
      (sfRationalHeartProperty l (Coefficient.{u} l Ω E) (Spec (.of D.k)))
      (sfCommonStageHeartProperty l (Spec (.of D.k)) Ω)
      (sfRationalHeart_properties l (Coefficient.{u} l Ω E) (Spec (.of D.k)) D hl).1
      (sfCommonStageHeart_properties l (Spec (.of D.k)) Ω D hl).1
    obtain ⟨t, htshift, ht⟩ := comparison_of_point
      (C := DerivedCategory (ModuleCat.{u} (Coefficient.{u} l Ω E)))
      (B := DerivedCategory (ModuleCat.{u} Ω)) t₀
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} (Coefficient.{u} l Ω E))).heart
      (DerivedCategory.TStructure.t (C := ModuleCat.{u} Ω)).heart rfl rfl
    refine ⟨s, t, β, htshift.trans ht₀, ?_, ?_⟩
    · intro K
      apply Iso.ext
      dsimp only [constructiblePointCommonStageScalarComponent,
        constructiblePointCommonStageObjectIso, constructiblePointCoefficientMap]
      exact congrArg Iso.hom (hβ K)
    · exact square_of_point (f E) g s t _ _ _ _ (hfcoh E) hgcoh hs ht β hsq

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
  let := constructiblePullbackResidueUnits D l hl X
  let := constructiblePullbackResidueUnits D l hl (Spec (.of D.k))
  obtain ⟨d, e, _⟩ := constructible_pullback_scalar_compatibility D l hl Ω x
  obtain ⟨f, g, _⟩ := constructible_point_scalar_compatibility D l hl Ω
  constructor
  · refine ⟨d E, f E, ?_, ?_⟩
    · exact comparison_composite_cohomology
        (A := DerivedCategory (ModuleCat.{u} (Coefficient.{u} l Ω E))) (d E) (f E)
    · intro F j hj
      exact derived_heart_homology_zero _
        (comparison_composite_heart
          (A := DerivedCategory (ModuleCat.{u} (Coefficient.{u} l Ω E))) (d E) (f E) F) j hj
  · refine ⟨e, g, ?_, ?_⟩
    · exact comparison_composite_cohomology (A := DerivedCategory (ModuleCat.{u} Ω)) e g
    · intro F j hj
      exact derived_heart_homology_zero _
        (comparison_composite_heart (A := DerivedCategory (ModuleCat.{u} Ω)) e g F) j hj

end WeilConjectures
