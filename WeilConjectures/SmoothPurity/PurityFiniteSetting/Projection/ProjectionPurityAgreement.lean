/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionPurityCoordinates
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionTensorIntegration
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorAmplitude

/-! # Agreement of the smooth and ordered affine-space purity maps

Source: the model paragraph of the smooth-purity blueprint unit.
(blueprint: lem-pur-projection-purity-agreement).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AffineSpacePurity

set_option backward.isDefEq.respectTransparency false in
private theorem projectionPresentation_exists
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    (K : Scheme.proEtaleDerivedCategory Y (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) Y K) :
    ∃ _hb : boundedBelow (projectionSetting F C E n).Coefficient Y
        ((Scheme.sfIntrinsicDerivedEquivalence Y (projectionSetting F C E n).Ring).inverse.obj K),
      ∃ Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient Y,
        ∃ _hKe : etaleFiniteTor (projectionSetting F C E n).Coefficient Y Ke,
          Nonempty ((ProEtale.VectorIntegrationSite.comparison
            (projectionSetting F C E n).Coefficient Y).obj Ke ≅
              (Scheme.sfIntrinsicDerivedEquivalence Y
                (projectionSetting F C E n).Ring).inverse.obj K) := by
  classical
  let P := projectionSetting F C E n
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y
  let D := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
  have hc := (Scheme.finiteRing_constructibleDerived_origin Y P.Ring).2.2.1 K
  have hOrigin : (ObjectProperty.ι
      (Etale.DerivedCategory.isBoundedConstructible P.Coefficient Y) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison Y P.Ring).essImage K := by
    apply hc.mpr
    refine ⟨hK.1.2, ?_⟩
    obtain ⟨a, ha⟩ := hK.1.1.bddBelow
    obtain ⟨b, hb⟩ := hK.1.1.bddAbove
    refine ⟨min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
    by_contra hn
    rcases hi with hi | hi
    · exact (not_lt_of_ge ((min_le_left a b).trans (ha hn))) hi
    · exact (not_lt_of_ge ((hb hn).trans (le_max_right a b))) hi
  obtain ⟨J, ⟨eJ⟩⟩ := hOrigin
  let : (Scheme.sfIntrinsicModuleEquivalence Y P.Ring).functor.Additive :=
    inferInstanceAs (ProEtale.finiteCoefficientIntrinsicRealization Y P.Ring).Additive
  let ecomp := (Functor.mapDerivedCategoryCompIso ν
    (Scheme.sfIntrinsicModuleEquivalence Y P.Ring).functor).app J.obj
  let e : ν.mapDerivedCategory.obj J.obj ≅ D.inverse.obj K :=
    D.functor.preimageIso (ecomp.symm ≪≫ eJ ≪≫ (D.counitIso.app K).symm)
  have hp : _root_.DerivedCategory.TStructure.t.plus J.obj := by
    obtain ⟨a, b, _, hz⟩ := J.property.2
    exact ⟨a, (_root_.DerivedCategory.isGE_iff J.obj a).mpr
      (fun i hi ↦ hz i (.inl hi))⟩
  have hb : boundedBelow P.Coefficient Y (D.inverse.obj K) :=
    _root_.DerivedCategory.TStructure.t.plus.prop_of_iso e
      (ProEtale.DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hp).plus
  obtain ⟨a, b, ht⟩ := hK.2
  let : ∀ x : Y, Invertible (C.l : Y.residueField x) :=
    fun x ↦ (show IsUnit (C.l : Y.residueField x) by
      simpa only [map_natCast] using
        (P.coefficientPrime_isUnit_stalk Y aY x).map (Y.residue x).hom).invertible
  have htor := AlgebraicGeometry.finiteCoefficient_comparison_reflects_torAmplitude
    F C.l C.different E (n + 1) (Nat.succ_pos n) Y a b J.obj hp
    K hK.1 ht eJ.symm
  have hbc : Etale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} P.Coefficient) Y J.obj := by
    obtain ⟨hc, a, b, hab, hv⟩ := J.property
    refine ⟨⟨⟨a, (_root_.DerivedCategory.isGE_iff _ a).mpr
      (fun i hi ↦ hv i (Or.inl hi))⟩,
      ⟨b, (_root_.DerivedCategory.isLE_iff _ b).mpr
        (fun i hi ↦ hv i (Or.inr hi))⟩⟩, ?_⟩
    intro i
    exact (Etale.constructibleSheaf_iff _ _ _).mpr
      ((Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i))
  exact ⟨hb, J.obj, ⟨hbc, a, b,
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp htor⟩, ⟨e⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem projectionIntegration_independent
    (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke Ke' : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (hKe' : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke')
    (eK : (ProEtale.VectorIntegrationSite.comparison
      (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj)
    (eK' : (ProEtale.VectorIntegrationSite.comparison
      (AffineLinePurity.Ring P) Y).obj Ke' ≅ K.obj) (d : ℕ) :
    ProEtale.AffineOrderedIntegration.integrationTranspose P Y aY K Ke hKe eK d =
      ProEtale.AffineOrderedIntegration.integrationTranspose P Y aY K Ke' hKe' eK' d := by
  have h := (ProEtale.AffineOrderedIntegration.integrationTranspose_existsUnique
    P Y aY K Ke hKe eK d).exists.choose_spec
  have h' := (ProEtale.AffineOrderedIntegration.integrationTranspose_existsUnique
    P Y aY K Ke' hKe' eK' d).exists.choose_spec
  have hr : HEq
      (ProEtale.AffineOrderedIntegration.integrationTransposeRaw P Y aY K Ke hKe eK d).2.2
      (ProEtale.AffineOrderedIntegration.integrationTransposeRaw P Y aY K Ke' hKe' eK' d).2.2 := by
    cases d <;> rfl
  unfold ProEtale.AffineOrderedIntegration.integrationTranspose
  exact eq_of_heq (h.trans (hr.trans h'.symm))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine-line composite has a unique presentation-independent realization on
K itself. Quantification over every etale presentation specifies its map completely;
existence of presentations follows from hK and is not an extra hypothesis.
Source: the affine-line construction and its ordered composite
(blueprint: lem-pur-projection-purity-agreement).
Proof: finite type over k makes Y Noetherian. The constructible-origin theorem and
finite-Tor comparison supply an etale finite-Tor representative of K and a lower bound.
The affine-line map is the specified exceptional transpose of the projection/integration
composite, so naturality of the Hom bijection identifies its maps under every change
of representative. The ordered recursion preserves this identity, using the canonical
pullback, Tate and exceptional compositors. The source root-power and tensor comparisons
and target identity comparison are natural in the same presentations. Hence their
conjugated composite has one value on every representative. Apply the intrinsic
realization functor. This constructs g and proves its defining equations. Any two
candidates agree using one of the available presentations, proving uniqueness. -/
theorem projectionAffineIntrinsic_existsUnique
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Scheme.proEtaleDerivedCategory Y (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) Y K) (d : ℕ) :
    ∃! g : ProjectionIntrinsicHom (projectionSetting F C E n) Y aY K d,
      ∀ (hb : boundedBelow (projectionSetting F C E n).Coefficient Y
        ((Scheme.sfIntrinsicDerivedEquivalence Y (projectionSetting F C E n).Ring).inverse.obj
          K))
        (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient Y)
        (hKe : etaleFiniteTor (projectionSetting F C E n).Coefficient Y Ke)
        (eK : (ProEtale.VectorIntegrationSite.comparison
          (projectionSetting F C E n).Coefficient Y).obj Ke ≅
            (Scheme.sfIntrinsicDerivedEquivalence Y (projectionSetting F C E n).Ring).inverse.obj
              K),
        g = (Scheme.sfIntrinsicDerivedEquivalence (iteratedAffineLine Y d)
          (projectionSetting F C E n).Ring).functor.map
            (projectionAffineInPresentation F C E n Y aY
              ⟨(Scheme.sfIntrinsicDerivedEquivalence Y
                (projectionSetting F C E n).Ring).inverse.obj K, hb⟩ Ke hKe eK d) := by
  classical
  let P := projectionSetting F C E n
  obtain ⟨hb, Ke, hKe, ⟨eK⟩⟩ := projectionPresentation_exists F C E n Y aY K hK
  let Kp : Plus P.Coefficient Y :=
    ⟨(Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K, hb⟩
  let R := (Scheme.sfIntrinsicDerivedEquivalence (iteratedAffineLine Y d) P.Ring).functor
  refine ⟨R.map (projectionAffineInPresentation F C E n Y aY Kp Ke hKe eK d), ?_, ?_⟩
  · intro hb' Ke' hKe' eK'
    have hh : hb' = hb := Subsingleton.elim _ _
    subst hb'
    apply congrArg R.map
    let := projectionTarget_isIso F C E n Y aY Kp Ke hKe eK d
    dsimp only [projectionAffineInPresentation]
    apply congrArg (fun t ↦ (projectionSourceIso F C E n Y aY Kp.obj d).hom ≫ t ≫
      inv (projectionTargetMap F C E n Y aY Kp.obj d))
    rw [← (ProEtale.AffineOrderedIntegration.ordered_integration_transposes
      P Y aY Kp Ke hKe eK).1 d,
      ← (ProEtale.AffineOrderedIntegration.ordered_integration_transposes
        P Y aY Kp Ke' hKe' eK').1 d]
    exact projectionIntegration_independent P Y aY Kp Ke Ke' hKe hKe' eK eK' d
  · intro g hg
    exact hg hb Ke hKe eK

/-- The ordered affine-line comparison on the original K. The existence-and-uniqueness
statement fixes the arrow by its value in every presentation, rather than choosing an
object or an orientation from mere existence.
Source: Gamma_(p_d,K) (blueprint: lem-pur-projection-purity-agreement). -/
def projectionAffineIntrinsic
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Scheme.proEtaleDerivedCategory Y (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) Y K) (d : ℕ) :
    ProjectionIntrinsicHom (projectionSetting F C E n) Y aY K d :=
  projectionChooseUnique (projectionAffineIntrinsic_existsUnique F C E n Y aY K hK d)

/-- The recorded smooth purity map at the affine projection. The required source
structure over k is its projection followed by aY, and the geometric instances
follow from polynomial charts; none is an additional hypothesis.
Source: def-pur-smooth-purity-map (blueprint: lem-pur-projection-purity-agreement). -/
def projectionSmoothIntrinsicRaw (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
    (d : ℕ) :
    Σ M N : Scheme.proEtaleDerivedCategory (iteratedAffineLine Y d) P.Ring, M ⟶ N :=
  let : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
  let : (iteratedAffineLine Y d).Over (Spec (.of P.field.k)) := ⟨towerBase aY d⟩
  letI : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aY)
  letI : QuasiCompact (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact aY)
  letI : LocallyOfFiniteType (iteratedAffineLine Y d ↘ Spec (.of P.field.k)) :=
    (tower_geometry aY d).1
  letI : QuasiCompact (iteratedAffineLine Y d ↘ Spec (.of P.field.k)) :=
    (tower_geometry aY d).2.1
  letI : (iteratedAffineLineProj Y d).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI := (projection_geometry Y d).1
  letI := projection_smooth Y d
  ⟨_, _, P.smoothPurityMap (iteratedAffineLineProj Y d) d K hK⟩

/-- The recorded smooth map has the displayed intrinsic source and exceptional target.
This fixes its hom by literal heterogeneous equality, without changing its orientation.
Source: def-pur-smooth-purity-map (blueprint: lem-pur-projection-purity-agreement).
Proof: the installed Over structures have maps aY and p_d followed by aY. Their
finite-type instances are the original base instances and tower_geometry. Unfold
smoothPurityMap and its tensor source. Its source and target are precisely the two
objects in ProjectionIntrinsicHom. Transport the raw map along those endpoint equalities;
HEq fixes the hom uniquely. No purity equality is used in this endpoint check. -/
theorem projectionSmoothIntrinsic_existsUnique
    (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
    (d : ℕ) :
    ∃! g : ProjectionIntrinsicHom P Y aY K d,
      HEq g (projectionSmoothIntrinsicRaw P Y aY K hK d).2.2 := by
  refine ⟨(projectionSmoothIntrinsicRaw P Y aY K hK d).2.2, HEq.refl _, ?_⟩
  intro g hg
  exact eq_of_heq hg

/-- The actual recorded smooth map in the common intrinsic Hom coordinates.
Source: def-pur-smooth-purity-map (blueprint: lem-pur-projection-purity-agreement). -/
def projectionSmoothIntrinsic (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
    (d : ℕ) : ProjectionIntrinsicHom P Y aY K d :=
  projectionChooseUnique (projectionSmoothIntrinsic_existsUnique P Y aY K hK d)

/-- Smooth purity for the affine-space projection agrees with the ordered composite
of the affine-line integration transposes, at every positive coefficient level.
The orientation in smoothPurityMap is the recorded normalized diagonal/DNC orientation.
The affine composite uses the actual open-counit restriction of projective-line trace.
Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
lem-pur-projection-purity-agreement (blueprint: lem-pur-projection-purity-agreement).

Proof (the DAG route, with its prerequisite nodes):
1. Choose $r\geq1$ with $\ell^r A=0$. Apply [lem-pur-vector-integration-site-comparison] to the
   trivial bundle over each base used here. Its statement gives the coherent specified Tate
   realization, the equality of the projective-line decompositions and traces, the open-counit
   restriction to $I_S$, and independence of $r$. Thus the displayed definition of each affine-line
   $\Gamma$ and its ordered composites is independent of $r$. This cites the coefficient and Kummer
   comparison as an existing lemma, rather than re-proving it using an empty divisor.
2. For $K$, choose the bounded constructible etale representative $K^e$ of [lem-sf-proetale-
   constructible-origin](ii). By [lem-sf-comparison-tor-amplitude](ii) it has the finite Tor
   interval of $K$, so [lem-pur-vector-integration-site-comparison] compares the actual
   projection/integration transposes on these inputs. Every scheme in the coordinate and projective
   compactification towers is finite type over $k$, hence Noetherian by [lem-weil-pbc-finite-type-
   over-noetherian] and of finite dimension by [lem-kun-dimension-finite-type]. Their projective
   compactifications therefore have integer dimension bounds. The source inputs are bounded etale-
   origin objects, so the Hom bijections of [thm-sf-ambient-adjoint-class] apply. Empty schemes have
   the unique maps between zero objects.
3. Put $p=p_d$, $X=\mathbf A^d_Y$ and $W=X\times_YX$. The projection $p$ is smooth of pure relative
   dimension $d$ by [sbc-lem-affine-space-smooth]. The diagonal base-change isomorphism is
   $\alpha:C(p_1,\Delta)\to\omega_p$ of [lem-pur-diagonal-base-change]; the section invariant is
   [def-pur-section-invariant]. The diagonal is regular of codimension $d$, with normal bundle
   $T_{X/Y}$ by [lem-pur-diagonal-regular-immersion]. In coordinates $(x,y)$, the isomorphism
   $h(x,y)=(x,u=y-x)$ has inverse $(x,u)\mapsto(x,x+u)$, takes $\Delta$ to zero, and sends its
   conormal basis $y_i-x_i$ to $u_i$. Thus its normal-coordinate basis is unchanged. The schemes and
   morphisms here are separated finite type by their polynomial charts; for $d=0$ the coordinate
   lists are empty.
4. The extracted lemma [lem-pur-affine-translation-trace], applied over $X$ to the section
   $(x_1,\ldots,x_d)$, says exactly that $h$ preserves the normalized integration. The actual site
   and transpose comparisons are [lem-pur-vector-integration-site-comparison] and the Hom bijections
   of [thm-sf-ambient-adjoint-class]. Applying those functors and bijections to the trace equality
   shows that the integration-transposed comparison is unchanged by $h$. This is the translation
   argument of the unit model paragraph, including the universal parameter and base-change
   normalization.
5. For any rank-$d$ trivial bundle $q$, write $P_{q,K}:Lq^*K(d)[2d]\to Rq^!K$ for the integration
   transpose, which is invertible by [thm-amb-vector-bundle-purity] and [lem-pur-vector-integration-
   site-comparison]. The integration is [def-amb-vector-integration]. Put $L=A_X(d)[2d]$,
   $P=P_{p,A_Y}$, $L'=A_W(d)[2d]$, and $J=P_{p_1,A_X}$. Let $B:Lp_2^*\omega_p\to\omega_{p_1}$ be the
   specified dualizing base-change map. The trace base-change equation is [lem-amb-affine-space-top-
   trace], transported by the site comparison just cited. Therefore [lem-pur-trace-transpose-base-
   change] applied to this square gives $J=B\circ Lp_2^*P$. In [lem-pur-diagonal-base-change],
   $\alpha=(L\Delta^*B)^{-1}$ under $p_2\Delta=1_X$, and hence
$$\alpha\circ L\Delta^*J=P.$$
The
   ordinary Tate restriction $L\Delta^*L'=L$ is the coherent restriction already fixed above.
6. Apply [thm-pur-dnc-invariance] to $(p_1,\Delta)$, obtaining
   $\delta:C(p_1,\Delta)\xrightarrow{\sim}C(\pi_N,0_N)$. In the global coordinates $u_i=y_i-x_i$
   this is a standard affine pair. Its deformation is given by $u_i=t v_i$ and has constant family
   object by the standard-pair clause of [lem-pur-dnc-section-geometry]. The normalization clause of
   the DNC theorem makes $\delta$ the identity between these two standard section invariants. Write
   $\beta=L0_N^*(P_{\pi_N,A_X}^{-1})$, followed by Step 3's ordinary Tate restriction, so
   $\beta:C(\pi_N,0_N)\to A_X(d)[2d]$. The induced normal coordinates $v_i$ use the same ordered
   basis as $u_i$, by Step 3. With Step 4's translation invariance, the standard-pair identity says
   precisely $\beta\delta=(L\Delta^*J)^{-1}$. The explicitly specified diagonal/DNC normalization in
   the statement and in the middle arrow of [def-pur-smooth-purity-map] is
   $\theta_p=\beta\delta\alpha^{-1}$. By Step 5,
   $$\theta_p=(L\Delta^*J)^{-1}\alpha^{-1}=P_{p,A_Y}^{-1}.$$
This checks the actual normalized
   arrows; it does not deduce equality merely from existence of isomorphisms to a twist. In rank
   zero the displayed coordinate lists are empty, the deformation is the constant rank-zero pair,
   and the same equations are identities.
7. The two projection maps at $(L,K)$ and $(\omega_p,K)$ used below are invertible by [lem-weil-
   finite-compact-projection-formula]. Its source coefficients have bounded constructible etale
   witnesses: $L$ is the realized shifted Tate line, and the previous DNC computation gives
   $P:L\xrightarrow{\sim}\omega_p$. Its base coefficient is the witness $K^e$ above, with finite Tor
   interval by [lem-sf-comparison-tor-amplitude](ii). The separated finite-type projection $p$
   therefore satisfies every hypothesis; no Tor condition on an arbitrary source coefficient or six-
   functor datum is assumed.
8. By [def-pur-smooth-purity-map] and the DNC computation, smooth purity is $\theta_{p,K}(1\otimes
   P)$ after the fixed Tate reassociation. Apply [lem-pur-tensor-trace-transpose] with $t=t_p$ and
   $L=A_X(d)[2d]$. It identifies this map with the transpose of $(1_K\otimes t_p)\Pi_{L,K}$. This is
   exactly $P_{p,K}$, by [thm-amb-vector-bundle-purity] and [lem-pur-vector-integration-site-
   comparison]. Thus the smooth map equals the integration transpose for every $K$. The
   tensor/counit identification is now a separate lemma; it is not inferred from naturality in $K$
   alone.
9. For the coordinate tower we need projection compatibility as an identity of maps. For
   $f=q_d:\mathbf A^{d+1}_Y\to\mathbf A^d_Y$ and $g=p_d$, compactify $g$ by $(\mathbf P^1_Y)^d$ and
   take the compatible compactification triangle for $f$ supplied by [lem-weil-pbc-compatible-
   compactification-triangle]. All these schemes are finite type over $k$, hence Noetherian by [lem-
   weil-pbc-finite-type-over-noetherian] and quasi-separated by [lem-weil-pbc-locally-noetherian-
   quasi-separated], so the qcqs hypothesis holds and their opens are quasi-compact. The normalized
   compositor of this triangle is that of [lem-amb-unbounded-compact-support-comparisons]; at the
   finite pro-etale level its proper/open interchange is the evaluation in [lem-cbc-strict-tower-
   proper-open-calculus], and with [lem-sf-class-compact-support-comparison] these are the
   comparisons defining the compositor $\alpha$ of [thm-sf-comp-composition] on the witnessed
   inputs.
10. For the triangle of the preceding step, [lem-sf-composition-projection-mate] states, for
   arbitrary ambient finite-coefficient inputs and the counit-defined projection maps of [def-
   exchange-projection], the identity
$$\operatorname{PF}_{gf;M,N}(\alpha_M\otimes1)
   =\alpha_{M\otimes P_fP_gN}\,Rg_!(\operatorname{PF}_{f;M,P_gN})\,\operatorname{PF}_{g;Rf_!M,N},$$
   with $P_u=Lu^*$ and the canonical pullback, tensor and direct-image associators inserted. By the
   preceding step its $\alpha$ is the actual compositor of [thm-sf-comp-composition] on the
   witnessed inputs used here. No coherence of a six-functor datum is invoked. Clause 3 of [lem-pur-
   finite-projection-action-laws] gives the tensor-action identity for each compactification
   projection map.
11. All inverses in the tower calculation are on the domain of [lem-weil-finite-compact-projection-
   formula]. The source coefficients are shifted Tate lines or their products, and the affine-line
   direct image of such a line is $A$ by [lem-amb-affine-space-top-trace] and [lem-pur-vector-
   integration-site-comparison]. Base factors are $K$, its pullbacks, and their tensors with locally
   free Tate lines. By [lem-sf-pullback-tor-amplitude] these pullbacks are bounded constructible
   with the same finite Tor interval; tensor with a locally free line preserves it, and a shift
   translates it. Etale witnesses exist by [lem-sf-proetale-constructible-origin], and their Tor
   intervals are reflected by [lem-sf-comparison-tor-amplitude](ii). Thus every application of the
   preceding tensor-interchange and projection identities has the required witnessed bounded-below
   and finite-Tor inputs.
12. Work first on the ordinary etale site. For a line projection $q$, [lem-asd-ordinary-
   finite-p1-adjunction] identifies the actual projective-line counit at every coefficient $K$ with
   coefficient tensor the normalized trace after inverse projection. The explicit affine-line
   adjunction of [lem-amb-affine-space-top-trace] composes it with extension by zero. Its counit is
   that projective-line counit composed with $Rq_*$ of the open counit. Naturality of the proper
   projection map in its first variable, applied to the open counit at $A(1)[2]$, and the
   compatibility of the open tensor isomorphism with the open counit (clause 2 of [lem-pur-finite-
   projection-action-laws]) identify its coefficient formula with $(1_K\otimes I_S)\Pi$, where $\Pi$
   is built from the compactification projection map of [def-exchange-projection] for $c=(j,q)$. The
   comparison [lem-pur-vector-integration-site-comparison] carries precisely this formula and its
   transpose to the specified pro-etale line map $\Gamma_{q,K}$. On the originally named domain this
   is [def-pur-affine-line-purity-comparison]. The formulas apply at all $n\geq1$ by the exponent
   independence established above.
13. On the pro-etale site use the explicit affine adjunctions, transported by [lem-pur-vector-
   integration-site-comparison], from the affine adjunctions $F_d\dashv G_d$ of [lem-amb-affine-
   space-top-trace], where $G_dK=p_d^*K(d)[2d]$. Inductively their counits have the coefficient
   formula just established in rank one. Apply [lem-pur-composite-integration-counit] to
   $f=q_d:\mathbf A^{d+1}_Y\to\mathbf A^d_Y$ and $g=p_d$, taking $L_f=A(1)[2]$ and $L_g=A(d)[2d]$.
   The projection hypotheses are the compositor identity and the compactification tensor-action
   identity of the preceding steps, on the verified domains. This lemma makes the composite counit
   $(1_K\otimes t_{p_{d+1}})\Pi$: at the tensor unit it is precisely the trace defining [lem-amb-
   affine-space-top-trace], and [def-amb-vector-integration] uses that trace on a trivial bundle.
   The induction starts from the identity adjunction at $d=0$. Thus the integration transpose
   $P_{p_d,K}$ is the adjunction-preserving comparison with the ordered composite of the explicit
   line adjunctions.
14. The composition convention on exceptional functors is the conjugate of $\alpha$ specified in
   [def-pur-affine-space-comparison], using [thm-sf-comp-composition]. Its ordered recursion uses
   $Rq_d^!Rp_d^!K$ instead of $G_1G_dK$. Naturality of the affine-line transpose gives
   $$\Gamma_{q_d,Rp_d^!K}\,Lq_d^*(P_{p_d,K})(1)[2]
=Rq_d^!(P_{p_d,K})\,\Gamma_{q_d,G_dK}.$$
It
   follows from naturality of the defining projection/integration composite in [def-pur-affine-line-
   purity-comparison], so substitution identifies the recursion with the composite counit just
   computed. Here $G_dK$ has the verified finite-Tor domain, and $Rp_d^!K\cong G_dK$ by the earlier
   integration comparison. The fixed Tate pullback and twist-additivity identifications are those in
   [def-pur-affine-space-comparison]; all shift factors have even degree. Finally [lem-pur-vector-
   integration-site-comparison] carries this counit equality and its transposes to the pro-etale
   site. Hence $P_{p_d,K}=\Gamma_{p_d,K}$; combined with the earlier DNC calculation this is the
   desired agreement. In rank zero all maps are $1_K$, and the calculation also covers $K=0$. -/
theorem projection_purity_agreement
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Scheme.proEtaleDerivedCategory Y (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) Y K) (d : ℕ) :
    projectionSmoothIntrinsic (projectionSetting F C E n) Y aY K hK d =
      projectionAffineIntrinsic F C E n Y aY K hK d := by
  classical
  let P := projectionSetting F C E n
  let : Y.Over (Spec (.of P.field.k)) := ⟨aY⟩
  let : (iteratedAffineLine Y d).Over (Spec (.of P.field.k)) := ⟨towerBase aY d⟩
  let : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aY)
  let : QuasiCompact (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact aY)
  let : LocallyOfFiniteType (iteratedAffineLine Y d ↘ Spec (.of P.field.k)) :=
    (tower_geometry aY d).1
  let : QuasiCompact (iteratedAffineLine Y d ↘ Spec (.of P.field.k)) :=
    (tower_geometry aY d).2.1
  let : (iteratedAffineLineProj Y d).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let := (projection_geometry Y d).1
  let := (projection_geometry Y d).2
  let := projection_smooth Y d
  obtain ⟨hb, Ke, hKe, ⟨eK⟩⟩ := projectionPresentation_exists F C E n Y aY K hK
  let Kp : Plus P.Coefficient Y :=
    ⟨(Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K, hb⟩
  let R := (Scheme.sfIntrinsicDerivedEquivalence (iteratedAffineLine Y d) P.Ring).functor
  have ha : projectionAffineIntrinsic F C E n Y aY K hK d =
      R.map (projectionAffineInPresentation F C E n Y aY Kp Ke hKe eK d) :=
    (projectionAffineIntrinsic_existsUnique F C E n Y aY K hK d).exists.choose_spec
      hb Ke hKe eK
  have hs : projectionSmoothIntrinsic P Y aY K hK d =
      P.smoothPurityMap (iteratedAffineLineProj Y d) d K hK :=
    eq_of_heq (projectionSmoothIntrinsic_existsUnique P Y aY K hK d).exists.choose_spec
  rw [ha, hs]
  exact projection_intrinsic_presentation F C E n Y aY d K hK hb Ke hKe eK


end WeilConjectures.PurityFiniteSetting
