/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSupportCoordinates
public import WeilConjectures.AlgebraicGeometry.EtaleLocalNormalForm

import Mathlib.CategoryTheory.Yoneda
import all WeilConjectures.SecSmoothPurity.ReductionDirectImage
import all WeilConjectures.AlgebraicGeometry.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.SecSmoothPurity.SupportedEtaleTensorOrigin
import WeilConjectures.SecSmoothPurity.OrdinaryChartExceptionalScalar
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local

/-! # Scalar change of evaluated representing pairs
Source: latest blueprint, tower-geometric Levels paragraph.
(blueprint: lem-dla1-tower-representing-pair-scalar-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

private theorem representing_pair_isIso
    {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) (G : B ⥤ A) (adj : F ⊣ G)
    (H : A) (K : B) (eps : F.obj H ⟶ K)
    (h : ∀ M, Function.Bijective (fun z : M ⟶ H ↦ F.map z ≫ eps)) :
    IsIso (adj.homEquiv H K eps) := by
  apply isIso_of_yoneda_map_bijective
  intro M
  convert (adj.homEquiv M K).bijective.comp (h M) using 1
  funext z
  exact (adj.homEquiv_naturality_left z eps).symm

private theorem scalar_pair_transport
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (FA : A ⥤ B) (GA : B ⥤ A) (adjA : FA ⊣ GA)
    (FB : C ⥤ D) (GB : D ⥤ C) (adjB : FB ⊣ GB)
    (S : A ⥤ C) (T : B ⥤ D) (beta : FA ⋙ T ≅ S ⋙ FB)
    (gamma : GA ⋙ S ≅ T ⋙ GB)
    (hc : ∀ K, FB.map (gamma.hom.app K) ≫ adjB.counit.app (T.obj K) =
      beta.inv.app (GA.obj K) ≫ T.map (adjA.counit.app K))
    (H : A) (K : B) (eps : FA.obj H ⟶ K)
    (h : ∀ M, Function.Bijective (fun z : M ⟶ H ↦ FA.map z ≫ eps)) (M : C) :
    Function.Bijective (fun z : M ⟶ S.obj H ↦ FB.map z ≫
      beta.inv.app H ≫ T.map eps) := by
  let a := adjA.homEquiv H K eps
  have : IsIso a := representing_pair_isIso FA GA adjA H K eps h
  let e : S.obj H ≅ GB.obj (T.obj K) := S.mapIso (asIso a) ≪≫ gamma.app K
  have heps : FA.map a ≫ adjA.counit.app K = eps := by
    simpa only [Adjunction.homEquiv_counit] using
      (adjA.homEquiv H K).symm_apply_apply eps
  have he : FB.map e.hom ≫ adjB.counit.app (T.obj K) =
      beta.inv.app H ≫ T.map eps := by
    change FB.map (S.map a ≫ gamma.hom.app K) ≫ _ = _
    rw [FB.map_comp, Category.assoc, hc]
    have hn := beta.inv.naturality a
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc, hn, Category.assoc, ← T.map_comp, heps]
  let E := (e.homToEquiv (Z := M)).trans (adjB.homEquiv M (T.obj K)).symm
  have hE : (fun z : M ⟶ S.obj H ↦ FB.map z ≫
      beta.inv.app H ≫ T.map eps) = E := by
    funext z
    dsimp [E]
    rw [adjB.homEquiv_counit, FB.map_comp, Category.assoc, he]
  rw [hE]
  exact E.bijective

private theorem finite_comparison_isIso
    (ell : ℕ) [Fact ell.Prime]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) (hA : ∃ n : ℕ, (ell : A) ^ n = 0)
    (hB : ∃ n : ℕ, (ell : B) ^ n = 0) (k : Type u) [Field k]
    {X Z Y : Scheme.{u}}
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (j : X ⟶ Z) [IsOpenImmersion j]
    (p : Z ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (M : proEtaleDerivedCategory X A) (hM : spFiniteConstructibleTor X A M) :
    IsIso ((reductionDirectImageComparison phi j p).app M) := by
  have hbounded : Set.Finite {i : ℤ | ¬ IsZero
      ((DerivedCategory.homologyFunctor _ i).obj M)} := by
    obtain ⟨a, b, _, hv⟩ := hM.1
    apply (Set.finite_Icc a b).subset
    intro i hi
    constructor <;> by_contra! hn
    · exact hi (hv i (Or.inl hn))
    · exact hi (hv i (Or.inr hn))
  let E := sfIntrinsicDerivedEquivalence X A
  let K := E.inverse.obj M
  have hK := ProEtale.reductionGood_iso (E.counitIso.app M).symm
    (show ProEtale.ReductionGood X A M from ⟨hbounded, hM.2⟩)
  have hctf := (ProEtale.reductionGood_realization_iff X A K).mp hK
  have hc := ProEtale.DerivedCategory.boundedConstructible_le_boundedConstructibleIntrinsic
    _ hctf.1
  have hcf (i : ℤ) : IsConstructibleProEtaleFixedModuleSheaf X (ULift.{u + 1} A)
      ((DerivedCategory.homologyFunctor _ i).obj K) :=
    (ProEtale.fixed_constructible_iff _ X _).mpr (hc.2 i)
  obtain ⟨L, hL, hLc, e, hJ, hH, hJplus, hHplus, hex⟩ :=
    SupportedEtaleTensorOrigin.supported_etale_tensor_origin ell (Fact.out : ell.Prime)
      phi hA hB j K hc.1 hcf hK.2.2
  let ei : (finiteCoefficientIntrinsicDerivedComparison Z A).obj
        ((SupportedEtaleTensorOrigin.etaleOpen A j).obj L) ≅
      ((sfIntrinsicExtensionByZero j A).mapDerivedCategory).obj M :=
    (FiniteCompactScalar.intrinsicSiteFunctorIso A Z).app _ ≪≫
    (sfIntrinsicDerivedEquivalence Z A).functor.mapIso
      (SupportedEtaleTensorOrigin.supportedComparison A j L K e) ≪≫
    (SupportedEtaleTensorOrigin.openPresentation A j).symm.app K ≪≫
    ((sfIntrinsicExtensionByZero j A).mapDerivedCategory).mapIso (E.counitIso.app M)
  have hi := ProEtale.reductionProper_isIso phi k p
    ((SupportedEtaleTensorOrigin.etaleOpen A j).obj L) hJ hH.1
  have : IsIso ((directImageScalarComparison phi p).app
      (((sfIntrinsicExtensionByZero j A).mapDerivedCategory).obj M)) :=
    (NatTrans.isIso_app_iff_of_iso (directImageScalarComparison phi p) ei).mp hi
  dsimp only [reductionDirectImageComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

private theorem finite_compact_support_ctf
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (hell : IsUnit (ell : k))
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) (c : Compactification f)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, (ell : A) ^ n = 0)
    (M : proEtaleDerivedCategory X A) (hM : spFiniteConstructibleTor X A M) :
    spFiniteConstructibleTor Y A ((reductionCompactSupport A c.i c.g).obj M) := by
  have hchar : ringChar k ≠ ell := by
    intro heq
    apply hell.ne_zero
    rw [← heq]
    exact CharP.cast_eq_zero k (ringChar k)
  have hbounded : Set.Finite {i : ℤ | ¬ IsZero
      ((DerivedCategory.homologyFunctor _ i).obj M)} := by
    obtain ⟨a, b, _, hv⟩ := hM.1
    apply (Set.finite_Icc a b).subset
    intro i hi
    constructor <;> by_contra! hn
    · exact hi (hv i (Or.inl hn))
    · exact hi (hv i (Or.inr hn))
  have htors : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0 := by
    obtain ⟨n, hn⟩ := hA
    exact ⟨n, fun x ↦ by rw [nsmul_eq_mul, Nat.cast_pow, hn, zero_mul]⟩
  have hgood := ProEtale.reductionGood_compactSupport ell (ringChar k) hchar k
    f c.i c.g c.comm.symm A htors M ⟨hbounded, hM.2⟩
  obtain ⟨a, ha⟩ := hgood.1.bddBelow
  obtain ⟨b, hb⟩ := hgood.1.bddAbove
  refine ⟨⟨min a b, b, min_le_right _ _, ?_⟩, hgood.2⟩
  intro i hi
  by_contra hz
  rcases hi with hi | hi
  · exact (not_lt_of_ge (ha hz)) (hi.trans_le (min_le_left _ _))
  · exact (not_lt_of_ge (hb hz)) hi

private theorem smooth_coordinate_chart
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (g : V ⟶ S) [IsSeparated g] (d : ℕ) [SmoothOfRelativeDimension d g] (x : V) :
    ∃ (W : V.Opens) (_ : x ∈ W) (e : W.toScheme ⟶ affineTraceTower S d),
      AlgebraicGeometry.Etale e ∧ IsSeparated e ∧ LocallyOfFiniteType e ∧
        QuasiCompact e ∧ W.ι ≫ g = e ≫ affineTraceProjection S d := by
  obtain ⟨T, W, hT, hW, _, hx, hWT, e₀, he₀, he₀g⟩ :=
    Smooth.exists_etale_to_affineSpace g d x
  have : IsAffine W.toScheme := hW
  have : AlgebraicGeometry.Etale e₀ := he₀
  have : IsOpenImmersion (AffineSpace.map (ULift.{u} (Fin d)) T.ι) :=
    MorphismProperty.of_isPullback
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) T.ι).flip
      (inferInstance : IsOpenImmersion T.ι)
  let a := e₀ ≫ AffineSpace.map (ULift.{u} (Fin d)) T.ι
  have ha : W.ι ≫ g = a ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) := by
    dsimp only [a]
    rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, he₀g,
      Scheme.Hom.resLE_comp_ι]
  have : IsSeparated a := inferInstance
  let e := a ≫ (affineTraceAffineSpaceIso S d).inv
  have : AlgebraicGeometry.Etale e := inferInstance
  have : IsSeparated e := inferInstance
  have : LocallyOfFiniteType e := inferInstance
  have : QuasiCompact e := inferInstance
  refine ⟨W, hx, e, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  have hp : affineTraceToAffineSpace S d ≫
      (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = affineTraceProjection S d :=
    AffineSpace.homOfVector_over _ _
  rw [ha, ← hp]
  change a ≫ _ = a ≫ (affineTraceAffineSpaceIso S d).inv ≫
    (affineTraceAffineSpaceIso S d).hom ≫ _
  rw [Iso.inv_hom_id_assoc]

private theorem ordinary_exceptional_scalar_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (g : V ⟶ S) [HasCompactification g]
    [IsSeparated g] [QuasiCompact g] (d : ℕ) [SmoothOfRelativeDimension d g]
    (K : Etale.DerivedCategoryModule A S) :
    IsIso (Etale.ExceptionalCoefficients.mateMap phi g K) := by
  obtain ⟨MA⟩ := Etale.nonempty_etaleCompactSupportNormalization A
  obtain ⟨MB⟩ := Etale.nonempty_etaleCompactSupportNormalization B
  obtain ⟨tA, PA, _⟩ := Etale.exists_ordinaryFiniteP1Adjunction N hN A hA
  obtain ⟨tB, PB, _⟩ := Etale.exists_ordinaryFiniteP1Adjunction N hN B hB
  choose W hx e he hs hft hqc hg using smooth_coordinate_chart g d
  have hlocal (x : V) :
      IsIso ((Etale.ordinaryFinitePullback B (W x).ι).map
        (Etale.ExceptionalCoefficients.mateMap phi g K)) := by
    have : IsLocallyNoetherian (W x).toScheme := inferInstance
    have : TopologicalSpace.NoetherianSpace (W x).toScheme :=
      (W x).ι.isOpenEmbedding.isInducing.noetherianSpace
    have : CompactSpace (W x).toScheme := TopologicalSpace.NoetherianSpace.compactSpace _
    have : IsNoetherian (W x).toScheme := ⟨⟩
    have : AlgebraicGeometry.Etale (e x) := he x
    have : IsSeparated (e x) := hs x
    have : LocallyOfFiniteType (e x) := hft x
    have : QuasiCompact (e x) := hqc x
    let RA := ProEtale.reductionEtaleChartRightIso A MA g (W x).ι d (e x) (hg x)
      (HasCompactification.compactification g)
      (Etale.rightDerivedUpperShriek A g)
      (Etale.rightDerivedUpperShriekAdjunction A g) N hA tA PA hS
    let RB := ProEtale.reductionEtaleChartRightIso B MB g (W x).ι d (e x) (hg x)
      (HasCompactification.compactification g)
      (Etale.rightDerivedUpperShriek B g)
      (Etale.rightDerivedUpperShriekAdjunction B g) N hB tB PB hS
    have H : IsIso
        ((Etale.scalarPullbackIso phi (W x).ι).inv.app
            ((Etale.rightDerivedUpperShriek A g).obj K) ≫
          (Etale.ordinaryFinitePullback B (W x).ι).map
            (Etale.ExceptionalCoefficients.mateMap phi g K) ≫
          RB.hom.app ((Etale.scalarExtension phi S).obj K)) := by
      rw [← Etale.ordinary_chart_exceptional_scalar phi N hN hA hB hS
        g (W x).ι d (e x) (hg x) MA MB tA tB PA PB K]
      infer_instance
    have := IsIso.of_isIso_comp_left
      ((Etale.scalarPullbackIso phi (W x).ι).inv.app
        ((Etale.rightDerivedUpperShriek A g).obj K))
      ((Etale.ordinaryFinitePullback B (W x).ι).map
        (Etale.ExceptionalCoefficients.mateMap phi g K) ≫
          RB.hom.app ((Etale.scalarExtension phi S).obj K))
    exact IsIso.of_isIso_comp_right _ (RB.hom.app ((Etale.scalarExtension phi S).obj K))
  exact Etale.isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective B
    (fun x ↦ (W x).ι) (fun x ↦ ⟨x, ⟨x, hx x⟩, rfl⟩)
    (Etale.ExceptionalCoefficients.mateMap phi g K) hlocal

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

private theorem tower_level_annihilated (n : ℕ) :
    (l : SpTowerShriek.R l E n) ^ (n + 1) = 0 := by
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.pow_mem_pow (I := spEllIdeal l E)
      (Ideal.subset_span (Set.mem_singleton (l : Padic.coefficientExtensionIntegers l E)))
      (n + 1))
  simpa only [map_pow, map_natCast] using hz

private theorem evaluated_comparison_isIso
    (k : Type u) [Field k]
    (X Y : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (H : SpTowerCalculus.C l E b q X.left) {m n : ℕ} (h : m ≤ n) :
    IsIso ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h)
      c.i c.g).app
        ((spDerivedCoefficientEvaluation l E X.left (q.abelian X.left) n).obj H.obj)) := by
  let : Y.left.Over (Spec (.of k)) := OverClass.ofHom Y.hom
  let : c.Z.Over (Spec (.of k)) := OverClass.ofHom (c.g ≫ Y.hom)
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.hom)
  let : QuasiCompact (Y.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Y.hom)
  let : LocallyOfFiniteType (c.Z ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y.hom))
  let : QuasiCompact (c.Z ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (c.g ≫ Y.hom))
  let : c.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  exact finite_comparison_isIso l (SpTowerCalculus.quotient l E h)
    ⟨n + 1, tower_level_annihilated l E n⟩
    ⟨m + 1, tower_level_annihilated l E m⟩ k c.i c.g _ (H.property.1 n)

/-- Quotient scalar change of the prescribed finite representing pairs.
The only representing-pair hypothesis concerns finite coefficient tests.
Source: latest blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric/
`sk-prop-sp-tower-geometric-gluing.proof.md`, Levels paragraph; finite smooth
purity and the normalized proper scalar comparison.
(blueprint: lem-dla1-tower-representing-pair-scalar-change).

Proof: finite smooth purity gives the finite constructible right adjoint
as the etale pullback followed by the Tate line and relative shift. The
finite Hom hypothesis identifies evaluated H with this right adjoint
applied to evaluated K: use the two universal Hom bijections and Yoneda
inside the full finite constructible finite-Tor category. Their inverse
maps carry the identity to inverse isomorphisms and preserve the prescribed
counits. Derived scalar extension commutes with the pullback, the finite
free Tate line and the shift, hence carries this identified pair to the
finite pair with scalar-extended target. These comparisons preserve the
ordered affine trace and etale fibre-sum counits. For general smooth f,
check this on etale coordinate charts and glue the Hom bijections by the
finite open-cover triangle and five lemma. The finite-Tor proper scalar
comparison is invertible on evaluated H, since H is a tower test. This
supplies hb. The adjunction counit equation expresses the scalar-changed
counit as the inverse of this comparison followed by scalar extension of
the old counit, exactly the displayed formula. For m=n the comparisons are
tensor unitors. Empty schemes and zero objects satisfy the same identities.
No restriction on the characteristic of the perfect ground field is used.
-/
theorem tower_representing_pair_scalar_change
    (k : Type u) [Field k] [PerfectField k] (_hell : IsUnit (l : k))
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (r : ℕ) [SmoothOfRelativeDimension r f.left]
    (c : Compactification f.left)
    (K : SpTowerCalculus.C l E b q Y.left)
    (H : SpTowerCalculus.C l E b q X.left)
    (eps : (SpTowerCalculus.F l E b o q c).obj H.obj ⟶ K.obj)
    (hfinite : ∀ (n : ℕ) (v : SpTowerCalculus.Evaluation l E b o q c n)
      (M : spFiniteConstructibleTorCategory X.left (SpTowerShriek.R l E n)),
      Function.Bijective (fun z : M.obj ⟶
          (spDerivedCoefficientEvaluation l E X.left (q.abelian X.left) n).obj H.obj ↦
        (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map z ≫
          (v.comparison.inv.app H.obj ≫
            (spDerivedCoefficientEvaluation l E Y.left (q.abelian Y.left) n).map eps))) :
    ∀ (m n : ℕ) (h : m ≤ n)
      (v : SpTowerCalculus.Evaluation l E b o q c n),
      ∃ hb : IsIso ((reductionDirectImageComparison (SpTowerCalculus.quotient l E h)
        c.i c.g).app
          ((spDerivedCoefficientEvaluation l E X.left (q.abelian X.left) n).obj H.obj)),
      ∀ M : spFiniteConstructibleTorCategory X.left (SpTowerShriek.R l E m),
        Function.Bijective (fun z : M.obj ⟶
            (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) X.left).obj
              ((spDerivedCoefficientEvaluation l E X.left (q.abelian X.left) n).obj H.obj) ↦
          (reductionCompactSupport (SpTowerShriek.R l E m) c.i c.g).map z ≫
            (@inv _ _ _ _ ((reductionDirectImageComparison
              (SpTowerCalculus.quotient l E h) c.i c.g).app
                ((spDerivedCoefficientEvaluation l E X.left (q.abelian X.left) n).obj
                  H.obj)) hb ≫
            (scalarExtensionFunctor (SpTowerCalculus.quotient l E h) Y.left).map
              (v.comparison.inv.app H.obj ≫
                (spDerivedCoefficientEvaluation l E Y.left (q.abelian Y.left) n).map
                  eps))) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerGluing
