/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGammaData
import WeilConjectures.AlgebraicGeometry.CoefficientTowerShriekCalculus
import WeilConjectures.AlgebraicGeometry.CoefficientTowerTransitionCompatibility
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin

/-! # Normalization of the compact-support and exceptional outputs

Source: latest blueprint tower-geometric gamma proof (3).
(blueprint: lem-sp-tower-normalization-preservation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerGamma
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)


set_option linter.unusedVariables false in
/-- Both actual adjoints preserve normalized objects in the uniform tower category.
The claim concerns only the quotient transitions; it asserts no tower orientation,
no isomorphism of whole towers, and no naturality of gamma.
Source: latest blueprint tower-geometric gamma proof (3)
(blueprint: lem-sp-tower-normalization-preservation).

Proof: build the finite evaluation of the actual compact-support functor at every
compactification from the realization counit, Fcomparison and the two level
comparisons, and its finite-origin datum from the finite-ring constructible origin
criterion (lem-weil-pbc-finite-ring-constructible-derived-origin).
For normalized M and m <= n, ReductionDirectImage makes the compact-support coefficient
comparison invertible on the bounded constructible finite-Tor level M_n (each
O_E/l^(n+1) is killed by l^(n+1)), and compact support of the invertible input
reduction is invertible. The transition compatibility identifies this composite, after
the scalar image of an evaluation isomorphism, with the output reduction followed by
the output evaluation isomorphism; cancel the evaluation isomorphism. For normalized
K, lift its reduction to the finite constructible finite-Tor subcategory; the supplied
Levels gives invertibility of the coefficient mate and the reduction equation for G,
whose left side is then invertible; cancel the finite evaluation comparison. In both
halves the reduction in intrinsic scalar coordinates is the original reduction
composed with the scalar-coordinate isomorphism, so the original reduction is
invertible. Equal indices and d = 0 are included; no flatness is used. Membership in
the uniform category is supplied by hF and by the codomain of G. -/
theorem tower_normalization_preservation (D : FiniteFieldDatum.{u}) [CharP D.k D.p] (hne : l ≠ D.p)
    {X Z Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [(j ≫ p).IsOver (Spec (.of D.k))]
    [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
    (d : ℕ) [SmoothOfRelativeDimension d (j ≫ p)]
    (w : SpChartAdmissibility.Twists l E X)
    (hF : ∀ M : SpTowerCalculus.C l E b q X,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((SpTowerCalculus.F l E b o q (factorization j p)).obj M.obj))
    (G : SpTowerCalculus.C l E b q Y ⥤ SpTowerCalculus.C l E b q X)
    (adj : SpTowerGluing.support l E b o q (factorization j p) hF ⊣ G)
    (lv : SpTowerGluing.Levels l E b o q (factorization j p) hF G adj)
    (roots : SpCoordinateAdjunction.RootLines l E X)
    (unitsX : ∀ n : ℕ, IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤)))
    (cc : ∀ n : ℕ,
      letI : Finite (SpTowerShriek.R l E n) := b.finite n
      SpTowerP1.CoefficientCoordinates l E n X (unitsX n))
    (tc : ∀ n : ℕ,
      letI : Finite (SpTowerShriek.R l E n) := b.finite n
      SpTowerP1.TensorCoordinates l E n b X)
    (gc : ∀ n : ℕ,
      letI : Finite (SpTowerShriek.R l E n) := b.finite n
      SpTowerP1.GeometricCoordinates l E n (j ≫ p)) :
    (∀ M : SpTowerCalculus.C l E b q X,
      IsSpNormalizedTower l E X (q.abelian X) M.obj →
        IsSpNormalizedTower l E Y (q.abelian Y)
          ((SpTowerGluing.support l E b o q (factorization j p) hF).obj M).obj) ∧
    (∀ K : SpTowerCalculus.C l E b q Y,
      IsSpNormalizedTower l E Y (q.abelian Y) K.obj →
        IsSpNormalizedTower l E X (q.abelian X) (G.obj K).obj) := by
  classical
  let := b
  have eval {S T : Scheme.{u}} {f : S ⟶ T} (c : Compactification f) (n : ℕ) :
      SpTowerCalculus.Evaluation l E b o q c n := by
    letI := (q.abelian S).hasDerived
    letI := (q.abelian T).hasDerived
    refine ⟨(Functor.isoWhiskerLeft _ (SpTowerCalculus.levelComparison l E b q T n).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft
          ((SpTowerCalculus.realization l E b S (q.abelian S)).functor ⋙
            SpTowerShriek.F l E b o c)
          (SpTowerCalculus.realization l E b T (q.abelian T)).counitIso ≪≫
            Functor.rightUnitor _) (SpTowerShriek.Ev l E T n) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (SpTowerShriek.Fcomparison l E b o c n) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (SpTowerCalculus.levelComparison l E b q S n) _, ?_⟩
    intro M
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.rightUnitor_hom_app, Functor.comp_obj, Category.id_comp]
    erw [Category.comp_id]
  obtain ⟨z⟩ := SpTowerCalculus.finite_coordinates_exists l E
  let fd : SpTowerCalculus.FiniteNormalization l E D.k b o q z :=
    { evaluation := eval
      finite_origin := by
        intro T _ _ _ _ K n
        let A := SpTowerShriek.R l E n
        let R := sfIntrinsicDerivedEquivalence T A
        let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
        obtain ⟨J, ⟨eJ⟩⟩ := ((finiteRing_constructibleDerived_origin T A).2.2.1 _).mpr
          ⟨(K.property.1 n).2.1, (K.property.1 n).1⟩
        let ec : R.functor.obj (ν.mapDerivedCategory.obj J.obj) ≅
            (spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj K.obj :=
          ((Functor.mapDerivedCategoryCompIso ν
            (ProEtale.finiteCoefficientIntrinsicRealization T A)).app J.obj).symm ≪≫ eJ
        let e : ν.mapDerivedCategory.obj J.obj ≅ R.inverse.obj
            ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj K.obj) :=
          R.unitIso.app _ ≪≫ R.inverse.mapIso ec
        obtain ⟨a, c, _, hz⟩ := J.property.2
        exact ⟨J.obj, ⟨a, (DerivedCategory.isGE_iff J.obj a).mpr
          (fun i hi ↦ hz i (.inl hi))⟩, ⟨e⟩⟩ }
  have : Smooth (j ≫ p) := SmoothOfRelativeDimension.smooth d (j ≫ p)
  have : LocallyOfFiniteType (j ≫ p) := inferInstance
  have : IsSeparated (j ≫ p) :=
    IsSeparated.of_comp (j ≫ p) (Y ↘ Spec (.of D.k))
  have torsion (n : ℕ) : ∃ a : ℕ, ∀ x : SpTowerShriek.R l E n, (l ^ a) • x = 0 := by
    refine ⟨n + 1, fun x ↦ ?_⟩
    have hz : ((l ^ (n + 1) : ℕ) : SpTowerShriek.R l E n) = 0 := by
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.pow_mem_pow (I := spEllIdeal l E)
          (Ideal.subset_span (Set.mem_singleton (l : Padic.coefficientExtensionIntegers l E)))
          (n + 1))
      simpa only [map_pow, map_natCast, Nat.cast_pow] using hz
    rw [nsmul_eq_mul, hz, zero_mul]
  constructor
  · intro M hM m n h
    have := hM m n h
    have : IsIso (SpTowerCalculus.reduction l E X (q.abelian X) h
        (q.scalar X h) M.obj) := by
      unfold SpTowerCalculus.reduction
      infer_instance
    let : Z.Over (Spec (.of D.k)) := ⟨p ≫ (Y ↘ Spec (.of D.k))⟩
    have : p.IsOver (Spec (.of D.k)) := ⟨rfl⟩
    have : j.IsOver (Spec (.of D.k)) := ⟨by
      change j ≫ (p ≫ (Y ↘ Spec (.of D.k))) = X ↘ Spec (.of D.k)
      rw [← Category.assoc, comp_over]⟩
    have : IsSeparated (Z ↘ Spec (.of D.k)) := inferInstanceAs
      (IsSeparated (p ≫ (Y ↘ Spec (.of D.k))))
    have : LocallyOfFiniteType (Z ↘ Spec (.of D.k)) := inferInstanceAs
      (LocallyOfFiniteType (p ≫ (Y ↘ Spec (.of D.k))))
    have : QuasiCompact (Z ↘ Spec (.of D.k)) := inferInstanceAs
      (QuasiCompact (p ≫ (Y ↘ Spec (.of D.k))))
    have hMn := M.property.1 n
    obtain ⟨a, c, _, hv⟩ := hMn.1
    have hb : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X (SpTowerShriek.R l E n))) i).obj
          ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj M.obj))} := by
      apply (Set.finite_Icc a c).subset
      intro i hi
      exact ⟨le_of_not_gt (fun h ↦ hi (hv i (.inl h))),
        le_of_not_gt (fun h ↦ hi (hv i (.inr h)))⟩
    have := (reductionDirectImage_isIso l D.p D.prime.pos (Ne.symm hne) D.k
      (j ≫ p) j p rfl (torsion n) (torsion m) (SpTowerCalculus.quotient l E h)
      ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj M.obj)
      hb hMn.2.1 hMn.2.2).1
    have eqn := SpTowerCalculus.reduction_transition_compatibility l E D.p D.prime.pos
      (Ne.symm hne) D.k b o q z fd (j ≫ p) (factorization j p) M h
    have : IsIso (SpTowerCalculus.reduction l E Y (q.abelian Y) h (q.scalar Y h)
        ((SpTowerCalculus.F l E b o q (factorization j p)).obj M.obj) ≫
          (fd.evaluation (factorization j p) m).comparison.hom.app M.obj) := by
      rw [← eqn]
      dsimp only [factorization]
      infer_instance
    have hout := IsIso.of_isIso_comp_right
      (SpTowerCalculus.reduction l E Y (q.abelian Y) h (q.scalar Y h)
        ((SpTowerCalculus.F l E b o q (factorization j p)).obj M.obj))
      ((fd.evaluation (factorization j p) m).comparison.hom.app M.obj)
    dsimp only [SpTowerCalculus.reduction] at hout
    exact (isIso_comp_left_iff _ _).mp hout
  · intro K hK m n h
    have := hK m n h
    have : IsIso (SpTowerCalculus.reduction l E Y (q.abelian Y) h
        (q.scalar Y h) K.obj) := by
      unfold SpTowerCalculus.reduction
      infer_instance
    have : IsIso (ObjectProperty.homMk
        (SpTowerCalculus.reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj) :
        (reductionCtfScalar (SpTowerCalculus.quotient l E h) Y
          (lv.scalarY m n h)).obj ((SpTowerGluing.level l E b q Y n).obj K) ⟶
          (SpTowerGluing.level l E b q Y m).obj K) := by
      apply (ObjectProperty.isIso_hom_iff _).mp
      change IsIso (SpTowerCalculus.reduction l E Y (q.abelian Y) h (q.scalar Y h) K.obj)
      infer_instance
    have := lv.coefficient_iso m n h ((SpTowerGluing.level l E b q Y n).obj K)
    have : IsIso (SpTowerCalculus.reduction l E X (q.abelian X) h
        (q.scalar X h) (G.obj K).obj ≫ ((lv.comparison m).hom.app K).hom) := by
      rw [← lv.reduction m n h K]
      infer_instance
    have hout := IsIso.of_isIso_comp_right
      (SpTowerCalculus.reduction l E X (q.abelian X) h (q.scalar X h) (G.obj K).obj)
      (((lv.comparison m).hom.app K).hom)
    dsimp only [SpTowerCalculus.reduction] at hout
    exact (isIso_comp_left_iff _ _).mp hout

end AlgebraicGeometry.ProEtale.SpTowerGamma

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
