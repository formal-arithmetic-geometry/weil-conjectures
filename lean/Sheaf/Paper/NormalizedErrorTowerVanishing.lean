/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.Paper.NormalizedErrorTowerData
import Sheaf.Paper.NormalizedStrictTensorFiber
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.IsConnected
import Mathlib.Algebra.Homology.Functor

/-! # The vanishing error tower of normalized coefficient complexes

Source: blueprint main-20261015, sk-lem-sp-tower, proof paragraph;
Bhatt--Scholze, Section 3.5, Lemmas 3.5.4--3.5.7
(blueprint: lem-sp-normalized-error-tower-vanishing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe t u c v r w u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open MonoidalCategory CochainComplex SheafOfModules.TotalTensorSigns
open WeilConjectures SheafOfModules

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  AlgebraicGeometry.ProEtale.spLevelReduction
  AlgebraicGeometry.ProEtale.spCompletedEllProjection

private theorem poweredSequenceMap
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    (H : C ⥤ D) (X : ℕ → C) (f : ∀ j, X (j + 1) ⟶ X j) (b : ℕ)
    (j j' : ℕ) (h : j ≤ j') :
    (Functor.ofOpSequence (X := fun n ↦ H.obj (X n)) (fun n ↦ b • H.map (f n))).map (homOfLE h).op =
      b ^ (j' - j) • H.map ((Functor.ofOpSequence f).map (homOfLE h).op) := by
  induction j', h using Nat.le_induction with
  | base => simp; rfl
  | succ k hk ih =>
    have he : homOfLE (show j ≤ k + 1 by omega) =
        homOfLE hk ≫ homOfLE (Nat.le_succ k) := rfl
    rw [he, op_comp, Functor.map_comp, Functor.map_comp, H.map_comp]
    rw [Functor.ofOpSequence_map_homOfLE_succ,
      Functor.ofOpSequence_map_homOfLE_succ, ih]
    rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, smul_smul]
    rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]
    rw [Nat.mul_comm]

namespace ErrorProof
variable {A : Type u} [Category.{v} A] [Abelian A]
private def evalConstAdj : (evaluation ℕᵒᵖ A).obj (op 0) ⊣ Functor.const ℕᵒᵖ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦
        { toFun := fun f ↦
            { app := fun n ↦ X.map (homOfLE (Nat.zero_le n.unop)).op ≫ f
              naturality := by
                intro i j g
                dsimp
                rw [Category.comp_id, ← Category.assoc, ← X.map_comp]
                rfl }
          invFun := fun f ↦ f.app (op 0)
          left_inv := by intro f; simp
          right_inv := by
            intro f
            ext n
            simp }
      homEquiv_naturality_left_symm := by intros; rfl
      homEquiv_naturality_right := by intros; ext; simp }
private theorem constKInjective (I : CochainComplex A ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (.up ℤ)).obj I) := by
  let := (evalConstAdj (A := A)).preservesKInjectiveComplexes
  infer_instance
variable [HasLimitsOfShape ℕᵒᵖ A]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
private def diagonal
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (κ : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (P : CochainComplex A ℤ) :=
  DerivedCategory.Q.{w}.map
    (((constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim).mapHomologicalComplex
      (.up ℤ)).unit.app P) ≫
    κ.app (((Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (.up ℤ)).obj P)
private theorem diagonal_iso
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (κ : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hκ : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective → IsIso (κ.app I))
    (hres : ∀ P : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (i : P ⟶ I),
      I.IsKInjective ∧ QuasiIso i)
    (P : CochainComplex A ℤ) : IsIso (diagonal RF κ P) := by
  obtain ⟨I, i, hI, hi⟩ := hres P
  let := hI
  let := hi
  let C := (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A).mapHomologicalComplex (.up ℤ)
  let adj := (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ ℕᵒᵖ ⥤ A) ⊣ lim).mapHomologicalComplex (.up ℤ)
  have hunit : IsIso adj.unit := inferInstance
  have hκI : IsIso (κ.app (C.obj I)) := hκ _ (constKInjective I)
  have hdI : IsIso (diagonal RF κ I) := by
    unfold diagonal
    infer_instance
  have hCi : QuasiIso (C.map i) := inferInstance
  have hnat : DerivedCategory.Q.map i ≫ diagonal RF κ I =
      diagonal RF κ P ≫ RF.map (DerivedCategory.Q.map (C.map i)) := by
    dsimp only [diagonal]
    have hu : i ≫ adj.unit.app I = adj.unit.app P ≫
        ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).map (C.map i) :=
      adj.unit.naturality i
    rw [← Category.assoc, ← DerivedCategory.Q.map_comp, hu]
    rw [DerivedCategory.Q.map_comp, Category.assoc]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun f ↦ DerivedCategory.Q.map (adj.unit.app P) ≫ f)
        (κ.naturality (C.map i))
  have hc : IsIso (diagonal RF κ P ≫ RF.map (DerivedCategory.Q.map (C.map i))) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (RF.map (DerivedCategory.Q.map (C.map i)))
end ErrorProof

namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})
variable [HasDerivedCategory.{w} (spErrorModules l E T)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ spErrorModules l E T)]

private theorem limitProperties
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ spErrorModules l E T) ⥤
      DerivedCategory.{w} (spErrorModules l E T))
    (κ : spErrorLimitComparison l E T RF)
    (hRF : RF.IsRightDerivedFunctor κ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ spErrorModules l E T) (.up ℤ))) :
    (∀ I : CochainComplex (ℕᵒᵖ ⥤ spErrorModules l E T) ℤ,
      I.IsKInjective → IsIso (κ.app I)) ∧
    (∃ (_ : RF.CommShift ℤ), RF.IsTriangulated) ∧
    (∀ X : ℕᵒᵖ ⥤ CochainComplex (spErrorModules l E T) ℤ,
      (∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
        DerivedCategory.Q.{w}.map (X.map (homOfLE h).op) = 0) →
      IsZero (RF.obj (DerivedCategory.Q.{w}.obj (spErrorTowerComplex l E T X)))) := by
  let : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf _
  let : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
    WeilConjectures.integralCoefficientAbSheafify.{t, u} T
  let : (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, u} T
  have hc : ∀ (U : T.ProEtᵒᵖ)
      (a b : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U),
      a * b = b * a := by
    intro U a b
    exact @mul_comm ((completedIntegralCommRingSheafUnrestricted l E T).obj.obj U)
      inferInstance a b
  obtain ⟨RF₀, κ₀, hRF₀, hκ₀, hres, hs, hp, Ev, ε, p, δ,
    htri, hroos, hpn, hδn, hz, hcone⟩ :=
    ringedStrictTowerHomotopyLimitIndependentCoefficients.{w, t + 1, t, max u (t + 1)}
      (C := T.ProEt) (Scheme.ProEt.topology T)
      (completedIntegralCoefficientSheafUnrestricted l E T) hc
  let := hRF₀
  let := hRF
  let e := Functor.rightDerivedUnique RF₀ RF κ₀ κ
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ spErrorModules l E T) (.up ℤ))
  have he (I : CochainComplex (ℕᵒᵖ ⥤ spErrorModules l E T) ℤ) :
      κ₀.app I ≫ e.hom.app (DerivedCategory.Q.obj I) = κ.app I := by
    simp [e, Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom]
  refine ⟨?_, ?_, ?_⟩
  · intro I hI
    have := hκ₀ I hI
    rw [← he I]
    infer_instance
  · let := hs
    let := htri
    let := Functor.CommShift.ofIso e ℤ
    let := Functor.CommShift.ofIso_compatibility e ℤ
    exact ⟨inferInstance, Functor.isTriangulated_of_iso e⟩
  · intro X hX
    apply (hz (DerivedCategory.Q.obj (spErrorTowerComplex l E T X)) ?_).of_iso
      (e.app _).symm
    intro n
    obtain ⟨m, h, hm⟩ := hX n
    refine ⟨m, h, ?_⟩
    let v := (ε.app (spErrorTowerComplex l E T X)).hom
    apply (cancel_mono (v.app (op n))).1
    rw [zero_comp]
    have hv := v.naturality (homOfLE h).op
    change (Ev.obj (DerivedCategory.Q.obj (spErrorTowerComplex l E T X))).map
        (homOfLE h).op ≫ v.app (op n) =
      v.app (op m) ≫ DerivedCategory.Q.map (X.map (homOfLE h).op) at hv
    rw [hv]
    change v.app (op m) ≫ DerivedCategory.Q.map (X.map (homOfLE h).op) = 0
    rw [hm, comp_zero]

/-- Normalized K-flat coefficient complexes have a vanishing error tower and the canonical
finite reduction isomorphism. No boundedness, constructibility or common cohomological
interval is imposed. Natural index m denotes the positive exponent m+1.

Source: blueprint main-20261015, sk-lem-sp-tower, proof paragraph; Bhatt--Scholze,
Section 3.5, Lemmas 3.5.4--3.5.7
(blueprint: lem-sp-normalized-error-tower-vanishing).

Proof plan (the node's seven steps):
1. Form the strict tensor towers using q and the coefficient reductions. Balancedness,
   identities and cocycles follow on tensor generators. The mutually inverse maps
   x tensor (b tensor k) ↦ bx tensor k and x tensor k ↦ x tensor (1 tensor k)
   identify the middle term, with no additional sign because b has degree zero.
2. Apply totalTensorHomotopyConeSigns to the rotated coefficient cone triangles.
   Its identity and (-1)^p summand maps commute with semilinear degree-zero transitions.
   This gives the displayed strict cone triangle; levelwise abelianity makes its
   derived image distinguished.
3. Tensor the normalized coefficient-fiber quasi-isomorphism with each K-flat Q_n.
   The shift comparison has sign (-1)^p. The coefficient transition equation becomes
   ell^(n'-n) times the usual shifted S transition. These are strict chain equations,
   so the comparisons assemble to the strict levelwise quasi-isomorphism η.
4. The maps x tensor b ↦ b q_(n,m)(x) commute with transitions by the cocycle law.
   Normalization makes every component a quasi-isomorphism. Exact evaluation detects
   their quasi-isomorphism as a map of complexes of towers.
5. Each S_n is killed by ell^(m+1). Thus the powered tower has zero transition across
   a gap m+1, and η makes the left tower pro-zero in D(R). Apply the pro-zero clause of
   ringedStrictTowerHomotopyLimitIndependentCoefficients to obtain limit_zero.
6. Resolve Q_m by a K-injective complex I. Evaluation at the initial tail index is
   exact and left adjoint to the constant-tower functor, so ΔI is K-injective.
   Its ordinary limit is I, with identity projections. The total-derived comparison
   therefore identifies the constant-tower diagonal with the resolution map and
   makes precisely that diagonal invertible.
7. The total right-derived limit is exact. It sends the strict triangle to a triangle
   with zero left object, hence its actual augmentation arrow is invertible by
   representable Hom exactness and rotation. Compose with the invertible reduction
   and the inverse of the identity-cone diagonal. This is the asserted original-map
   composite, without any termwise-product or boundedness assumption. -/
theorem sp_normalized_error_tower_vanishing
    (Q : ∀ n : ℕ,
      CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (q : SpErrorTransitions l E T Q)
    (hq_id : ∀ (n : ℕ) (p : ℤ) (U : T.ProEtᵒᵖ) (x : ((Q n).X p).val.obj U),
      spErrorTransitionValue l E T Q q n n le_rfl p U x = x)
    (hq_comp : ∀ (n k m : ℕ) (hkn : k ≤ n) (hmk : m ≤ k)
      (p : ℤ) (U : T.ProEtᵒᵖ) (x : ((Q n).X p).val.obj U),
      spErrorTransitionValue l E T Q q k m hmk p U
        (spErrorTransitionValue l E T Q q n k hkn p U x) =
      spErrorTransitionValue l E T Q q n m (hmk.trans hkn) p U x)
    (hflat : ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
      (R := (spCoefficientCommRings l E T).obj (op n)) (Q n))
    (hnorm : ∀ (n m : ℕ) (h : m ≤ n),
      ∃ ρ : spErrorReduction l E T Q n m h ⟶ (spErrorRestrict l E T m).obj (Q m),
        SpErrorReductionFormula l E T Q q n m h ρ ∧ QuasiIso ρ)
    (m : ℕ)
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ spErrorModules l E T) ⥤
      DerivedCategory.{w} (spErrorModules l E T))
    (κ : spErrorLimitComparison l E T RF)
    (hRF : RF.IsRightDerivedFunctor κ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ spErrorModules l E T) (.up ℤ))) :
    SpNormalizedErrorDiagram l E T Q q m RF κ := by
  classical
  let : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf _
  let : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbSheafify.{t, u} T
  let : (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    integralCoefficientAbLocallyBijective.{t, u} T
  obtain ⟨hκ, ⟨hs, htri⟩, hz⟩ := limitProperties l E T RF κ hRF
  let := hs
  let := htri
  obtain ⟨A, s, t, a, left, ρ, assoc, fiber, η,
    hs_formula, ht_formula, ha_left, ha_right, hassoc, hfiber,
    hdist, hη, hηlevel, hρformula, hρ, hzero⟩ :=
    sp_normalized_strict_tensor_fiber l E T Q q hq_id hq_comp hflat hnorm m
  have hpowered : ∀ (j j' : ℕ) (h : j ≤ j'),
      (spErrorPoweredShift l E T Q m s).map (homOfLE h).op =
        spErrorPoweredMap (l ^ (j' - j))
          ((spErrorTailS l E T Q m s).map (homOfLE h).op) := by
    intro j j' h
    exact poweredSequenceMap
      (CategoryTheory.shiftFunctor (CochainComplex (spErrorModules l E T) ℤ) (1 : ℤ))
      (fun k ↦ spErrorReduction l E T Q (m + k) m (by omega)) s l j j' h
  have hZ : IsZero (RF.obj (DerivedCategory.Q.obj (spErrorTowerComplex l E T A))) := by
    apply hz
    intro n
    obtain ⟨k, h, hk⟩ := hzero n
    refine ⟨k, h, ?_⟩
    have hnat := η.naturality (homOfLE h).op
    have hnat' := congrArg (fun f ↦ DerivedCategory.Q.{w}.map f) hnat
    rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp, hk,
      DerivedCategory.Q.map_zero, zero_comp] at hnat'
    have := hηlevel k
    apply (cancel_epi (DerivedCategory.Q.{w}.map (η.app (op k)))).1
    simpa using hnat'.symm
  have hres : ∀ P : CochainComplex (spErrorModules l E T) ℤ,
      ∃ (I : CochainComplex (spErrorModules l E T) ℤ) (i : P ⟶ I),
        I.IsKInjective ∧ QuasiIso i := by
    obtain ⟨_, _, I, ε, hI⟩ :=
      grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t + 1, t, u}
        (Scheme.ProEt.topology T) (completedIntegralCommRingSheafUnrestricted l E T)
    intro P
    exact ⟨I.obj P, ε.app P, (hI P).2.1, (hI P).1⟩
  have hd : IsIso (spErrorDiagonal l E T RF κ ((spErrorRestrict l E T m).obj (Q m))) :=
    ErrorProof.diagonal_iso RF κ hκ hres _
  let := hd
  let diagonal := asIso
    (spErrorDiagonal l E T RF κ ((spErrorRestrict l E T m).obj (Q m)))
  refine ⟨A, s, t, a, left, ρ, assoc, fiber, η, diagonal,
    hs_formula, ht_formula, ha_left, ha_right, hassoc, hfiber, hdist,
    hη, hηlevel, hpowered, hρformula, hρ, hZ, rfl, ?_⟩
  have hρtower : QuasiIso
      (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E T) ρ) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
    intro n
    exact hρ n.unop
  obtain ⟨δ, hδ⟩ := hdist
  have hlim := RF.map_distinguished _ hδ
  have ha : IsIso (RF.map (DerivedCategory.Q.map
      (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E T) a))) :=
    (Triangle.isZero₁_iff_isIso₂ _ hlim).mp hZ
  infer_instance

end AlgebraicGeometry.ProEtale
