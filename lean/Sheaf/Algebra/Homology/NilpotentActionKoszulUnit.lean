/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Homology.NilpotentKoszulCoordinates
import Sheaf.CategoryTheory.RoosExactAugmentation
import all Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-! # The specified principal Koszul unit under nilpotent action

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 3.4.12;
Stacks Project, Tags 0941 and 012Z; the completeness sentence in
`sec-smooth-purity/sk-lem-sp-tower/sk-lem-sp-tower.proof.md`
(blueprint: lem-sp-nilpotent-action-koszul-unit).
-/

@[expose] public section

set_option autoImplicit false

universe uC vC r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable [EssentiallySmall.{r} C]
variable [HasSheafify J AddCommGrpCat.{r}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
variable (R : Sheaf J CommRingCat.{r})

private local instance (priority := 1000001) cachedSheafCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := inferInstance


attribute [local irreducible] spKoszulRightTensor spKoszulRightCoordinatesInv

omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private lemma spKoszulScalar_pow_apply
    (t : (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R)).sections)
    (M : ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
    (a : ℕ) (U : Cᵒᵖ) (x : M.val.obj U) :
    (((End.of (spKoszulScalar R t M)) ^ a).val.app U).hom x =
      (@id (R.obj.obj U) (t.val U)) ^ a • x := by
  induction a generalizing x with
  | zero => change x = _; simp
  | succ a ih =>
    change (((End.of (spKoszulScalar R t M)) ^ a).val.app U).hom
      ((spKoszulScalar R t M).val.app U x) = _
    rw [ih]
    change (@id (R.obj.obj U) (t.val U)) ^ a •
      ((@id (R.obj.obj U) (t.val U)) • x) = _
    rw [smul_smul, pow_succ]

private lemma productShift_pow_coordinates
    {A : Type*} [Category* A] [Preadditive A] [HasCountableProducts A]
    (T : ℕᵒᵖ ⥤ A) (M : A) (e : ∀ n : ℕ, T.obj (op n) ≅ M)
    (f : End M)
    (he : ∀ n : ℕ, T.map (homOfLE n.le_succ).op ≫ (e n).hom =
      (e (n + 1)).hom ≫ f) (a n : ℕ) :
    ((End.of (towerProductShift (K := fun j : ℕ ↦ T.obj (op j))
      (fun j : ℕ ↦ T.map (homOfLE j.le_succ).op))) ^ a) ≫
        Pi.π (fun j : ℕ ↦ T.obj (op j)) n ≫ (e n).hom =
      Pi.π (fun j : ℕ ↦ T.obj (op j)) (n + a) ≫ (e (n + a)).hom ≫ f ^ a := by
  induction a generalizing n with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, End.mul_def, Category.assoc, ih]
    rw [← Category.assoc, ← Category.assoc]
    rw [show towerProductShift (K := fun j : ℕ ↦ T.obj (op j))
        (fun j : ℕ ↦ T.map (homOfLE j.le_succ).op) ≫
        Pi.π (fun j : ℕ ↦ T.obj (op j)) (n + a) =
        Pi.π (fun j : ℕ ↦ T.obj (op j)) (n + a + 1) ≫
          T.map (homOfLE (n + a).le_succ).op from Pi.lift_π _ _]
    simp only [Category.assoc, he]
    simp only [← End.mul_def, ← pow_succ]
    congr 2

private lemma constantTowerAugment_naturality
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {P P' : CochainComplex A ℤ} {V V' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (b : P ⟶ P') (c : V ⟶ V')
    (i : ((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ⟶ V)
    (i' : ((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P' ⟶ V')
    (h : ((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map b ≫ i' = i ≫ c) :
    b ≫ constantTowerRoosAugmentation i' =
      constantTowerRoosAugmentation i ≫ roosF.map c := by
  ext k : 1
  obtain ⟨l, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  apply (cancel_mono (roosχ V' l).hom).1
  change (b ≫ constantTowerRoosAugmentation i').f (l + 1) ≫ _ =
    (constantTowerRoosAugmentation i ≫ roosF.map c).f (l + 1) ≫ _
  simp only [HomologicalComplex.comp_f, Category.assoc,
    constantTowerRoosAugmentation, roosAugment_χ, roosF_map_χ]
  rw [← Category.assoc, roosAugment_χ]
  apply biprod.hom_ext
  · simp
  · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
      biprod.lift_snd_assoc]
    change (b ≫ Pi.lift (constantTowerComponents i')).f (l + 1) =
      (Pi.lift (constantTowerComponents i) ≫ roosPmap c).f (l + 1)
    congr 1
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.lift_π, roosPmap, Pi.map_π,
      Pi.lift_π_assoc]
    ext k : 1
    exact congrArg (fun f ↦ (f.f k).app (op n)) h

attribute [local irreducible] spKoszulScalar

set_option maxHeartbeats 400000 in
-- The unchanged large existential signature repeats independent-universe sheaf instances.
/-- The specified natural principal Koszul completion unit and its nilpotent-action theorem.

Source: Bhatt--Scholze Lemma 3.4.12; Stacks Tags 012Z and 0941, and the
completeness sentence of the current smooth-purity tower proof
(blueprint: lem-sp-nilpotent-action-koszul-unit).

Proof plan (the seven steps of the DAG):
1. Right total tensor has only degrees `(k,0)` and `(k+1,-1)`. Its differential
   is `(dx+(-1)^(k+1)t^(m+1)y,dy)`. Inclusion is `(x,0)` and quotient is
   `(-1)^k y` in Q[1]; these give a degreewise split short exact sequence.
2. The transition is `(x,ty)`, preserving the inclusions and inducing t on Q[1].
   Thus the sequence is strictly exact in the tower category. Its sections need
   not commute with transitions.
3. Apply the explicit Roos functor. Products of the displayed splittings give a
   degreewise split sequence of Roos complexes, with diagonal maps on both coordinates.
4. If t^a kills every term, the product shift s on Z has s^a=0. The finite sum
   A=1+s+...+s^(a-1) inverts 1-s. In reordered Roos coordinates the homotopy
   h(v,z)=(-Az,0) satisfies dh+hd=1. The strict Roos comparison identifies this
   acyclic complex with total derived inverse limit, hence Rlim Z=0.
5. For the constant tower the finite coordinate sums B(z)_0=0 and
   B(z)_j=-sum_(i<j) z_i satisfy (1-s)B=1 and B(1-s)=1-diagonal*pr_0.
   Consequently the diagonal zero-homotopy augmentation is a quasi-isomorphism.
6. The degreewise split derived triangle has zero third object by step 4. The
   zero-third-map splitting lemma makes the first arrow invertible. Composing
   it with step 5 gives exactly the displayed map u, hence a quasi-isomorphism.
7. A chain map acts as `(b^k,b^(k+1))` and commutes with both inclusions and
   transitions. Products and Roos maps yield strict naturality of u on all
   complexes, without an exponent in its construction. Apply this to the
   transitions of any outer tower; use step 6 separately at each level, with
   its own exponent and with no cohomological bound.

The index m represents the positive integer j=m+1. The Roos dependency orders
coordinates as `(shifted,product)`, so the unit equation below is `(0,(i_j x)_j)`.
The inverse coordinate map is pinned to the actual canonical total-tensor inclusions.
-/
theorem nilpotentActionKoszulUnit
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))]
    (t : (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R)).sections) :
    ∃ (Z : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤
      (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ℤ)
      (ζ : ∀ (Q : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (m : ℕ),
        (Z.obj Q).asFunctor.obj (op m) ≅ Q⟦(1 : ℤ)⟧)
      (i : (Functor.const ℕᵒᵖ : (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤ (ℕᵒᵖ ⥤ (ringedSiteModules.{r}
      ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⟶ spKoszulRightTower R t)
      (p : spKoszulRightTower R t ⟶ Z)
      (hi : i ≫ p = 0)
      (χ : ∀ (Q : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (m : ℕ) (k : ℤ),
        (((spKoszulRightTower R t).obj Q).X k).obj (op m) ≅ Q.X k ⊞ Q.X (k + 1))
      (u : 𝟭 (CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) ⟶ spKoszulRightTower R t ⋙ roosF),
      (∀ (Q : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (m : ℕ) (k : ℤ),
        (χ Q m k).inv = spKoszulRightCoordinatesInv R t Q m k) ∧
      (∀ (Q : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ),
        (ShortComplex.mk (i.app Q) (p.app Q) (NatTrans.congr_app hi Q)).ShortExact) ∧
      (∀ (Q : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (m : ℕ) (k : ℤ),
        ((i.app Q).f k).app (op m) ≫ (χ Q m k).hom = biprod.inl) ∧
      (∀ (Q : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (m : ℕ) (k : ℤ),
        ((p.app Q).f k).app (op m) ≫ (ζ Q m).hom.f k ≫
          (Q.shiftFunctorObjXIso (1 : ℤ) k (k + 1) rfl).hom =
        (χ Q m k).hom ≫ (k.negOnePow • biprod.snd)) ∧
      (∀ (Q : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (m : ℕ) (k : ℤ),
        (((spKoszulRightTower R t).obj Q).d k (k + 1)).app (op m) ≫
            (χ Q m (k + 1)).hom =
          (χ Q m k).hom ≫ biprod.desc
            (Q.d k (k + 1) ≫ biprod.inl)
            (((k + 1).negOnePow •
                endoPow (spKoszulScalar R t (Q.X (k + 1))) (m + 1)) ≫ biprod.inl +
              Q.d (k + 1) ((k + 1) + 1) ≫ biprod.inr)) ∧
      (∀ (Q : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (m : ℕ) (k : ℤ),
        (((spKoszulRightTower R t).obj Q).X k).map
            (homOfLE (Nat.le_succ m)).op ≫ (χ Q m k).hom =
          (χ Q (m + 1) k).hom ≫
            biprod.map (𝟙 _) (spKoszulScalar R t (Q.X (k + 1)))) ∧
      (∀ (Q : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (m : ℕ) (k : ℤ),
        ((Z.obj Q).X k).map (homOfLE (Nat.le_succ m)).op ≫
            (ζ Q m).hom.f k ≫ (Q.shiftFunctorObjXIso (1 : ℤ) k (k + 1) rfl).hom =
          (ζ Q (m + 1)).hom.f k ≫
            (Q.shiftFunctorObjXIso (1 : ℤ) k (k + 1) rfl).hom ≫
              spKoszulScalar R t (Q.X (k + 1))) ∧
      (∀ (Q : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (k : ℤ),
        (u.app Q).f (k + 1) ≫ (roosχ ((spKoszulRightTower R t).obj Q) k).hom =
          biprod.lift 0 ((@id (Q ⟶ roosP ((spKoszulRightTower R t).obj Q))
            (Pi.lift (fun m : ℕ ↦
              (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
                (i.app Q)).app (op m)))).f (k + 1))) ∧
      (∀ (Q : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (a : ℕ), 1 ≤ a →
        (∀ (k : ℤ) (U : Cᵒᵖ) (x : (Q.X k).val.obj U),
          (@id (R.obj.obj U) (t.val U)) ^ a • x = 0) →
        QuasiIso (u.app Q) ∧
          ∀ (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ⥤ DerivedCategory.{w}
      (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
            (η : (lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ⥤ (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).mapHomologicalComplex
              (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF),
            RF.IsRightDerivedFunctor η
              (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) (ComplexShape.up ℤ)) →
            IsZero (RF.obj (DerivedCategory.Q.{w}.obj (Z.obj Q)))) ∧
      (∀ (T : ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (a : ℕ → ℕ),
        (∀ n : ℕ, 1 ≤ a n) →
        (∀ (n : ℕ) (k : ℤ) (U : Cᵒᵖ) (x : ((T.obj (op n)).X k).val.obj U),
          (@id (R.obj.obj U) (t.val U)) ^ (a n) • x = 0) →
        ∀ n : ℕ, QuasiIso ((Functor.whiskerLeft T u).app (op n))) := by
  classical
  let A := ringedSiteModules.{r} ((sheafCompose J
    (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  let : IsGrothendieckAbelian.{r} A := moduleSheaves_grothendieck J
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  have h := nilpotentKoszulCoordinates R t
  rcases h with ⟨Z, hZ⟩
  obtain ⟨ζ, hZ⟩ := hZ
  obtain ⟨i, hZ⟩ := hZ
  obtain ⟨p, hZ⟩ := hZ
  obtain ⟨hi, hZ⟩ := hZ
  obtain ⟨χ, hχ, hS, hiχ, hpχ, hdχ, htχ, hZχ⟩ := hZ
  let u : 𝟭 (CochainComplex A ℤ) ⟶ spKoszulRightTower R t ⋙ roosF :=
    { app := fun Q ↦ constantTowerRoosAugmentation (i.app Q)
      naturality := fun _ _ b ↦ constantTowerAugment_naturality b
        ((spKoszulRightTower R t).map b) (i.app _) (i.app _) (i.naturality b) }
  have hunit (Q : CochainComplex A ℤ) (a : ℕ) (ha : 1 ≤ a)
      (hQ : ∀ (k : ℤ) (U : Cᵒᵖ) (x : (Q.X k).val.obj U),
        (@id (R.obj.obj U) (t.val U)) ^ a • x = 0) :
      QuasiIso (u.app Q) ∧
        ∀ (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
          (η : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF),
          RF.IsRightDerivedFunctor η
            (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)) →
          IsZero (RF.obj (DerivedCategory.Q.{w}.obj (Z.obj Q))) := by
    apply roosNilpotentExactAugmentation Q _ _ (i.app Q) (p.app Q)
      (NatTrans.congr_app hi Q) (hS Q) a ha
    intro k
    let e (n : ℕ) : ((Z.obj Q).X k).obj (op n) ≅ Q.X (k + 1) :=
      (HomologicalComplex.eval A (ComplexShape.up ℤ) k).mapIso (ζ Q n) ≪≫
        Q.shiftFunctorObjXIso (1 : ℤ) k (k + 1) rfl
    let f : End (Q.X (k + 1)) := spKoszulScalar R t (Q.X (k + 1))
    have hf : f ^ a = 0 := by
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (spKoszulScalar_pow_apply R t (Q.X (k + 1)) a U x).trans (hQ _ _ x)
    apply Pi.hom_ext
    intro n
    apply (cancel_mono (e n).hom).1
    rw [Category.assoc, productShift_pow_coordinates ((Z.obj Q).X k)
      (Q.X (k + 1)) e f (fun j ↦ hZχ Q j k), hf]
    simp
  refine ⟨Z, ζ, i, p, hi, χ, u, hχ, hS, hiχ, hpχ, hdχ, htχ, hZχ, ?_, hunit, ?_⟩
  · intro Q k
    exact roosAugment_χ (constantTowerComponents (i.app Q))
      (constantTowerCompatible (i.app Q)) k
  · intro T a ha hT n
    exact (hunit (T.obj (op n)) (a n) (ha n) (hT n)).1

end CategoryTheory
