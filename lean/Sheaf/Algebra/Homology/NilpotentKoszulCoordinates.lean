/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Mathlib.Algebra.Homology.BifunctorShift

/-! # Signed coordinates of the right principal Koszul tensor tower

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 3.4.12;
Stacks Project, Tags 0941 and 012Z; the completeness sentence in
`sec-smooth-purity/sk-lem-sp-tower/sk-lem-sp-tower.proof.md`
(blueprint: lem-sp-nilpotent-koszul-coordinates).
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

/-- The existing total tensor bifunctor with its canonical sheaf tensor structure.
Source: Stacks Tag 012Z (blueprint: lem-sp-nilpotent-action-koszul-unit).
This only installs the recorded tensor instances inside a real construction. -/
noncomputable def spKoszulRightTensor :
    CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤ CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤ CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  exact (MonoidalCategory.curriedTensor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))).map₂CochainComplex

/-- Rearrangement of the recorded tower-complex construction, functorially.
Source: Stacks Tag 0941 (blueprint: lem-sp-nilpotent-action-koszul-unit). -/
def spKoszulRearrange :
    (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) ⥤ CochainComplex (ℕᵒᵖ ⥤
      (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ℤ where
  obj := koszulTowerComplex R
  map := koszulTowerComplexMap R
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The actual right total tensor tower `Q ⊗ L_(m+1)`, functorial in every complex Q.
Source: Bhatt--Scholze Lemma 3.4.12 and Stacks 012Z
(blueprint: lem-sp-nilpotent-action-koszul-unit). -/
noncomputable def spKoszulRightTower
    (t : (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R)).sections) :
    CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤
      (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ℤ :=
  spKoszulRightTensor R ⋙
    (Functor.whiskeringLeft ℕᵒᵖ (CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
      (CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)).obj (principalKoszulTower R t) ⋙
      spKoszulRearrange R

/-- The two canonical tensor summands, ordered as `(Q^k,Q^(k+1))`.
Source: Stacks 012Z (blueprint: lem-sp-nilpotent-action-koszul-unit).
The first factor uses the degree-zero target of the cone; the second its shifted source. -/
noncomputable def spKoszulRightCoordinatesInv
    (t : (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R)).sections)
    (Q : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) (m : ℕ) (k : ℤ) :
    Q.X k ⊞ Q.X (k + 1) ⟶
      (((spKoszulRightTensor R).obj Q).obj (principalKoszul R t m)).X k := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  exact biprod.desc
    ((MonoidalCategory.rightUnitor (Q.X k)).inv ≫
      MonoidalCategory.whiskerLeft (Q.X k)
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R))).inv ≫
          (CochainComplex.mappingCone.inr
            ((CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) 0).map
              (endoPow (globalSectionMultiplication R t) (m + 1)))).f 0) ≫
      CochainComplex.ιMapBifunctor Q (principalKoszul R t m)
        (MonoidalCategory.curriedTensor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) k 0 k (add_zero k))
    ((MonoidalCategory.rightUnitor (Q.X (k + 1))).inv ≫
      MonoidalCategory.whiskerLeft (Q.X (k + 1))
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R))).inv ≫
          (CochainComplex.mappingCone.inl
            ((CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) 0).map
              (endoPow (globalSectionMultiplication R t) (m + 1)))).v 0 (-1) rfl) ≫
      CochainComplex.ιMapBifunctor Q (principalKoszul R t m)
        (MonoidalCategory.curriedTensor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) (k + 1) (-1) k (add_neg_cancel_right k 1))

/-- Multiplication by the specified global section, using the existing presheaf action.
Source: Bhatt--Scholze Lemma 3.4.12
(blueprint: lem-sp-nilpotent-action-koszul-unit). -/
noncomputable def spKoszulScalar
    (t : (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
      R)).sections) (M : (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) : M ⟶ M :=
  ⟨PresheafOfModules.sectionsSMul (S := R.obj) M.val ⟨t.val, t.property⟩⟩

/-- The canonical right tensor summands give a natural strict short exact sequence.
Source: Bhatt--Scholze, Lemma 3.4.12, principal cone calculation, and Stacks Tag 012Z
(blueprint: lem-sp-nilpotent-koszul-coordinates).

Proof: In total degree k only the pairs (k,0) and (k+1,-1) survive, because the
principal cone is zero in all other degrees. Tensoring the two cone inclusions with
Q and using the right unitor gives precisely spKoszulRightCoordinatesInv. The
universal property of the total direct sum gives its inverse. On these summands the
differential is (dx + (-1)^(k+1) t^(m+1)y, dy); the cone transition is (x,ty).
Define Z as the tower with all levels Q[1] and scalar transition t. Define i in
coordinates by x -> (x,0), and p by (x,y) -> (-1)^k y. The displayed differential
identities prove these are chain maps, and the transition identities make them
strict tower maps. Their composite is zero, and each degree is the split sequence
of the two summands, with section z -> (0,(-1)^k z). Exactness in functor and complex
categories is degreewise. A map b of complexes acts by (b^k,b^(k+1)), so the
inclusions and projections are natural in Q. These calculations give every stated
equation, including the pinning of the inverse coordinates to the actual tensor
summand inclusions. No nilpotence or boundedness is used. -/
theorem nilpotentKoszulCoordinates
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
        (((spKoszulRightTower R t).obj Q).X k).obj (op m) ≅ Q.X k ⊞ Q.X (k + 1)),
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
              spKoszulScalar R t (Q.X (k + 1))) := by sorry

end CategoryTheory
