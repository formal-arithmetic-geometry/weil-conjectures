/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.ExceptionalFiniteRealization
import Sheaf.CategoryTheory.MateIsoAlongEquivalences
import WeilConjectures.CategoryTheory.InverseMateEquivalence
/-! # Compact-support realization of the actual finite adjunction
Source: blueprint def-weil-exceptional-inverse-image.
(blueprint: def-pur-adic-support-realization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry SheafOfModules
private theorem transpose_square
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (V : C ⥤ C') (W : D ⥤ D')
    (α : V ⋙ L' ⟶ L ⋙ W) (β : R ⋙ V ⟶ W ⋙ R')
    (hu : ∀ M, V.map (a.unit.app M) ≫ β.app (L.obj M) =
      b.unit.app (V.obj M) ≫ R'.map (α.app M))
    (M : C) (N : D) (h : L.obj M ⟶ N) :
    b.homEquiv _ _ (α.app M ≫ W.map h) = V.map (a.homEquiv _ _ h) ≫ β.app N := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, V.map_comp, R'.map_comp]
  have hn := β.naturality h
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, hn, ← Category.assoc, ← hu, Category.assoc]

private theorem left_square_unique
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (V : C ⥤ C') (W : D ⥤ D')
    [V.IsEquivalence] [W.IsEquivalence] (β : R ⋙ V ≅ W ⋙ R') :
    ∃! e : L ⋙ W ≅ V ⋙ L', ∀ M N (h : L.obj M ⟶ N),
      b.homEquiv _ _ (e.inv.app M ≫ W.map h) =
        V.map (a.homEquiv _ _ h) ≫ β.hom.app N := by
  let α := (mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β.hom)
  have : IsIso α.natTrans := isIso_inverseMate_of_equivalences a b β
  refine ⟨(asIso α.natTrans).symm, ?_, ?_⟩
  · intro M N h
    exact transpose_square a b V W α.natTrans β.hom
      (unit_mateEquiv_symm a b (.mk _ _ _ _ β.hom)) M N h
  · intro e he
    apply Iso.ext_inv
    ext M
    apply (b.homEquiv _ _).injective
    simpa using (he M (L.obj M) (𝟙 _)).trans
      (transpose_square a b V W α.natTrans β.hom
        (unit_mateEquiv_symm a b (.mk _ _ _ _ β.hom)) M (L.obj M) (𝟙 _)).symm

private theorem right_square_unique
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (V : C ⥤ C') (W : D ⥤ D')
    [V.IsEquivalence] [W.IsEquivalence] (e : L ⋙ W ≅ V ⋙ L') :
    ∃! β : R ⋙ V ≅ W ⋙ R', ∀ M N (h : L.obj M ⟶ N),
      b.homEquiv _ _ (e.inv.app M ≫ W.map h) =
        V.map (a.homEquiv _ _ h) ≫ β.hom.app N := by
  let β := (mateEquiv a b (.mk _ _ _ _ e.inv)).natTrans
  have : IsIso β := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful a b V W e.symm
  refine ⟨asIso β, ?_, ?_⟩
  · intro M N h
    exact transpose_square a b V W e.inv β (unit_mateEquiv a b (.mk _ _ _ _ e.inv)) M N h
  · intro q hq
    ext N
    have h₁ := hq (R.obj N) N (a.counit.app N)
    have h₂ := transpose_square a b V W e.inv β
      (unit_mateEquiv a b (.mk _ _ _ _ e.inv)) (R.obj N) N (a.counit.app N)
    change q.hom.app N = β.app N
    simpa only [← a.homEquiv_symm_id N, Equiv.apply_symm_apply, V.map_id,
      Category.id_comp] using h₁.symm.trans h₂

private theorem localization_square_unique
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    {F G : D ⥤ E} {A B : C ⥤ E}
    (a : Q ⋙ F ≅ A) (b : Q ⋙ G ≅ B) (t : A ≅ B) :
    ∃! e : F ≅ G, ∀ X, e.hom.app (Q.obj X) ≫ b.hom.app X =
      a.hom.app X ≫ t.hom.app X := by
  let ff := Localization.fullyFaithfulWhiskeringLeft Q W E
  let e := ff.preimageIso (a ≪≫ t ≪≫ b.symm)
  have he (X : C) : e.hom.app (Q.obj X) =
      (a ≪≫ t ≪≫ b.symm).hom.app X :=
    congr_app (ff.map_preimage (a ≪≫ t ≪≫ b.symm).hom) X
  refine ⟨e, ?_, ?_⟩
  · intro X
    rw [he]
    simp
  · intro q hq
    apply Iso.ext
    apply Localization.natTrans_ext Q W
    intro X
    rw [he]
    apply (cancel_mono (b.hom.app X)).1
    simpa using hq X

namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)
section CompactSupport
variable (c : Compactification g)
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)

/-- Open-extension realization is the mate of the unit-normalized inverse-image
comparison. Its Hom-transpose equation determines the map itself.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization).
Proof: extension by zero is left adjoint to the exact open inverse image in both
presentations. Transport these adjunctions along the realization equivalences and
take the mate of integralExceptionalEtaleInverse. The displayed equation is its
adjunction characterization; bijectivity of the Hom transposes gives uniqueness. -/
theorem integralExceptionalEtaleOpen_existsUnique (n : ℕ) :
    ∃! e : S.val.levelOpen n ⋙ integralExceptionalEtaleRealization l E c.Z n ≅
      integralExceptionalEtaleRealization l E X n ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i,
      ∀ (M : strictEtaleLevel X (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n)
        (N : strictEtaleLevel c.Z (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n)
        (h : (S.val.levelOpen n).obj M ⟶ N),
        (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i).homEquiv _ _
          (e.inv.app M ≫ (integralExceptionalEtaleRealization l E c.Z n).map h) =
        (integralExceptionalEtaleRealization l E X n).map
          ((S.val.levelOpenAdjunction n).homEquiv _ _ h) ≫
          (integralExceptionalEtaleInverse l E c.i S.openImage n).hom.app N := by
  exact left_square_unique (S.val.levelOpenAdjunction n)
    (Etale.openImmersionLowerShriekUpperStarAdjunction _ c.i)
    (integralExceptionalEtaleRealization l E X n)
    (integralExceptionalEtaleRealization l E c.Z n)
    (integralExceptionalEtaleInverse l E c.i S.openImage n)

/-- The ordinary open-extension mate, fixed by its transpose equation.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization). -/
def integralExceptionalEtaleOpen (n : ℕ) :
    S.val.levelOpen n ⋙ integralExceptionalEtaleRealization l E c.Z n ≅
      integralExceptionalEtaleRealization l E X n ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i :=
  (integralExceptionalEtaleOpen_existsUnique l E g c S n).choose

/-- The full exact-localization square on every cochain representative.
Source: blueprint integral exceptional realization
(blueprint: def-pur-adic-support-realization). -/
def IsIntegralExceptionalEtaleDerivedOpen (n : ℕ)
    (e : S.levelDerivedOpen n ⋙
      (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i).mapDerivedCategory) :
      Prop :=
  ∀ J : CochainComplex (strictEtaleLevel X (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) ℤ,
        e.hom.app (DerivedCategory.Q.obj J) ≫
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
              c.i).mapDerivedCategory.map
                ((integralExceptionalEtaleRealization l E X n).mapDerivedCategoryFactors.hom.app
                   J) ≫
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
              c.i).mapDerivedCategoryFactors.hom.app
                (((integralExceptionalEtaleRealization l E X n).mapHomologicalComplex
                   (.up ℤ)).obj J) =
        (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory.map
          ((S.val.levelOpenFactors n).hom.app J) ≫
        (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategoryFactors.hom.app
          (((S.val.levelOpen n).mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (integralExceptionalEtaleOpen l E g c S n).hom (.up ℤ)).app J)

/-- The exact derived open comparison is fixed on every cochain representative by
the recorded exact factorization and the ordinary adjunction mate.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization).
Proof: apply the exact localization functor to the ordinary comparison. The defining
localization factorization is precisely the displayed square. Every derived object
has a complex representative and every derived arrow is a roof; hence that square
also determines the natural isomorphism uniquely. -/
theorem integralExceptionalEtaleDerivedOpen_existsUnique (n : ℕ) :
    ∃! e : S.levelDerivedOpen n ⋙
      (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i).mapDerivedCategory,
      IsIntegralExceptionalEtaleDerivedOpen l E g c S n e := by
  let V := integralExceptionalEtaleRealization l E X n
  let W := integralExceptionalEtaleRealization l E c.Z n
  let O := Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
    (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i
  let a : DerivedCategory.Q ⋙ (S.levelDerivedOpen n ⋙ W.mapDerivedCategory) ≅
      (S.val.levelOpen n).mapHomologicalComplex (.up ℤ) ⋙
        W.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (S.val.levelOpenFactors n) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ W.mapDerivedCategoryFactors
  let b : DerivedCategory.Q ⋙ (V.mapDerivedCategory ⋙ O.mapDerivedCategory) ≅
      V.mapHomologicalComplex (.up ℤ) ⋙
        O.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight V.mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ O.mapDerivedCategoryFactors
  let t : (S.val.levelOpen n).mapHomologicalComplex (.up ℤ) ⋙
        W.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅
      V.mapHomologicalComplex (.up ℤ) ⋙
        O.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun J ↦ DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (integralExceptionalEtaleOpen l E g c S n)
        (.up ℤ)).app J)) (by
      intro J K f
      dsimp
      rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
      congr 1
      exact (NatTrans.mapHomologicalComplex
        (integralExceptionalEtaleOpen l E g c S n).hom (.up ℤ)).naturality f)
  simpa only [IsIntegralExceptionalEtaleDerivedOpen, a, b, t, V, W, O,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.app_hom,
    NatIso.mapHomologicalComplex, Category.id_comp, Category.comp_id,
    Category.assoc] using
    localization_square_unique DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) a b t

/-- The exact derived open comparison, specified by its representative square.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization). -/
def integralExceptionalEtaleDerivedOpen (n : ℕ) :
    S.levelDerivedOpen n ⋙
      (integralExceptionalEtaleRealization l E c.Z n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) c.i).mapDerivedCategory :=
  (integralExceptionalEtaleDerivedOpen_existsUnique l E g c S n).choose

/-- The compact-support realization, literally the open comparison followed by the
proper comparison. Each factor retains its universal normalization.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization). -/
def integralExceptionalEtaleSupportComparison (n : ℕ) :
    S.levelFunctor n ⋙ (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ⋙
        Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (integralExceptionalEtaleDerivedRight l E c.g S.properImage n
      (S.properDerived.level n)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (integralExceptionalEtaleDerivedOpen l E g c S n) _ ≪≫
    Functor.associator _ _ _
/-- The full compact-support adjunction-transpose normalization.
Source: blueprint integral exceptional realization
(blueprint: def-pur-adic-support-realization). -/
def IsIntegralExceptionalEtaleRightAdjoint (n : ℕ)
    (G : StrictEtaleExceptionalAdjoint (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) c S)
    (H : DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ⥤
      DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E (n + 1)))) c ⊣ H)
    (e : G.levelRight n ⋙ (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ⋙ H) : Prop :=
  ∀ (M : DerivedCategory (strictEtaleLevel X (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n))
        (N : DerivedCategory (strictEtaleLevel Y (integralExceptionalIntegers l E)
          (integralExceptionalUniformizer l E) n))
        (h : (S.levelFunctor n).obj M ⟶ N),
        adj.homEquiv _ _
          ((integralExceptionalEtaleSupportComparison l E g c S n).inv.app M ≫
            (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory.map h) =
        (integralExceptionalEtaleRealization l E X n).mapDerivedCategory.map
          ((G.levelAdjunction n).homEquiv _ _ h) ≫ e.hom.app N

/-- The finite exceptional realization is the mate of the already specified compact-
support realization. The Hom-transpose equation fixes its map, including the counit.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization).
Proof: compose the generic finite adjunction with the realization equivalences. The
compact-support comparison identifies its left adjoint with the fixed finite compact-
support functor. The induced right-adjoint comparison is uniquely determined by the
Hom-transpose equation. Applying the inverse realization gives its inverse. -/
theorem integralExceptionalEtaleRightAdjoint_existsUnique (n : ℕ)
    (G : StrictEtaleExceptionalAdjoint (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) c S)
    (H : DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ⥤
      DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E (n + 1)))) c ⊣ H) :
    ∃! e : G.levelRight n ⋙ (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ⋙ H,
      IsIntegralExceptionalEtaleRightAdjoint l E g c S n G H adj e := by
  exact right_square_unique (G.levelAdjunction n) adj
    (integralExceptionalEtaleRealization l E X n).mapDerivedCategory
    (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory
    (integralExceptionalEtaleSupportComparison l E g c S n)

/-- The finite right-adjoint comparison, fixed by the compact-support counit equation.
Source: blueprint integral exceptional image (blueprint: def-pur-adic-support-realization). -/
@[no_expose] def integralExceptionalEtaleRightAdjoint (n : ℕ)
    (G : StrictEtaleExceptionalAdjoint (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) c S)
    (H : DerivedCategory
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ⥤
      DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))))
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E (n + 1)))) c ⊣ H) :
    G.levelRight n ⋙ (integralExceptionalEtaleRealization l E X n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E Y n).mapDerivedCategory ⋙ H :=
  (integralExceptionalEtaleRightAdjoint_existsUnique l E g c S n G H adj).choose

end CompactSupport

end WeilConjectures
