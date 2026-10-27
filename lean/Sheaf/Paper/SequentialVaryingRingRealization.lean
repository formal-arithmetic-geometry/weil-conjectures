/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Sequential realization with varying coefficient rings

Source: blueprint main-20261015, lem-coef-integral-compact-support, proof paragraph 2;
Stacks Tags 05RT, 04VI and 02MZ (blueprint: lem-coef-sequential-varying-ring-realization).
Natural index n means positive level n+1. All restrictions retain the coefficient actions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.SequentialVaryingRing
attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.mapDerivedCategoryFactorsh SheafOfModules.monoidalCategory
attribute [local instance 3000] reductionModulesHasDerivedCategory
  reductionTowerHasDerivedCategory reductionRingModulesHasDerivedCategory
  Abelian.hasFiniteLimits Abelian.hasFiniteColimits
set_option allowUnsafeReducibility true in
attribute [local reducible] reductionRestrict reductionModulesHasDerivedCategory
  reductionTowerHasDerivedCategory reductionRingModulesHasDerivedCategory
attribute [local instance 3000] reductionRestrict_preservesFiniteLimits
  reductionRestrict_preservesFiniteColimits reductionRestrict_additive

private instance evalLimits (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) RingCat.{u + 1}) (n : ℕ) :
    PreservesFiniteLimits (reductionTowerEvaluation T R n) where
  preservesFiniteLimits _J _ _ := evaluation_preservesLimitsOfShape (op n)

private instance evalColimits (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) RingCat.{u + 1}) (n : ℕ) :
    PreservesFiniteColimits (reductionTowerEvaluation T R n) where
  preservesFiniteColimits _J _ _ := evaluation_preservesColimitsOfShape (op n)

variable (T : Scheme.{u})

/-- Identity-on-sections composition of scalar restrictions, including the given equality
of ring maps. Source: Stacks 03DA (blueprint: lem-coef-sequential-varying-ring-realization). -/
def restrictionComp {A B C : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : A ⟶ B) (b : B ⟶ C) (d : A ⟶ C) (h : a ≫ b = d) :
    reductionRestrict T b ⋙ reductionRestrict T a ≅ reductionRestrict T d :=
  by
  subst d
  refine NatIso.ofComponents (fun M ↦ Iso.refl _) ?_
  intro X Y f
  ext U x
  rfl

/-- Canonical derived composition, normalized by its ordinary identity-on-sections map.
Source: Stacks 015F (blueprint: lem-coef-sequential-varying-ring-realization). -/
def derivedComp {A B C : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : A ⟶ B) (b : B ⟶ C) (d : A ⟶ C) (h : a ≫ b = d) :=
  exactDerivedRestrictionComposition (reductionRestrict T b) (reductionRestrict T a)
    (reductionRestrict T d) (restrictionComp T a b d h)

/-- Identity restriction on the derived category, with its canonical unit comparison.
Source: Stacks 015F (blueprint: lem-coef-sequential-varying-ring-realization). -/
def derivedId (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    reductionDerivedRestrict T (𝟙 A) ≅ 𝟭 (reductionDerivedCategory T A) :=
  exactDerivedRestrictionUnit (reductionRestrict T (𝟙 A))
    (NatIso.ofComponents (fun M ↦ Iso.refl _) (by intro X Y f; ext U x; rfl))

variable (B : ℕᵒᵖ ⥤ Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (c : Cone B)

/-- The chain-level composition comparison for the coefficient cone.
Source: Stacks 03DA (blueprint: lem-coef-sequential-varying-ring-realization). -/
def coneComplexComp {m n : ℕ} (h : n ≤ m) :=
  Functor.mapHomologicalComplexCompIso
    (restrictionComp T (c.π.app (op m)) (B.map (homOfLE h).op)
      (c.π.app (op n)) (c.w (homOfLE h).op)) (.up ℤ)

/-- The actual constant-R tower of restricted complexes, assembled from adjacent chain maps.
Source: blueprint paragraph 2 (blueprint: lem-coef-sequential-varying-ring-realization). -/
def restrictedTower
    (C : ∀ n : ℕ, CochainComplex (reductionModules T (B.obj (op n))) ℤ)
    (t : ∀ (m n : ℕ) (h : n ≤ m), C m ⟶
      ((reductionRestrict T (B.map (homOfLE h).op)).mapHomologicalComplex (.up ℤ)).obj
        (C n)) :
    ℕᵒᵖ ⥤ CochainComplex (reductionModules T c.pt) ℤ :=
  Functor.ofOpSequence (fun n ↦
    ((reductionRestrict T (c.π.app (op (n + 1)))).mapHomologicalComplex (.up ℤ)).map
      (t (n + 1) n (Nat.le_succ n)) ≫
    (coneComplexComp T B c (Nat.le_succ n)).hom.app (C n))

/-- The canonical evaluation isomorphism, using equality of actual complexes before
localization. Source: Stacks 015F (blueprint: lem-coef-sequential-varying-ring-realization). -/
def evaluationIso
    (M : ∀ n : ℕ, reductionDerivedCategory T (B.obj (op n)))
    (C : ∀ n : ℕ, CochainComplex (reductionModules T (B.obj (op n))) ℤ)
    (i : ∀ n : ℕ, DerivedCategory.Q.obj (C n) ≅ M n)
    (t : ∀ (m n : ℕ) (h : n ≤ m), C m ⟶
      ((reductionRestrict T (B.map (homOfLE h).op)).mapHomologicalComplex (.up ℤ)).obj
        (C n))
    (S : CochainComplex (reductionTowerCategory T (reductionModuleRing T c.pt)) ℤ)
    (hS : S.asFunctor = restrictedTower T B c C t) (n : ℕ) :
    (reductionTowerDerivedEvaluation T (reductionModuleRing T c.pt) n).obj
        (DerivedCategory.Q.obj S) ≅
      (reductionDerivedRestrict T (c.π.app (op n))).obj (M n) :=
  (reductionTowerEvaluation T (reductionModuleRing T c.pt) n).mapDerivedCategoryFactors.app S
    ≪≫ DerivedCategory.Q.mapIso (eqToIso (congrArg
      (fun F : ℕᵒᵖ ⥤ CochainComplex (reductionModules T c.pt) ℤ ↦ F.obj (op n)) hS))
    ≪≫ ((reductionRestrict T (c.π.app (op n))).mapDerivedCategoryFactors.app (C n)).symm
    ≪≫ (reductionDerivedRestrict T (c.π.app (op n))).mapIso (i n)

/-- The evaluated transition of the localized strict tower, using the canonical exact
factorizations. Source: Stacks 015F (blueprint: lem-coef-sequential-varying-ring-realization). -/
def evaluatedTransition
    (S : CochainComplex (reductionTowerCategory T (reductionModuleRing T c.pt)) ℤ)
    (m n : ℕ) (h : n ≤ m) :
    (reductionTowerDerivedEvaluation T (reductionModuleRing T c.pt) m).obj
        (DerivedCategory.Q.obj S) ⟶
      (reductionTowerDerivedEvaluation T (reductionModuleRing T c.pt) n).obj
        (DerivedCategory.Q.obj S) :=
  (reductionTowerEvaluation T (reductionModuleRing T c.pt) m).mapDerivedCategoryFactors.hom.app S
    ≫ DerivedCategory.Q.map (S.asFunctor.map (homOfLE h).op) ≫
    (reductionTowerEvaluation T (reductionModuleRing T c.pt) n).mapDerivedCategoryFactors.inv.app S

attribute [local irreducible] derivedComp derivedId

private theorem localize_comp_generic
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
    (F : D ⥤ B) (G : B ⥤ A) (H : D ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H)
    {X : CochainComplex A ℤ} {Y : CochainComplex B ℤ} {Z : CochainComplex D ℤ}
    (g : X ⟶ (G.mapHomologicalComplex (.up ℤ)).obj Y)
    (f : Y ⟶ (F.mapHomologicalComplex (.up ℤ)).obj Z) :
    DerivedCategory.Q.map
        (g ≫ (G.mapHomologicalComplex (.up ℤ)).map f ≫
          (NatIso.mapHomologicalComplex e (.up ℤ)).hom.app Z) ≫
      H.mapDerivedCategoryFactors.inv.app Z =
    DerivedCategory.Q.map g ≫ G.mapDerivedCategoryFactors.inv.app Y ≫
      G.mapDerivedCategory.map
        (DerivedCategory.Q.map f ≫ F.mapDerivedCategoryFactors.inv.app Z) ≫
      (exactDerivedRestrictionComposition F G H e).hom.app (DerivedCategory.Q.obj Z) := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← exactDerivedRestrictionComposition_inv_factors F G H e Z]
  have hn := G.mapDerivedCategoryFactors.inv.naturality f
  simpa only [Category.assoc, CategoryTheory.Functor.comp_map] using
    congrArg (fun k ↦ DerivedCategory.Q.map g ≫ k ≫
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app Z) ≫
    (exactDerivedRestrictionComposition F G H e).hom.app (DerivedCategory.Q.obj Z)) hn

private theorem postcompose_comparison
    {A B D : Type*} [Category A] [Category B] [Category D]
    (F : D ⥤ B) (G : B ⥤ A) (H : D ⥤ A) (e : F ⋙ G ≅ H)
    {W X : A} {Y : B} {Z Z' : D}
    (x : W ⟶ X) (y : X ⟶ G.obj Y) (f : Y ⟶ F.obj Z) (i : Z ⟶ Z')
    (k : W ⟶ H.obj Z)
    (hk : k = x ≫ y ≫ G.map f ≫ e.hom.app Z) :
    k ≫ H.map i = x ≫ y ≫ G.map (f ≫ F.map i) ≫ e.hom.app Z' := by
  rw [hk]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← e.hom.naturality]
  rfl

private theorem unit_transport {D : Type*} [Category D] (R : D ⥤ D)
    (e : R ≅ 𝟭 D) {X M : D} (i : X ≅ M) (τ : M ⟶ R.obj M)
    (hτ : τ ≫ e.hom.app M = 𝟙 M) (f : X ⟶ R.obj X)
    (hf : f = e.inv.app X) : f ≫ R.map i.hom = i.hom ≫ τ := by
  rw [hf]
  apply (cancel_mono (e.hom.app M)).mp
  rw [Category.assoc, e.hom.naturality, Iso.inv_hom_id_app_assoc,
    Category.assoc, hτ, Category.comp_id]
  rfl

private theorem liftArrow
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (M : DerivedCategory A) (K : CochainComplex A ℤ)
    (f : M ⟶ DerivedCategory.Q.obj K) :
    ∃ (L : CochainComplex A ℤ) (i : DerivedCategory.Q.obj L ≅ M) (t : L ⟶ K),
      DerivedCategory.Q.map t = i.hom ≫ f := by
  let i := DerivedCategory.Q.objObjPreimageIso M
  obtain ⟨L', s, hs, t, ht⟩ := DerivedCategory.right_fac (i.hom ≫ f)
  have := hs
  refine ⟨L', asIso (DerivedCategory.Q.map s) ≪≫ i, t, ?_⟩
  simpa only [Iso.trans_hom, asIso_hom, Category.assoc,
    IsIso.hom_inv_id_assoc] using
    (congrArg (fun k ↦ DerivedCategory.Q.map s ≫ k) ht).symm

private def transpose {A : Type*} [Category A] [HasZeroMorphisms A]
    (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) : CochainComplex (ℕᵒᵖ ⥤ A) ℤ where
  X k := F ⋙ HomologicalComplex.eval A (.up ℤ) k
  d k l :=
    { app := fun n ↦ (F.obj n).d k l
      naturality := fun _ _ f ↦ (F.map f).comm k l }
  shape k l h := by ext n; exact (F.obj n).shape k l h
  d_comp_d' k l m _ _ := by ext n; exact (F.obj n).d_comp_d k l m

private theorem transpose_asFunctor {A : Type*} [Category A] [HasZeroMorphisms A]
    (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) : (transpose F).asFunctor = F := rfl

private theorem adjacentRepresentatives
    (M : ∀ n : ℕ, reductionDerivedCategory T (B.obj (op n)))
    (τ : ∀ n : ℕ, M (n + 1) ⟶
      (reductionDerivedRestrict T (B.map (homOfLE (Nat.le_succ n)).op)).obj (M n))
    (C₀ : CochainComplex (reductionModules T (B.obj (op 0))) ℤ)
    (i₀ : DerivedCategory.Q.obj C₀ ≅ M 0) :
    ∃ (C : ∀ n : ℕ, CochainComplex (reductionModules T (B.obj (op n))) ℤ)
      (i : ∀ n : ℕ, DerivedCategory.Q.obj (C n) ≅ M n)
      (s : ∀ n : ℕ, C (n + 1) ⟶
        ((reductionRestrict T (B.map (homOfLE (Nat.le_succ n)).op)).mapHomologicalComplex
          (.up ℤ)).obj (C n)),
      C 0 = C₀ ∧ HEq (i 0) i₀ ∧ ∀ n : ℕ,
        DerivedCategory.Q.map (s n) ≫
        (reductionRestrict T (B.map (homOfLE (Nat.le_succ n)).op)).mapDerivedCategoryFactors.inv.app
            (C n) ≫
          (reductionDerivedRestrict T (B.map (homOfLE (Nat.le_succ n)).op)).map (i n).hom =
        (i (n + 1)).hom ≫ τ n := by
  classical
  let P (n : ℕ) := Σ C : CochainComplex (reductionModules T (B.obj (op n))) ℤ,
    DerivedCategory.Q.obj C ≅ M n
  have step (n : ℕ) (p : P n) := liftArrow (M (n + 1))
    (((reductionRestrict T (B.map (homOfLE (Nat.le_succ n)).op)).mapHomologicalComplex
      (.up ℤ)).obj p.1)
    (τ n ≫ (reductionDerivedRestrict T (B.map (homOfLE (Nat.le_succ n)).op)).map p.2.inv ≫
      (reductionRestrict T (B.map (homOfLE (Nat.le_succ n)).op)).mapDerivedCategoryFactors.hom.app
        p.1)
  choose X i g hg using step
  let p : ∀ n, P n := fun n ↦ Nat.rec ⟨C₀, i₀⟩ (fun n p ↦ ⟨X n p, i n p⟩) n
  refine ⟨fun n ↦ (p n).1, fun n ↦ (p n).2, fun n ↦ g n (p n), rfl, HEq.rfl, ?_⟩
  intro n
  rw [hg]
  simp only [reductionDerivedRestrict, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

private abbrev resC {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : A ⟶ B) := (reductionRestrict T a).mapHomologicalComplex (.up ℤ)

private def compC {A B D : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : B ⟶ D) (b : A ⟶ B) (d : A ⟶ D) (h : b ≫ a = d)
    {X : CochainComplex (reductionModules T A) ℤ}
    {Y : CochainComplex (reductionModules T B) ℤ}
    {Z : CochainComplex (reductionModules T D) ℤ}
    (g : X ⟶ (resC T b).obj Y) (f : Y ⟶ (resC T a).obj Z) :
    X ⟶ (resC T d).obj Z :=
  g ≫ (resC T b).map f ≫
    (Functor.mapHomologicalComplexCompIso (restrictionComp T b a d h) (.up ℤ)).hom.app Z

private theorem compC_assoc
    {A B D E : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : D ⟶ E) (b : B ⟶ D) (e : A ⟶ B)
    (ab : B ⟶ E) (be : A ⟶ D) (abe : A ⟶ E)
    (hab : b ≫ a = ab) (hbe : e ≫ b = be)
    (h₁ : e ≫ ab = abe) (h₂ : be ≫ a = abe)
    {W : CochainComplex (reductionModules T A) ℤ}
    {X : CochainComplex (reductionModules T B) ℤ}
    {Y : CochainComplex (reductionModules T D) ℤ}
    {Z : CochainComplex (reductionModules T E) ℤ}
    (k : W ⟶ (resC T e).obj X) (g : X ⟶ (resC T b).obj Y)
    (f : Y ⟶ (resC T a).obj Z) :
    compC T ab e abe h₁ k (compC T a b ab hab g f) =
      compC T a be abe h₂ (compC T b e be hbe k g) f := by
  subst ab be abe
  ext j U x
  rfl

private def idC {A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : A ⟶ A) (h : a = 𝟙 A)
    (X : CochainComplex (reductionModules T A) ℤ) : X ⟶ (resC T a).obj X :=
  eqToHom (by
    subst a
    refine HomologicalComplex.ext (by funext k; rfl) ?_
    intro k l hkl
    ext U x
    rfl)

private theorem idC_heq {A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : A ⟶ A) (h : a = 𝟙 A)
    (X : CochainComplex (reductionModules T A) ℤ) : HEq (idC T a h X) (𝟙 X) := by
  exact eqToHom_heq_id_dom _ _ _

private theorem compC_id_left {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : A ⟶ B) (b : A ⟶ A) (h : b = 𝟙 A) (w : b ≫ a = a)
    {X : CochainComplex (reductionModules T A) ℤ}
    {Y : CochainComplex (reductionModules T B) ℤ}
    (f : X ⟶ (resC T a).obj Y) :
    compC T a b a w (idC T b h X) f = f := by
  subst b
  ext j U x
  rfl

@[no_expose] private def allTransitions
    (C : ∀ n : ℕ, CochainComplex (reductionModules T (B.obj (op n))) ℤ)
    (s : ∀ n : ℕ, C (n + 1) ⟶
      (resC T (B.map (homOfLE (Nat.le_succ n)).op)).obj (C n))
    (m n : ℕ) (h : n ≤ m) : C m ⟶ (resC T (B.map (homOfLE h).op)).obj (C n) :=
  Nat.leRec (motive := fun m h ↦
    C m ⟶ (resC T (B.map (homOfLE h).op)).obj (C n))
    (idC T _ (B.map_id (op n)) (C n))
    (fun {m} h f ↦ compC T (B.map (homOfLE h).op)
      (B.map (homOfLE (Nat.le_succ m)).op)
      (B.map (homOfLE (h.trans (Nat.le_succ m))).op)
      (B.map_comp (homOfLE (Nat.le_succ m)).op (homOfLE h).op).symm (s m) f) h

private theorem allTransitions_self
    (C : ∀ n : ℕ, CochainComplex (reductionModules T (B.obj (op n))) ℤ)
    (s : ∀ n : ℕ, C (n + 1) ⟶
      (resC T (B.map (homOfLE (Nat.le_succ n)).op)).obj (C n)) (n : ℕ) :
    allTransitions T B C s n n le_rfl = idC T _ (B.map_id (op n)) (C n) :=
  Nat.leRec_self _ _

private theorem allTransitions_id
    (C : ∀ n : ℕ, CochainComplex (reductionModules T (B.obj (op n))) ℤ)
    (s : ∀ n : ℕ, C (n + 1) ⟶
      (resC T (B.map (homOfLE (Nat.le_succ n)).op)).obj (C n)) (n : ℕ) :
    HEq (allTransitions T B C s n n le_rfl) (𝟙 (C n)) := by
  rw [allTransitions_self]
  exact idC_heq T _ (B.map_id (op n)) (C n)

private theorem allTransitions_succ
    (C : ∀ n : ℕ, CochainComplex (reductionModules T (B.obj (op n))) ℤ)
    (s : ∀ n : ℕ, C (n + 1) ⟶
      (resC T (B.map (homOfLE (Nat.le_succ n)).op)).obj (C n))
    (m n : ℕ) (h : n ≤ m) :
    allTransitions T B C s (m + 1) n (h.trans (Nat.le_succ m)) =
      compC T (B.map (homOfLE h).op) (B.map (homOfLE (Nat.le_succ m)).op)
        (B.map (homOfLE (h.trans (Nat.le_succ m))).op)
        (B.map_comp (homOfLE (Nat.le_succ m)).op (homOfLE h).op).symm
        (s m) (allTransitions T B C s m n h) := by
  exact Nat.leRec_succ _ _ h

private theorem allTransitions_comp
    (C : ∀ n : ℕ, CochainComplex (reductionModules T (B.obj (op n))) ℤ)
    (s : ∀ n : ℕ, C (n + 1) ⟶
      (resC T (B.map (homOfLE (Nat.le_succ n)).op)).obj (C n))
    (r m n : ℕ) (hnm : n ≤ m) (hmr : m ≤ r) :
    allTransitions T B C s r n (hnm.trans hmr) =
      compC T (B.map (homOfLE hnm).op) (B.map (homOfLE hmr).op)
        (B.map (homOfLE (hnm.trans hmr)).op)
        (B.map_comp (homOfLE hmr).op (homOfLE hnm).op).symm
        (allTransitions T B C s r m hmr) (allTransitions T B C s m n hnm) := by
  induction r, hmr using Nat.le_induction with
  | base =>
    have he := allTransitions_self T B C s m
    rw [he]
    exact (compC_id_left T _ _ (B.map_id _) _ _).symm
  | succ r h ih =>
    rw [allTransitions_succ T B C s r n (hnm.trans h),
      allTransitions_succ T B C s r m h]
    rw [ih]
    exact compC_assoc T _ _ _ _ _ _ _ _ _ _ _ _ _

attribute [local irreducible] compC

private theorem compC_localize
    {A B D : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : B ⟶ D) (b : A ⟶ B) (d : A ⟶ D) (h : b ≫ a = d)
    {X : CochainComplex (reductionModules T A) ℤ}
    {Y : CochainComplex (reductionModules T B) ℤ}
    {Z : CochainComplex (reductionModules T D) ℤ}
    (g : X ⟶ (resC T b).obj Y) (f : Y ⟶ (resC T a).obj Z) :
    DerivedCategory.Q.map (compC T a b d h g f) ≫
        (reductionRestrict T d).mapDerivedCategoryFactors.inv.app Z =
      DerivedCategory.Q.map g ≫ (reductionRestrict T b).mapDerivedCategoryFactors.inv.app Y ≫
        (reductionDerivedRestrict T b).map
          (DerivedCategory.Q.map f ≫ (reductionRestrict T a).mapDerivedCategoryFactors.inv.app Z) ≫
        (derivedComp T b a d h).hom.app (DerivedCategory.Q.obj Z) := by
  simpa only [derivedComp, compC, mapHomologicalComplexCompIso] using
    localize_comp_generic (reductionRestrict T a) (reductionRestrict T b)
    (reductionRestrict T d) (restrictionComp T b a d h) g f

private theorem compC_localize_iso
    {A B D : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : B ⟶ D) (b : A ⟶ B) (d : A ⟶ D) (h : b ≫ a = d)
    {X : CochainComplex (reductionModules T A) ℤ}
    {Y : CochainComplex (reductionModules T B) ℤ}
    {Z : CochainComplex (reductionModules T D) ℤ}
    (g : X ⟶ (resC T b).obj Y) (f : Y ⟶ (resC T a).obj Z)
    {M : reductionDerivedCategory T D} (i : DerivedCategory.Q.obj Z ≅ M) :
    DerivedCategory.Q.map (compC T a b d h g f) ≫
        (reductionRestrict T d).mapDerivedCategoryFactors.inv.app Z ≫
        (reductionDerivedRestrict T d).map i.hom =
      DerivedCategory.Q.map g ≫ (reductionRestrict T b).mapDerivedCategoryFactors.inv.app Y ≫
        (reductionDerivedRestrict T b).map
          (DerivedCategory.Q.map f ≫ (reductionRestrict T a).mapDerivedCategoryFactors.inv.app Z ≫
            (reductionDerivedRestrict T a).map i.hom) ≫
        (derivedComp T b a d h).hom.app M := by
  simpa only [Category.assoc] using postcompose_comparison
    (reductionDerivedRestrict T a) (reductionDerivedRestrict T b)
    (reductionDerivedRestrict T d) (derivedComp T b a d h)
    (DerivedCategory.Q.map g) ((reductionRestrict T b).mapDerivedCategoryFactors.inv.app Y)
    (DerivedCategory.Q.map f ≫ (reductionRestrict T a).mapDerivedCategoryFactors.inv.app Z)
    i.hom _ (compC_localize T a b d h g f)

private theorem unit_localization {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (F : A ⥤ A) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (e : F ≅ 𝟭 A)
    (X : CochainComplex A ℤ) (f : X ⟶ (F.mapHomologicalComplex (.up ℤ)).obj X)
    (hf : f ≫ (NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
      mapHomologicalComplexIdIso A (.up ℤ)).hom.app X = 𝟙 X) :
    DerivedCategory.Q.map f ≫ F.mapDerivedCategoryFactors.inv.app X =
      (exactDerivedRestrictionUnit F e).inv.app (DerivedCategory.Q.obj X) := by
  apply (cancel_mono ((exactDerivedRestrictionUnit F e).hom.app
    (DerivedCategory.Q.obj X))).mp
  rw [Category.assoc, exactDerivedRestrictionUnit_inv_factors,
    ← CategoryTheory.Functor.map_comp, hf, CategoryTheory.Functor.map_id,
    Iso.inv_hom_id_app]
  rfl

private theorem derived_refl_inv {A D : Type*} [Category A] [Category D]
    [Abelian A] [Abelian D] [HasDerivedCategory A] [HasDerivedCategory D]
    (F : A ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (mapDerivedCategoryNatIso (Iso.refl F)).inv = 𝟙 _ := by
  apply (cancel_mono (mapDerivedCategoryNatIso (Iso.refl F)).hom).mp
  rw [Iso.inv_hom_id, mapDerivedCategoryNatIso_refl, Category.id_comp]

private theorem idC_localize
    {A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : A ⟶ A) (h : a = 𝟙 A)
    (X : CochainComplex (reductionModules T A) ℤ) :
    DerivedCategory.Q.map (idC T a h X) ≫
        (reductionRestrict T a).mapDerivedCategoryFactors.inv.app X =
      ((mapDerivedCategoryNatIso (eqToIso (congrArg (reductionRestrict T) h))) ≪≫
        derivedId T A).inv.app (DerivedCategory.Q.obj X) := by
  subst a
  simp only [eqToIso_refl, Iso.trans_inv,
    derived_refl_inv, Category.comp_id]
  unfold derivedId
  apply unit_localization (reductionRestrict T (𝟙 A))
    (NatIso.ofComponents (fun M ↦ Iso.refl _) (by intro Y Z f; ext U x; rfl)) X
  ext k U x
  rfl

private theorem idC_localize_iso
    {A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : A ⟶ A) (h : a = 𝟙 A)
    (X : CochainComplex (reductionModules T A) ℤ)
    {M : reductionDerivedCategory T A} (i : DerivedCategory.Q.obj X ≅ M)
    (τ : M ⟶ (reductionDerivedRestrict T a).obj M)
    (hτ : τ ≫
      (mapDerivedCategoryNatIso (eqToIso (congrArg (reductionRestrict T) h))).hom.app M ≫
        (derivedId T A).hom.app M = 𝟙 M) :
    DerivedCategory.Q.map (idC T a h X) ≫
        (reductionRestrict T a).mapDerivedCategoryFactors.inv.app X ≫
        (reductionDerivedRestrict T a).map i.hom = i.hom ≫ τ := by
  simpa only [Category.assoc] using unit_transport (reductionDerivedRestrict T a)
    (mapDerivedCategoryNatIso (eqToIso (congrArg (reductionRestrict T) h)) ≪≫ derivedId T A)
    i τ hτ _ (idC_localize T a h X)

private theorem allTransitions_localize
    (M : ∀ n : ℕ, reductionDerivedCategory T (B.obj (op n)))
    (τ : ∀ (m n : ℕ) (h : n ≤ m), M m ⟶
      (reductionDerivedRestrict T (B.map (homOfLE h).op)).obj (M n))
    (hτid : ∀ n : ℕ, τ n n le_rfl ≫
      (mapDerivedCategoryNatIso
        (eqToIso (congrArg (reductionRestrict T) (B.map_id (op n))))).hom.app (M n) ≫
      (derivedId T (B.obj (op n))).hom.app (M n) = 𝟙 (M n))
    (hτcomp : ∀ (r m n : ℕ) (hnm : n ≤ m) (hmr : m ≤ r),
      τ r m hmr ≫ (reductionDerivedRestrict T (B.map (homOfLE hmr).op)).map
        (τ m n hnm) ≫
      (derivedComp T (B.map (homOfLE hmr).op) (B.map (homOfLE hnm).op)
        (B.map (homOfLE (hnm.trans hmr)).op)
        (B.map_comp (homOfLE hmr).op (homOfLE hnm).op).symm).hom.app (M n) =
      τ r n (hnm.trans hmr))
    (C : ∀ n : ℕ, CochainComplex (reductionModules T (B.obj (op n))) ℤ)
    (i : ∀ n : ℕ, DerivedCategory.Q.obj (C n) ≅ M n)
    (s : ∀ n : ℕ, C (n + 1) ⟶
      (resC T (B.map (homOfLE (Nat.le_succ n)).op)).obj (C n))
    (hs : ∀ n : ℕ, DerivedCategory.Q.map (s n) ≫
      (reductionRestrict T (B.map (homOfLE (Nat.le_succ n)).op)).mapDerivedCategoryFactors.inv.app
        (C n) ≫
      (reductionDerivedRestrict T (B.map (homOfLE (Nat.le_succ n)).op)).map (i n).hom =
        (i (n + 1)).hom ≫ τ (n + 1) n (Nat.le_succ n))
    (m n : ℕ) (h : n ≤ m) :
    DerivedCategory.Q.map (allTransitions T B C s m n h) ≫
      (reductionRestrict T (B.map (homOfLE h).op)).mapDerivedCategoryFactors.inv.app (C n) ≫
      (reductionDerivedRestrict T (B.map (homOfLE h).op)).map (i n).hom =
        (i m).hom ≫ τ m n h := by
  induction m, h using Nat.le_induction with
  | base =>
    have he := allTransitions_self T B C s n
    rw [he]
    exact idC_localize_iso T _ (B.map_id _) (C n) (i n) _ (hτid n)
  | succ m h ih =>
    rw [allTransitions_succ T B C s m n h]
    erw [compC_localize_iso T (B.map (homOfLE h).op)
      (B.map (homOfLE (Nat.le_succ m)).op)
      (B.map (homOfLE (h.trans (Nat.le_succ m))).op)
      (B.map_comp (homOfLE (Nat.le_succ m)).op (homOfLE h).op).symm
      (s m) (allTransitions T B C s m n h) (i n), ih]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    have hh := congrArg (fun f ↦ f ≫
      (reductionDerivedRestrict T (B.map (homOfLE (Nat.le_succ m)).op)).map
        (τ m n h) ≫
      (derivedComp T (B.map (homOfLE (Nat.le_succ m)).op) (B.map (homOfLE h).op)
        (B.map (homOfLE (h.trans (Nat.le_succ m))).op)
        (B.map_comp (homOfLE (Nat.le_succ m)).op (homOfLE h).op).symm).hom.app
          (M n)) (hs m)
    simp only [Category.assoc] at hh
    rw [hh, hτcomp]

private def restrictC
    {R A D : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ A) (b : A ⟶ D) (d : R ⟶ D) (h : a ≫ b = d)
    {X : CochainComplex (reductionModules T A) ℤ}
    {Y : CochainComplex (reductionModules T D) ℤ}
    (f : X ⟶ (resC T b).obj Y) :
    (resC T a).obj X ⟶ (resC T d).obj Y :=
  (resC T a).map f ≫
    (Functor.mapHomologicalComplexCompIso (restrictionComp T a b d h) (.up ℤ)).hom.app Y

private theorem restrictC_comp
    {R A D E : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : A ⟶ D) (b : D ⟶ E) (ab : A ⟶ E) (hab : a ≫ b = ab)
    (p : R ⟶ A) (q : R ⟶ D) (r : R ⟶ E)
    (hp : p ≫ a = q) (hq : q ≫ b = r) (hr : p ≫ ab = r)
    {X : CochainComplex (reductionModules T A) ℤ}
    {Y : CochainComplex (reductionModules T D) ℤ}
    {Z : CochainComplex (reductionModules T E) ℤ}
    (f : X ⟶ (resC T a).obj Y) (g : Y ⟶ (resC T b).obj Z) :
    restrictC T p ab r hr (compC T b a ab hab f g) =
      restrictC T p a q hp f ≫ restrictC T q b r hq g := by
  subst q r ab
  unfold restrictC compC
  ext k U x
  rfl

private theorem restrictC_id
    {R A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (p : R ⟶ A) (a : A ⟶ A) (h : a = 𝟙 A) (hp : p ≫ a = p)
    (X : CochainComplex (reductionModules T A) ℤ) :
    restrictC T p a p hp (idC T a h X) = 𝟙 ((resC T p).obj X) := by
  subst a
  ext k U x
  rfl

private theorem ofOpSequence_map_all {A : Type*} [Category A] (X : ℕ → A)
    (v : ∀ m n : ℕ, n ≤ m → (X m ⟶ X n))
    (hid : ∀ n : ℕ, v n n le_rfl = 𝟙 (X n))
    (hcomp : ∀ r m n : ℕ, ∀ (hnm : n ≤ m) (hmr : m ≤ r),
      v r n (hnm.trans hmr) = v r m hmr ≫ v m n hnm)
    (m n : ℕ) (h : n ≤ m) :
    (Functor.ofOpSequence (fun k ↦ v (k + 1) k (Nat.le_succ k))).map
      (homOfLE h).op = v m n h := by
  induction m, h using Nat.le_induction with
  | base => exact ((Functor.ofOpSequence _).map_id (op n)).trans (hid n).symm
  | succ m h ih =>
    have hh : (homOfLE (h.trans (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
    rw [hh, CategoryTheory.Functor.map_comp, ih,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact (hcomp (m + 1) m n h (Nat.le_succ m)).symm

set_option allowUnsafeReducibility true in
attribute [local reducible] restrictedTower Functor.ofOpSequence
  Functor.mapHomologicalComplex

private theorem restrictedTower_map
    (C : ∀ n : ℕ, CochainComplex (reductionModules T (B.obj (op n))) ℤ)
    (s : ∀ n : ℕ, C (n + 1) ⟶
      (resC T (B.map (homOfLE (Nat.le_succ n)).op)).obj (C n))
    (m n : ℕ) (h : n ≤ m) :
    (restrictedTower T B c C (allTransitions T B C s)).map (homOfLE h).op =
      restrictC T (c.π.app (op m)) (B.map (homOfLE h).op) (c.π.app (op n))
        (c.w (homOfLE h).op) (allTransitions T B C s m n h) := by
  let v (m n : ℕ) (h : n ≤ m) := restrictC T (c.π.app (op m))
    (B.map (homOfLE h).op) (c.π.app (op n)) (c.w (homOfLE h).op)
    (allTransitions T B C s m n h)
  change (Functor.ofOpSequence
    (C := CochainComplex (reductionModules T c.pt) ℤ)
    (X := fun k ↦ (resC T (c.π.app (op k))).obj (C k))
    (fun k ↦ v (k + 1) k (Nat.le_succ k))).map
    (homOfLE h).op = v m n h
  refine ofOpSequence_map_all (A := CochainComplex (reductionModules T c.pt) ℤ)
    (fun k ↦ (resC T (c.π.app (op k))).obj (C k)) v
    ?_ ?_ m n h
  · intro k
    have he := allTransitions_self T B C s k
    dsimp only [v]
    rw [he]
    exact restrictC_id T (c.π.app (op k)) (B.map (𝟙 (op k)))
      (B.map_id (op k)) (c.w (𝟙 (op k))) (C k)
  · intro r m n hnm hmr
    dsimp only [v]
    rw [allTransitions_comp T B C s r m n hnm hmr]
    exact restrictC_comp T _ _ _ _ _ _ _ _ _ _ _ _

/-- Sequential derived realization preserving all varying coefficient actions, an arbitrary
prescribed first representative, actual complex evaluations, and every derived transition.
Source: blueprint main-20261015 lem-coef-integral-compact-support proof paragraph 2;
Stacks 05RT, 04VI, 03DA, 02MZ, 015F
(blueprint: lem-coef-sequential-varying-ring-realization).

Proof: restriction changes only the action on the underlying abelian sheaf; its exact
localization has the canonical unit and composition comparisons. Start with the prescribed
first pair. Given C_n, represent the next derived arrow by a right fraction in K(Mod B_{n+1})
with fixed target Res C_n, using the quasi-isomorphism multiplicative system (05RT) and
right-fraction representation (04VI). Choose chain representatives of numerator and
denominator; use their source as C_{n+1} and compose the denominator with the chosen
representative isomorphism. This proves the adjacent equation without changing earlier
choices. Recursion gives the sequence. Compose adjacent maps with the restriction
compositors to obtain all t_{m,n}; induction and the supplied cocycle prove their equations.
Restrict to R using the cone relations. The chain-map equations give natural differentials
on the actual inverse sequences, and their squares vanish levelwise. This constructs S
with exactly the displayed asFunctor, including its differentials. Levelwise abelianness
and exact evaluation (02MZ) descend through localization (015F). The cochain factorization
and the restricted i_n give evaluationIso. Compatibility of the exact restriction
compositor with these factorizations proves the final equation in the derived category.
There is no boundedness or invertibility assumption on the transitions. -/
theorem realization
    (M : ∀ n : ℕ, reductionDerivedCategory T (B.obj (op n)))
    (τ : ∀ (m n : ℕ) (h : n ≤ m), M m ⟶
      (reductionDerivedRestrict T (B.map (homOfLE h).op)).obj (M n))
    (hτid : ∀ n : ℕ, τ n n le_rfl ≫
      (Functor.mapDerivedCategoryNatIso
        (eqToIso (congrArg (reductionRestrict T) (B.map_id (op n))))).hom.app (M n) ≫
      (derivedId T (B.obj (op n))).hom.app (M n) = 𝟙 (M n))
    (hτcomp : ∀ (r m n : ℕ) (hnm : n ≤ m) (hmr : m ≤ r),
      τ r m hmr ≫ (reductionDerivedRestrict T (B.map (homOfLE hmr).op)).map
        (τ m n hnm) ≫
      (derivedComp T (B.map (homOfLE hmr).op) (B.map (homOfLE hnm).op)
        (B.map (homOfLE (hnm.trans hmr)).op)
        (B.map_comp (homOfLE hmr).op (homOfLE hnm).op).symm).hom.app (M n) =
      τ r n (hnm.trans hmr))
    (C₀ : CochainComplex (reductionModules T (B.obj (op 0))) ℤ)
    (i₀ : DerivedCategory.Q.obj C₀ ≅ M 0) :
    ∃ (C : ∀ n : ℕ, CochainComplex (reductionModules T (B.obj (op n))) ℤ)
      (i : ∀ n : ℕ, DerivedCategory.Q.obj (C n) ≅ M n)
      (t : ∀ (m n : ℕ) (h : n ≤ m), C m ⟶
        ((reductionRestrict T (B.map (homOfLE h).op)).mapHomologicalComplex (.up ℤ)).obj
          (C n)),
      C 0 = C₀ ∧ HEq (i 0) i₀ ∧
      (∀ n : ℕ, HEq (t n n le_rfl) (𝟙 (C n))) ∧
      (∀ (r m n : ℕ) (hnm : n ≤ m) (hmr : m ≤ r),
        t r n (hnm.trans hmr) = t r m hmr ≫
          ((reductionRestrict T (B.map (homOfLE hmr).op)).mapHomologicalComplex (.up ℤ)).map
            (t m n hnm) ≫
          (Functor.mapHomologicalComplexCompIso
            (restrictionComp T (B.map (homOfLE hmr).op) (B.map (homOfLE hnm).op)
              (B.map (homOfLE (hnm.trans hmr)).op)
              (B.map_comp (homOfLE hmr).op (homOfLE hnm).op).symm) (.up ℤ)).hom.app
                (C n)) ∧
      (∀ (m n : ℕ) (h : n ≤ m),
        DerivedCategory.Q.map (t m n h) ≫
          (reductionRestrict T (B.map (homOfLE h).op)).mapDerivedCategoryFactors.inv.app
            (C n) ≫
          (reductionDerivedRestrict T (B.map (homOfLE h).op)).map (i n).hom =
        (i m).hom ≫ τ m n h) ∧
      ∃ (S : CochainComplex (reductionTowerCategory T (reductionModuleRing T c.pt)) ℤ)
        (hS : S.asFunctor = restrictedTower T B c C t),
        ∀ (m n : ℕ) (h : n ≤ m),
          evaluatedTransition T B c S m n h ≫ (evaluationIso T B c M C i t S hS n).hom =
          (evaluationIso T B c M C i t S hS m).hom ≫
            (reductionDerivedRestrict T (c.π.app (op m))).map (τ m n h) ≫
            (derivedComp T (c.π.app (op m)) (B.map (homOfLE h).op)
              (c.π.app (op n)) (c.w (homOfLE h).op)).hom.app (M n)  := by
  obtain ⟨C, i, s, hC, hi, hs⟩ := adjacentRepresentatives T B M
    (fun n ↦ τ (n + 1) n (Nat.le_succ n)) C₀ i₀
  let t := allTransitions T B C s
  have ht := allTransitions_localize T B M τ hτid hτcomp C i s hs
  refine ⟨C, i, t, hC, hi, allTransitions_id T B C s,
    ?_, ht, ?_⟩
  · intro r m n hnm hmr
    simpa only [t, compC] using allTransitions_comp T B C s r m n hnm hmr
  let F := restrictedTower T B c C t
  refine ⟨transpose F, transpose_asFunctor F, ?_⟩
  intro m n h
  have hf := compC_localize_iso T (B.map (homOfLE h).op) (c.π.app (op m))
    (c.π.app (op n)) (c.w (homOfLE h).op)
    (𝟙 ((resC T (c.π.app (op m))).obj (C m))) (t m n h) (i n)
  simp only [compC] at hf
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hf
  change DerivedCategory.Q.map (restrictC T (c.π.app (op m))
      (B.map (homOfLE h).op) (c.π.app (op n)) (c.w (homOfLE h).op) (t m n h)) ≫
      (reductionRestrict T (c.π.app (op n))).mapDerivedCategoryFactors.inv.app (C n) ≫
      (reductionDerivedRestrict T (c.π.app (op n))).map (i n).hom = _ at hf
  rw [ht m n h] at hf
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hf
  dsimp only [evaluatedTransition, evaluationIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, CategoryTheory.Functor.mapIso_hom, eqToIso_refl,
    Iso.app_hom, Iso.app_inv, Iso.refl_hom]
  simp only [CategoryTheory.Functor.map_id, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [show (transpose F).asFunctor.map (homOfLE h).op =
    restrictC T (c.π.app (op m)) (B.map (homOfLE h).op) (c.π.app (op n))
      (c.w (homOfLE h).op) (t m n h) from restrictedTower_map T B c C s m n h]
  change
    (reductionTowerEvaluation T (reductionModuleRing T c.pt) m).mapDerivedCategoryFactors.hom.app
      (transpose F) ≫ DerivedCategory.Q.map (restrictC T (c.π.app (op m))
      (B.map (homOfLE h).op) (c.π.app (op n)) (c.w (homOfLE h).op) (t m n h)) ≫
      𝟙 _ ≫ (reductionRestrict T (c.π.app (op n))).mapDerivedCategoryFactors.inv.app (C n) ≫
      (reductionDerivedRestrict T (c.π.app (op n))).map (i n).hom =
    (reductionTowerEvaluation T (reductionModuleRing T c.pt) m).mapDerivedCategoryFactors.hom.app
      (transpose F) ≫ 𝟙 _ ≫
      (reductionRestrict T (c.π.app (op m))).mapDerivedCategoryFactors.inv.app (C m) ≫
      (reductionDerivedRestrict T (c.π.app (op m))).map (i m).hom ≫
      (reductionDerivedRestrict T (c.π.app (op m))).map (τ m n h) ≫
      (derivedComp T (c.π.app (op m)) (B.map (homOfLE h).op)
        (c.π.app (op n)) (c.w (homOfLE h).op)).hom.app (M n)
  simpa only [Category.assoc, Category.id_comp] using congrArg (fun f ↦
    (reductionTowerEvaluation T (reductionModuleRing T c.pt) m).mapDerivedCategoryFactors.hom.app
      (transpose F) ≫ f) hf

end AlgebraicGeometry.Scheme.SequentialVaryingRing
