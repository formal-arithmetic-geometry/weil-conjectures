/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Derivations induce degree-one transformations on perfect complexes

Source: blueprint sk-lem-sf-determination, commutator construction, steps 6–10
(blueprint: lem-sf-perfect-derivation-transformation).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

private theorem exists_projective_connection (R : Type u) [CommRing R]
    (δ : R →+ R) (hδ : ∀ r s, δ (r * s) = δ r * s + r * δ s)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Projective R M] :
    ∃ nabla : M →+ M, ∀ r m, nabla (r • m) = δ r • m + r • nabla m := by
  obtain ⟨s, hs⟩ := Module.Projective.out (R := R) (P := M)
  let D : (M →₀ R) →+ (M →₀ R) := Finsupp.mapRange.addMonoidHom δ
  let p : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  refine ⟨p.toAddMonoidHom.comp (D.comp s.toAddMonoidHom), ?_⟩
  intro r m
  have hD : D (r • s m) = δ r • s m + r • D (s m) := by
    ext i
    simp [D, hδ]
  change p (D (s (r • m))) = δ r • m + r • p (D (s m))
  rw [map_smul, hD, map_add, map_smul, map_smul]
  simpa [p] using congrArg (fun t ↦ δ r • t + r • p (D (s m))) (hs m)

private def linearCommutator {R : Type u} [CommRing R] (δ : R →+ R)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (a : M →+ M) (b : N →+ N)
    (ha : ∀ r m, a (r • m) = δ r • m + r • a m)
    (hb : ∀ r m, b (r • m) = δ r • m + r • b m) : M ⟶ N :=
  ModuleCat.ofHom
    { toFun := fun m ↦ b (f.hom m) - f.hom (a m)
      map_add' := by intros; simp; abel
      map_smul' := by intros; simp [ha, hb, smul_sub] }

private def commutatorCochain {R : Type u} [CommRing R] (δ : R →+ R)
    (A : CochainComplex (ModuleCat.{u} R) ℤ) (nabla : ∀ i : ℤ, A.X i →+ A.X i)
    (hnabla : ∀ i r m, nabla i (r • m) = δ r • m + r • nabla i m) :
    CochainComplex.HomComplex.Cochain A A 1 :=
  CochainComplex.HomComplex.Cochain.mk fun p q _ ↦
    linearCommutator δ (A.d p q) (nabla p) (nabla q) (hnabla p) (hnabla q)

private theorem commutator_cocycle {R : Type u} [CommRing R] (δ : R →+ R)
    (A : CochainComplex (ModuleCat.{u} R) ℤ) (nabla : ∀ i : ℤ, A.X i →+ A.X i)
    (hnabla : ∀ i r m, nabla i (r • m) = δ r • m + r • nabla i m) :
    CochainComplex.HomComplex.δ 1 2 (commutatorCochain δ A nabla hnabla) = 0 := by
  ext p q hpq m
  rw [CochainComplex.HomComplex.δ_v 1 2 rfl _ p q hpq (p + 1) (p + 1)
    (by omega) rfl]
  have hz (x : A.X p) : (A.d (p + 1) q).hom ((A.d p (p + 1)).hom x) = 0 := by
    exact congrArg (fun f ↦ f.hom x) (A.d_comp_d p (p + 1) q)
  simp [commutatorCochain, linearCommutator, show Int.negOnePow 2 = 1 by decide, hz]

private def commutatorCocycle {R : Type u} [CommRing R] (δ : R →+ R)
    (A : CochainComplex (ModuleCat.{u} R) ℤ) (nabla : ∀ i : ℤ, A.X i →+ A.X i)
    (hnabla : ∀ i r m, nabla i (r • m) = δ r • m + r • nabla i m) :
    CochainComplex.HomComplex.Cocycle A A 1 :=
  CochainComplex.HomComplex.Cocycle.mk (commutatorCochain δ A nabla hnabla) 2 rfl
    (commutator_cocycle δ A nabla hnabla)

private def commutatorMap {R : Type u} [CommRing R] (δ : R →+ R)
    (A : CochainComplex (ModuleCat.{u} R) ℤ) (nabla : ∀ i : ℤ, A.X i →+ A.X i)
    (hnabla : ∀ i r m, nabla i (r • m) = δ r • m + r • nabla i m) : A ⟶ A⟦(1 : ℤ)⟧ :=
  CochainComplex.HomComplex.Cocycle.equivHomShift.symm (commutatorCocycle δ A nabla hnabla)

private theorem commutatorMap_formula {R : Type u} [CommRing R] (δ : R →+ R)
    (A : CochainComplex (ModuleCat.{u} R) ℤ) (nabla : ∀ i : ℤ, A.X i →+ A.X i)
    (hnabla : ∀ i r m, nabla i (r • m) = δ r • m + r • nabla i m)
    (i : ℤ) (m : A.X i) :
    (((commutatorMap δ A nabla hnabla).f i) ≫
      (A.shiftFunctorObjXIso (1 : ℤ) i (i + 1) rfl).hom).hom m =
        nabla (i + 1) ((A.d i (i + 1)).hom m) -
          (A.d i (i + 1)).hom (nabla i m) := by
  simp [commutatorMap, CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply,
    CochainComplex.HomComplex.Cocycle.rightShift,
    CochainComplex.HomComplex.Cochain.rightShift, commutatorCocycle,
    commutatorCochain, linearCommutator]

private def mapCommutator {R : Type u} [CommRing R] (δ : R →+ R)
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (g : A ⟶ B)
    (a : ∀ i : ℤ, A.X i →+ A.X i) (b : ∀ i : ℤ, B.X i →+ B.X i)
    (ha : ∀ i r m, a i (r • m) = δ r • m + r • a i m)
    (hb : ∀ i r m, b i (r • m) = δ r • m + r • b i m) :
    CochainComplex.HomComplex.Cochain A B 0 :=
  CochainComplex.HomComplex.Cochain.ofHoms fun i ↦
    linearCommutator δ (g.f i) (a i) (b i) (ha i) (hb i)

private theorem commutator_naturality_boundary {R : Type u} [CommRing R] (δ : R →+ R)
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (g : A ⟶ B)
    (a : ∀ i : ℤ, A.X i →+ A.X i) (b : ∀ i : ℤ, B.X i →+ B.X i)
    (ha : ∀ i r m, a i (r • m) = δ r • m + r • a i m)
    (hb : ∀ i r m, b i (r • m) = δ r • m + r • b i m) :
    CochainComplex.HomComplex.δ 0 1 (mapCommutator δ g a b ha hb) =
      ((commutatorCocycle δ A a ha).postcomp g :
        CochainComplex.HomComplex.Cochain A B 1) -
      ((commutatorCocycle δ B b hb).precomp g :
        CochainComplex.HomComplex.Cochain A B 1) := by
  ext p q hpq m
  rw [CochainComplex.HomComplex.δ_v 0 1 rfl _ p q hpq p q (by omega) (by omega)]
  have hg (x : A.X p) : (B.d p q).hom ((g.f p).hom x) =
      (g.f q).hom ((A.d p q).hom x) :=
    congrArg (fun f ↦ f.hom x) (g.comm p q)
  simp [mapCommutator, commutatorCocycle, commutatorCochain, linearCommutator,
    CochainComplex.HomComplex.Cocycle.postcomp,
    CochainComplex.HomComplex.Cocycle.precomp,
    hg,
    show Int.negOnePow 1 = -1 by decide]
  abel

private theorem commutator_naturality_homotopy {R : Type u} [CommRing R] (δ : R →+ R)
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (g : A ⟶ B)
    (a : ∀ i : ℤ, A.X i →+ A.X i) (b : ∀ i : ℤ, B.X i →+ B.X i)
    (ha : ∀ i r m, a i (r • m) = δ r • m + r • a i m)
    (hb : ∀ i r m, b i (r • m) = δ r • m + r • b i m) :
    (HomotopyCategory.quotient _ _).map (commutatorMap δ A a ha ≫ g⟦(1 : ℤ)⟧') =
      (HomotopyCategory.quotient _ _).map (g ≫ commutatorMap δ B b hb) := by
  open CochainComplex.HomComplex in
  have h : CohomologyClass.mk ((commutatorCocycle δ A a ha).postcomp g) =
      CohomologyClass.mk ((commutatorCocycle δ B b hb).precomp g) := by
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
    exact ⟨0, rfl, mapCommutator δ g a b ha hb,
      commutator_naturality_boundary δ g a b ha hb⟩
  open CochainComplex.HomComplex in
  have h' := congrArg (CohomologyClass.toHom (K := A) (L := B) (n := 1)) h
  simpa only [CochainComplex.HomComplex.CohomologyClass.toHom_mk,
    CochainComplex.HomComplex.Cocycle.equivHomShift_symm_postcomp,
    CochainComplex.HomComplex.Cocycle.equivHomShift_symm_precomp,
    commutatorMap] using h'

private noncomputable def derivedCommutator {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (δ : R →+ R)
    (A : CochainComplex (ModuleCat.{u} R) ℤ) (nabla : ∀ i : ℤ, A.X i →+ A.X i)
    (hnabla : ∀ i r m, nabla i (r • m) = δ r • m + r • nabla i m) :
    Q.obj A ⟶ (Q.obj A)⟦(1 : ℤ)⟧ :=
  Q.map (commutatorMap δ A nabla hnabla) ≫ (Q.commShiftIso (1 : ℤ)).hom.app A

private theorem derivedCommutator_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (δ : R →+ R)
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (bound : ℤ) (hbound : A.IsStrictlyLE bound)
    (hA : ∀ i, Module.Projective R (A.X i))
    (a : ∀ i : ℤ, A.X i →+ A.X i) (b : ∀ i : ℤ, B.X i →+ B.X i)
    (ha : ∀ i r m, a i (r • m) = δ r • m + r • a i m)
    (hb : ∀ i r m, b i (r • m) = δ r • m + r • b i m)
    (g : Q.obj A ⟶ Q.obj B) :
    g ≫ derivedCommutator δ B b hb =
      derivedCommutator δ A a ha ≫ g⟦(1 : ℤ)⟧' := by
  let := hbound
  let (i : ℤ) : Module.Projective R (A.X i) := hA i
  let (i : ℤ) : Projective (A.X i) := inferInstance
  let := CochainComplex.isKProjective_of_projective A bound
  obtain ⟨g, rfl⟩ := CochainComplex.IsKProjective.exists_Q_map_eq A B g
  have h := Q_map_eq_of_homotopy (ModuleCat.{u} R)
    (HomotopyCategory.homotopyOfEq _ _ (commutator_naturality_homotopy δ g a b ha hb))
  dsimp [derivedCommutator]
  simp only [Category.assoc]
  rw [← Q.commShiftIso_hom_naturality g (1 : ℤ)]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ f ≫ (Q.commShiftIso (1 : ℤ)).hom.app B) h.symm

/-- An additive derivation of a commutative ring defines a natural transformation from
inclusion of its perfect complexes to the shifted inclusion, with the commutator formula
for every bounded finite projective model and every connection.

Source: blueprint sk-lem-sf-determination, counterexample proof steps 6–10
(blueprint: lem-sf-perfect-derivation-transformation).

Proof: Split each projective term into a free module and apply the derivation to its
coordinates to obtain a connection. The commutator nablad-dnabla is linear by Leibniz and is a
chain map to the shift since d²=0. Changing a connection changes this chain map by a
homotopy. For a chain map g, the linear maps nablag-gnabla form a homotopy witnessing naturality
of the commutators. Bounded above projective complexes are K-projective, so the bijection
between their homotopy classes and derived morphisms transports these classes to all
perfect objects. Conjugation by a representing isomorphism defines the component on a
perfect object. Applying the preceding homotopy to a representative of the transition
isomorphism shows independence of model and connection, and applying it to a representative
of an arbitrary derived morphism proves naturality. -/
theorem exists_perfect_derivation_transformation (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (δ : R →+ R) (hδ : ∀ r s, δ (r * s) = δ r * s + r * δ s) :
    ∃ η : ObjectProperty.ι (IsPerfectRingComplex (R := R)) ⟶
        ObjectProperty.ι (IsPerfectRingComplex (R := R)) ⋙
          shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (1 : ℤ),
      ∀ (A : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ),
        A.IsStrictlyGE a → A.IsStrictlyLE b →
        (∀ i : ℤ, Module.Projective R (A.X i) ∧ Module.Finite R (A.X i)) →
        ∀ (nabla : ∀ i : ℤ, A.X i →+ A.X i),
          (∀ (i : ℤ) (r : R) (m : A.X i),
            nabla i (r • m) = δ r • m + r • nabla i m) →
          ∃ (hA : IsPerfectRingComplex (Q.obj A)) (f : A ⟶ A⟦(1 : ℤ)⟧),
            (∀ (i : ℤ) (m : A.X i),
              ((f.f i) ≫ (A.shiftFunctorObjXIso (1 : ℤ) i (i + 1) rfl).hom).hom m =
                nabla (i + 1) ((A.d i (i + 1)).hom m) -
                  (A.d i (i + 1)).hom (nabla i m)) ∧
            η.app ⟨Q.obj A, hA⟩ = Q.map f ≫ (Q.commShiftIso (1 : ℤ)).hom.app A := by
  classical
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} R)) := IsPerfectRingComplex
  choose A lo hi hge hle ht he using (fun X : P.FullSubcategory ↦ X.property)
  let e (X : P.FullSubcategory) : X.obj ≅ Q.obj (A X) := (he X).some
  have hc (X : P.FullSubcategory) (i : ℤ) :
      ∃ nabla : (A X).X i →+ (A X).X i,
        ∀ r m, nabla (r • m) = δ r • m + r • nabla m := by
    let := (ht X i).1
    exact exists_projective_connection R δ hδ ((A X).X i)
  choose nabla hnabla using hc
  let c (X : P.FullSubcategory) := derivedCommutator δ (A X) (nabla X) (hnabla X)
  let η : P.ι ⟶ P.ι ⋙ shiftFunctor _ (1 : ℤ) :=
    { app := fun X ↦ (e X).hom ≫ c X ≫ (e X).inv⟦(1 : ℤ)⟧'
      naturality := by
        intro X Y f
        have h := derivedCommutator_naturality δ (hi X) (hle X)
          (fun i ↦ (ht X i).1) (nabla X) (nabla Y) (hnabla X) (hnabla Y)
          ((e X).inv ≫ f.hom ≫ (e Y).hom)
        have h' := congrArg
          (fun g ↦ (e X).hom ≫ g ≫ (e Y).inv⟦(1 : ℤ)⟧') h
        simpa [c, Functor.map_comp, Category.assoc] using h' }
  refine ⟨η, ?_⟩
  intro B a b hBa hBb hB conn hconn
  let hperf : IsPerfectRingComplex (Q.obj B) := ⟨B, a, b, hBa, hBb, hB, ⟨Iso.refl _⟩⟩
  let X : P.FullSubcategory := ⟨Q.obj B, hperf⟩
  refine ⟨hperf, commutatorMap δ B conn hconn, commutatorMap_formula δ B conn hconn, ?_⟩
  have h := derivedCommutator_naturality δ (hi X) (hle X)
    (fun i ↦ (ht X i).1) (nabla X) conn (hnabla X) hconn (e X).inv
  have h' := congrArg (fun g ↦ (e X).hom ≫ g) h
  simpa [η, X, c, derivedCommutator, Category.assoc] using h'.symm

end DerivedCategory
