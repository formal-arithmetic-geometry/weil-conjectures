/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.ModuleCupShiftedUnitTensor
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory

/-! # Tensoring homology classes in the derived category of modules

Source: Stacks Project, Tags 0FKU and 068G.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {k : Type u} [CommRing k] [HasDerivedCategory.{u} (ModuleCat.{u} k)]

/-- The class of an integer-degree cycle, transported through the homology
factorization of localization. This uses only actual homology and an existing iso. -/
def cupLocalizedCycleClass (K : CochainComplex (ModuleCat.{u} k) ℤ) (n : ℤ)
    (z : K.cycles n) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj (DerivedCategory.Q.obj K) :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).app K).inv
    (K.homologyπ n z)

/-- The natural tensor of derived homology classes, normalized on cochain cycles.
This is an interface, rather than a choice of an unproved operation. -/
structure CupDerivedHomologyTensor (k : Type u) [CommRing k]
    [HasDerivedCategory.{u} (ModuleCat.{u} k)] where
  pair : ∀ (A B : DerivedCategory (ModuleCat.{u} k)) (p q : ℕ),
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p : ℤ)).obj A →ₗ[k]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (q : ℤ)).obj B →ₗ[k]
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) ((p + q : ℕ) : ℤ)).obj (A ⊗ B)
  natural : ∀ (A A' B B' : DerivedCategory (ModuleCat.{u} k))
    (f : A ⟶ A') (g : B ⟶ B') (p q : ℕ)
    (a : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p : ℤ)).obj A)
    (b : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (q : ℤ)).obj B),
    pair A' B' p q
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p : ℤ)).map f a)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (q : ℤ)).map g b) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) ((p + q : ℕ) : ℤ)).map (f ⊗ₘ g)
        (pair A B p q a b)
  on_cycles : ∀ (K L : CochainComplex (ModuleCat.{u} k) ℤ) (p q : ℕ)
    (a : K.cycles p) (b : L.cycles q),
    ∃ z : (K ⊗ L).cycles (p + q),
      (K ⊗ L).iCycles (p + q) z =
        (HomologicalComplex.ιTensorObj K L p q (p + q) (by omega))
          ((K.iCycles p a) ⊗ₜ[k] (L.iCycles q b)) ∧
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) ((p + q : ℕ) : ℤ)).map
          (Functor.LaxMonoidal.μ DerivedCategory.Q K L)
          (pair (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) p q
            (cupLocalizedCycleClass K p a) (cupLocalizedCycleClass L q b)) =
        cupLocalizedCycleClass (K ⊗ L) (p + q) z

omit [HasDerivedCategory.{u} (ModuleCat.{u} k)] in
private theorem cupCycle_single_map (K : CochainComplex (ModuleCat.{u} k) ℤ) (n : ℤ)
    (a : K.cycles n) :
    ∃ f : (HomologicalComplex.single (ModuleCat.{u} k) (ComplexShape.up ℤ) n).obj
        (ModuleCat.of k k) ⟶ K,
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
        (ModuleCat.of k k)).inv ≫ f.f n) (1 : k) = K.iCycles n a := by
  let φ : ModuleCat.of k k ⟶ K.X n :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton k (K.X n) (K.iCycles n a))
  have hφ (j : ℤ) (_hj : (ComplexShape.up ℤ).Rel n j) : φ ≫ K.d n j = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change K.d n j (r • K.iCycles n a) = 0
    rw [map_smul]
    have h : K.d n j (K.iCycles n a) = 0 := congr($(K.iCycles_d n j) a)
    rw [h, smul_zero]
  refine ⟨HomologicalComplex.mkHomFromSingle φ hφ, ?_⟩
  simp [φ]

omit [HasDerivedCategory.{u} (ModuleCat.{u} k)] in
private theorem cupSingle_map_cycle (K : CochainComplex (ModuleCat.{u} k) ℤ) (n : ℤ)
    (f : (HomologicalComplex.single (ModuleCat.{u} k) (ComplexShape.up ℤ) n).obj
      (ModuleCat.of k k) ⟶ K) :
    ∃ a : K.cycles n,
      K.iCycles n a = ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
        (ModuleCat.of k k)).inv ≫ f.f n) (1 : k) := by
  let φ := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
    (ModuleCat.of k k)).inv ≫ f.f n
  have hφ : φ ≫ K.d n (n + 1) = 0 := by
    dsimp [φ]
    rw [Category.assoc, f.comm]
    simp
  refine ⟨(K.liftCycles φ (n + 1) (by simp) hφ) (1 : k), ?_⟩
  exact congr($(K.liftCycles_i φ (n + 1) (by simp) hφ) (1 : k))

/-- Derived homology admits its natural bilinear tensor pairing.
Source: Stacks Project, Tag 0FKU, global cohomology diagram following Lemma 20.31.3;
Tag 068G, tensor product of cocycles.
(blueprint: lem-sc-module-cup-derived-homology-tensor)
Proof: represent a class in H^p(A) by a morphism k[-p] to A. The rank-one free
module k is projective, so the standard homology/Hom identification is bijective.
Tensor the two representing morphisms and use the canonical identification
k[-p-q] with k[-p] tensor k[-q]. Transport back to homology. Additivity and
k-linearity of tensor give a bilinear map; composition gives naturality.
For localized complexes, the two representing maps are the single-complex maps
whose components are the supplied cocycles. Their tensor, followed by the lax
localization comparison, has component the indicated tensor summand. The signed
Leibniz rule says that component is a cycle. Applying homology gives on_cycles.
The same argument includes degree zero, zero complexes and zero
cycles; projectivity is used for the rank-one source, never for K or L. -/
theorem exists_cupDerivedHomologyTensor : Nonempty (CupDerivedHomologyTensor k) := by
  classical
  obtain ⟨J⟩ := exists_cupHomologyRepresentability k
  have hE (p q n : ℤ) (hpq : p + q = n) :
    ∃ e : DerivedCategory.Q.obj (cupSingleModule k n) ≅
      DerivedCategory.Q.obj (cupSingleModule k p) ⊗
        DerivedCategory.Q.obj (cupSingleModule k q),
    ∀ (K L : CochainComplex (ModuleCat.{u} k) ℤ)
      (f : cupSingleModule k p ⟶ K) (g : cupSingleModule k q ⟶ L),
    ∃ h : cupSingleModule k n ⟶ K ⊗ L,
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n
          (ModuleCat.of k k)).inv ≫ h.f n) (1 : k) =
        (HomologicalComplex.ιTensorObj K L p q n hpq)
          ((((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p
              (ModuleCat.of k k)).inv ≫ f.f p) (1 : k)) ⊗ₜ[k]
            (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q
              (ModuleCat.of k k)).inv ≫ g.f q) (1 : k))) ∧
      e.hom ≫ (DerivedCategory.Q.map f ⊗ₘ DerivedCategory.Q.map g) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q K L = DerivedCategory.Q.map h := by
    subst n
    exact exists_cupShiftedUnitTensor k p q
  choose e he using fun (p q : ℕ) ↦ hE p q (p + q : ℕ) (by omega)
  let P (A B : DerivedCategory (ModuleCat.{u} k)) (p q : ℕ) :
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) p).obj A →ₗ[k]
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) q).obj B →ₗ[k]
          (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p + q : ℕ)).obj (A ⊗ B) :=
    { toFun := fun a ↦
        { toFun := fun b ↦ J.equiv (A ⊗ B) (p + q : ℕ)
            ((e p q).hom ≫ ((J.equiv A p).symm a ⊗ₘ (J.equiv B q).symm b))
          map_add' := by
            intros b b'
            simp only [map_add, MonoidalPreadditive.tensor_add, Preadditive.comp_add]
          map_smul' := by
            intros r b
            simp only [map_smul, RingHom.id_apply, tensorHom_def,
              MonoidalLinear.whiskerLeft_smul, Linear.comp_smul] }
      map_add' := by
        intros a a'
        ext b
        simp only [map_add, MonoidalPreadditive.add_tensor, Preadditive.comp_add]
        rfl
      map_smul' := by
        intros r a
        ext b
        simp only [map_smul, RingHom.id_apply, tensorHom_def,
          MonoidalLinear.smul_whiskerRight, Linear.comp_smul, Linear.smul_comp]
        rfl }
  have hPn (A A' B B' : DerivedCategory (ModuleCat.{u} k))
      (f : A ⟶ A') (g : B ⟶ B') (p q : ℕ)
      (a : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) p).obj A)
      (b : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) q).obj B) :
      P A' B' p q
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) p).map f a)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) q).map g b) =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p + q : ℕ)).map (f ⊗ₘ g)
          (P A B p q a b) := by
    have hf : (J.equiv A' p).symm
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) p).map f a) =
        (J.equiv A p).symm a ≫ f := by
      apply (J.equiv A' p).injective
      simp only [LinearEquiv.apply_symm_apply, J.natural]
    have hg : (J.equiv B' q).symm
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) q).map g b) =
        (J.equiv B q).symm b ≫ g := by
      apply (J.equiv B' q).injective
      simp only [LinearEquiv.apply_symm_apply, J.natural]
    dsimp only [P, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hf, hg, ← J.natural, ← tensorHom_comp_tensorHom, Category.assoc]
  have hPc (K L : CochainComplex (ModuleCat.{u} k) ℤ) (p q : ℕ)
      (a : K.cycles p) (b : L.cycles q) :
      ∃ z : (K ⊗ L).cycles (p + q : ℕ),
        (K ⊗ L).iCycles (p + q : ℕ) z =
          (HomologicalComplex.ιTensorObj K L p q (p + q : ℕ) (by omega))
            ((K.iCycles p a) ⊗ₜ[k] (L.iCycles q b)) ∧
        (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p + q : ℕ)).map
            (Functor.LaxMonoidal.μ DerivedCategory.Q K L)
            (P (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) p q
              (cupLocalizedCycleClass K p a) (cupLocalizedCycleClass L q b)) =
          cupLocalizedCycleClass (K ⊗ L) (p + q : ℕ) z := by
    obtain ⟨f, hf⟩ := cupCycle_single_map K p a
    obtain ⟨g, hg⟩ := cupCycle_single_map L q b
    obtain ⟨h, hh, hQ⟩ := he p q K L f g
    obtain ⟨z, hz⟩ := cupSingle_map_cycle (K ⊗ L) (p + q : ℕ) h
    refine ⟨z, ?_, ?_⟩
    · rw [hz, hh, hf, hg]
    · have hfa : (J.equiv (DerivedCategory.Q.obj K) p).symm
          (cupLocalizedCycleClass K p a) = DerivedCategory.Q.map f := by
        apply (J.equiv (DerivedCategory.Q.obj K) p).injective
        simpa only [LinearEquiv.apply_symm_apply, cupLocalizedCycleClass] using
          (J.on_cycles K p f a hf).symm
      have hgb : (J.equiv (DerivedCategory.Q.obj L) q).symm
          (cupLocalizedCycleClass L q b) = DerivedCategory.Q.map g := by
        apply (J.equiv (DerivedCategory.Q.obj L) q).injective
        simpa only [LinearEquiv.apply_symm_apply, cupLocalizedCycleClass] using
          (J.on_cycles L q g b hg).symm
      dsimp only [P, LinearMap.coe_mk, AddHom.coe_mk]
      rw [hfa, hgb, ← J.natural, Category.assoc, hQ]
      exact J.on_cycles (K ⊗ L) (p + q : ℕ) h z hz.symm
  exact ⟨{ pair := P, natural := hPn, on_cycles := hPc }⟩

end
end AlgebraicGeometry.Scheme.Modules
