/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.SmallIntegralFiniteQuotientTransport
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Transport of the strict small integral Roos augmentation

Source: Stacks Tag 08TC and the integral-heart completeness argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.IntegralConstantModel.pointComparison
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local instance] smallIntegralSheafMonoidal smallIntegralSheafClosed
  smallIntegralModulesMonoidal

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.modulesDerived
  AdicCompletion.modulesProducts AdicCompletion.complexProducts

private instance siteEssentiallySmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _


private def tensorComparison {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (G : C ⥤ D) [G.Monoidal]
    (B : C) (B' : D) (b : G.obj B ≅ B') :
    tensorRight B ⋙ G ≅ G ⋙ tensorRight B' :=
  NatIso.ofComponents
    (fun M ↦ (Functor.Monoidal.μIso G M B).symm ≪≫ whiskerLeftIso (G.obj M) b)
    (by
      intro M N f
      dsimp
      simp only [Functor.Monoidal.μIso_inv, whiskerLeftIso_hom]
      rw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
      simp only [Category.assoc]
      rw [whisker_exchange])

private theorem tensorComparison_unit
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (G : C ⥤ D) [G.Monoidal]
    (B : C) (B' : D) (b : G.obj B ≅ B') (a : 𝟙_ C ⟶ B) (a' : 𝟙_ D ⟶ B')
    (ha : G.map a ≫ b.hom = (Functor.Monoidal.εIso G).inv ≫ a') (M : C) :
    G.map ((ρ_ M).inv ≫ M ◁ a) ≫ (tensorComparison G B B' b).hom.app M =
      (ρ_ (G.obj M)).inv ≫ G.obj M ◁ a' := by
  simp only [Functor.Monoidal.εIso_inv] at ha
  simp only [tensorComparison, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Iso.symm_hom, Functor.Monoidal.μIso_inv, whiskerLeftIso_hom]
  rw [Functor.map_comp, Category.assoc,
    ← Functor.OplaxMonoidal.δ_natural_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp, ha, MonoidalCategory.whiskerLeft_comp,
    ← Functor.OplaxMonoidal.right_unitality_assoc]

private theorem tensorComparison_step
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (G : C ⥤ D) [G.Monoidal]
    (B₁ B₀ : C) (B₁' B₀' : D) (b₁ : G.obj B₁ ≅ B₁') (b₀ : G.obj B₀ ≅ B₀')
    (t : B₁ ⟶ B₀) (t' : B₁' ⟶ B₀')
    (ht : G.map t ≫ b₀.hom = b₁.hom ≫ t') (M : C) :
    G.map (M ◁ t) ≫ (tensorComparison G B₀ B₀' b₀).hom.app M =
      (tensorComparison G B₁ B₁' b₁).hom.app M ≫ G.obj M ◁ t' := by
  simp only [tensorComparison, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Iso.symm_hom, Functor.Monoidal.μIso_inv, whiskerLeftIso_hom]
  rw [← Functor.OplaxMonoidal.δ_natural_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp, ht, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]

private theorem mapLiftComparison {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (G : C ⥤ D) [G.Additive] {P V W : C} {V' W' : D}
    (c : G.obj (V ⊞ W) ⟶ V' ⊞ W') (q : G.obj V ⟶ V') (r : G.obj W ⟶ W')
    (hf : c ≫ biprod.fst = G.map biprod.fst ≫ q)
    (hs : c ≫ biprod.snd = G.map biprod.snd ≫ r)
    (a : P ⟶ V) (a' : G.obj P ⟶ V') (ha : G.map a ≫ q = a') :
    G.map (biprod.lift a (0 : P ⟶ W)) ≫ c = biprod.lift a' 0 := by
  apply biprod.hom_ext
  · rw [Category.assoc, hf, ← G.map_comp_assoc, biprod.lift_fst, ha, biprod.lift_fst]
  · rw [Category.assoc, hs, ← G.map_comp_assoc, biprod.lift_snd, G.map_zero,
      zero_comp, biprod.lift_snd]

set_option maxHeartbeats 800000 in
-- Compare products and both signed cone coordinates without unfolding coefficient rings.
/-- Scalar transport identifies the strict augmented Roos complexes. No completeness,
K-flatness, constructibility or cohomological bound is assumed.
Source: Stacks Tag 08TC; the finite quotient coefficient comparisons.
(blueprint: lem-sfb-small-integral-roos-comparison).
Proof: tensor the normalized finite module comparisons with each term of P using the
strong monoidal scalar equivalence. These chain isomorphisms preserve the tensor units
and transitions. Their product comparison intertwines 1-s. Apply the biproduct
comparison in degrees i and i-1: the two differentials are (dx,(1-s)x-dy), so the
diagonal comparison is a chain isomorphism. Its first augmentation coordinate is the
product of quotient units and its second coordinate is zero, giving the asserted
identity of chain maps. -/
theorem smallIntegralRoosComparison
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (F : Type u) [Field F] [Algebra (Padic ℓ) F] [FiniteDimensional (Padic ℓ) F]
    (e : Mon.mk (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E) ≅
      sfbCondensedIntegers ℓ F) (X : Scheme.{u})
    (P : CochainComplex (SmallAdicCompletion.Modules ℓ E X) ℤ) :
    let G := Mod.comap (coefficientMap (IntegralConstantModel.pointComparison ℓ F).hom.hom X ≫
      coefficientMap e.inv.hom X)
    let Gc := G.mapHomologicalComplex (.up ℤ)
    ∃ b : Gc.obj (SmallAdicCompletion.roos ℓ E X P) ≅
        AdicCompletion.roos ℓ F X (Gc.obj P),
      Gc.map (SmallAdicCompletion.augmentation ℓ E X P) ≫ b.hom =
        AdicCompletion.augmentation ℓ F X (Gc.obj P) := by
  let G : SmallAdicCompletion.Modules ℓ E X ⥤ AdicCompletion.Modules ℓ F X :=
    Mod.comap
    (coefficientMap (IntegralConstantModel.pointComparison ℓ F).hom.hom X ≫
      coefficientMap e.inv.hom X)
  have : G.IsEquivalence := (Mod.comapEquivalenceOfIsIso _).isEquivalence_functor
  have : PreservesBinaryBiproducts G :=
    preservesBinaryBiproducts_of_preservesBinaryProducts G
  let Gc := G.mapHomologicalComplex (.up ℤ)
  obtain ⟨b, hb, ht⟩ := smallIntegralFiniteQuotientTransport ℓ E F e X
  let a (n : ℕ) : Gc.obj ((SmallAdicCompletion.level ℓ E X n).obj P) ≅
      (AdicCompletion.level ℓ F X n).obj (Gc.obj P) :=
    (NatIso.mapHomologicalComplex
      (tensorComparison G _ _ (b n)) (.up ℤ)).app P
  have ha (n : ℕ) : Gc.map (SmallAdicCompletion.levelUnit ℓ E X P n) ≫ (a n).hom =
      AdicCompletion.levelUnit ℓ F X (Gc.obj P) n := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact tensorComparison_unit G _ _ (b n) _ _ (hb n) (P.X i)
  have hs (n : ℕ) : Gc.map (SmallAdicCompletion.levelStep ℓ E X P n) ≫ (a n).hom =
      (a (n + 1)).hom ≫ AdicCompletion.levelStep ℓ F X (Gc.obj P) n := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact tensorComparison_step G _ _ _ _ (b (n + 1)) (b n) _ _ (ht n) (P.X i)
  let V := SmallAdicCompletion.product ℓ E X P
  let W := AdicCompletion.product ℓ F X (Gc.obj P)
  let q : Gc.obj V ≅ W := PreservesProduct.iso Gc _ ≪≫
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by apply Pi.hom_ext; intro n; simp [Category.assoc]
      inv_hom_id := by apply Pi.hom_ext; intro n; simp [Category.assoc] }
  have hq (n : ℕ) : q.hom ≫ Pi.π _ n = Gc.map (Pi.π _ n) ≫ (a n).hom := by
    simp [q]
  have hunit : Gc.map (SmallAdicCompletion.unitProduct ℓ E X P) ≫ q.hom =
      AdicCompletion.unitProduct ℓ F X (Gc.obj P) := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, hq, ← Gc.map_comp_assoc, SmallAdicCompletion.unitProduct,
      Pi.lift_π, ha]
    exact (Pi.lift_π _ _).symm
  have hqa (n : ℕ) := reassoc_of% (hq n)
  have hshift : Gc.map (SmallAdicCompletion.oneSubShift ℓ E X P) ≫ q.hom =
      q.hom ≫ AdicCompletion.oneSubShift ℓ F X (Gc.obj P) := by
    apply Pi.hom_ext
    intro n
    simp only [SmallAdicCompletion.oneSubShift, AdicCompletion.oneSubShift,
      towerTransitionEndomorphism, Functor.map_sub,
      Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc]
    congr 1
    rw [hq, ← Gc.map_comp_assoc]
    simp only [towerProductShift, Pi.lift_π, Functor.map_comp,
      Category.assoc, hs, hqa]
  let c (i : ℤ) : (Gc.obj (SmallAdicCompletion.roos ℓ E X P)).X i ≅
      (AdicCompletion.roos ℓ F X (Gc.obj P)).X i :=
    G.mapBiprod (V.X i) (V.X (i - 1)) ≪≫
      biprod.mapIso (HomologicalComplex.Hom.isoApp q i) (HomologicalComplex.Hom.isoApp q (i - 1))
  have cfst (i : ℤ) : (c i).hom ≫ biprod.fst = G.map biprod.fst ≫ q.hom.f i := by
    simp [c, Category.assoc]; rfl
  have csnd (i : ℤ) : (c i).hom ≫ biprod.snd = G.map biprod.snd ≫ q.hom.f (i - 1) := by
    simp [c, Category.assoc]; rfl
  have cfsta (i : ℤ) := reassoc_of% (cfst i)
  have csnda (i : ℤ) := reassoc_of% (csnd i)
  have qcast (i j : ℤ) (h : i = j) :
      G.map (eqToHom (congrArg V.X h)) ≫ q.hom.f j =
        q.hom.f i ≫ eqToHom (congrArg W.X h) := by
    subst j
    simp
  have hc (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
      (c i).hom ≫ (AdicCompletion.roos ℓ F X (Gc.obj P)).d i j =
        (Gc.obj (SmallAdicCompletion.roos ℓ E X P)).d i j ≫ (c j).hom := by
    have hj : j = i + 1 := (show i + 1 = j from hij).symm
    subst j
    change (c i).hom ≫ (AdicCompletion.roos ℓ F X (Gc.obj P)).d i (i + 1) =
      G.map ((SmallAdicCompletion.roos ℓ E X P).d i (i + 1)) ≫ (c (i + 1)).hom
    simp only [AdicCompletion.roos, SmallAdicCompletion.roos, CochainComplex.of_d]
    apply biprod.hom_ext
    · simp only [Category.assoc, AdicCompletion.roosD, SmallAdicCompletion.roosD,
        biprod.lift_fst, cfst, cfsta]
      rw [← G.map_comp_assoc, biprod.lift_fst, G.map_comp, Category.assoc]
      exact congrArg (fun f ↦ G.map biprod.fst ≫ f) (q.hom.comm i (i + 1))
    · simp only [Category.assoc, AdicCompletion.roosD, SmallAdicCompletion.roosD,
        biprod.lift_snd, Preadditive.comp_sub,
        cfsta, csnd, csnda]
      rw [← G.map_comp_assoc, biprod.lift_snd, G.map_sub, Preadditive.sub_comp]
      simp only [Functor.map_comp, Category.assoc]
      have hh : G.map ((SmallAdicCompletion.oneSubShift ℓ E X P).f i) ≫ q.hom.f i =
          q.hom.f i ≫ (AdicCompletion.oneSubShift ℓ F X (Gc.obj P)).f i :=
        congrArg (fun f ↦ f.f i) hshift
      have h₁ :
          G.map (biprod.fst : V.X i ⊞ V.X (i - 1) ⟶ V.X i) ≫ q.hom.f i ≫
              (AdicCompletion.oneSubShift ℓ F X (Gc.obj P)).f i ≫
              eqToHom (congrArg W.X (Int.add_sub_cancel i 1).symm) =
            G.map biprod.fst ≫ G.map ((SmallAdicCompletion.oneSubShift ℓ E X P).f i) ≫
              G.map (eqToHom (congrArg V.X (Int.add_sub_cancel i 1).symm)) ≫
              q.hom.f (i + 1 - 1) := by
        rw [← reassoc_of% hh, ← qcast i (i + 1 - 1) (Int.add_sub_cancel i 1).symm]
      have h₂ := congrArg
        (fun f ↦ G.map (biprod.snd : V.X i ⊞ V.X (i - 1) ⟶ V.X (i - 1)) ≫ f)
        (q.hom.comm (i - 1) (i + 1 - 1))
      rw [h₁, h₂]
      rfl
  let d := HomologicalComplex.Hom.isoOfComponents c hc
  refine ⟨d, ?_⟩
  apply HomologicalComplex.Hom.ext
  funext i
  change G.map (biprod.lift ((SmallAdicCompletion.unitProduct ℓ E X P).f i)
      (0 : P.X i ⟶ V.X (i - 1))) ≫ (c i).hom =
    biprod.lift ((AdicCompletion.unitProduct ℓ F X (Gc.obj P)).f i)
      (0 : (Gc.obj P).X i ⟶ W.X (i - 1))
  exact mapLiftComparison G (c i).hom (q.hom.f i) (q.hom.f (i - 1))
    (cfst i) (csnd i) _ _ (congrArg (fun f ↦ f.f i) hunit)

end AlgebraicGeometry.ProEtale
