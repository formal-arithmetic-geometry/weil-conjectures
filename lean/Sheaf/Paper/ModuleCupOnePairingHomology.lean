/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.ModuleCupDerivedClassComparison
public import Sheaf.Paper.ModuleCupNaiveDerivedCompatibility

/-! # Homology formula for one realized resolution pairing

Source: Stacks Project, Section 20.31, Tags 0FKU and 0FKV.
(blueprint: new-module-cup-one-pairing-homology)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

@[instance_reducible] local instance cupSingleFormulaCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))

attribute [local instance] cupRealizationMonoidalCategory cupRealizationSymmetricCategory
  cupRealizationHasColimitsOfSize cupRealizationMonoidalPreadditive cupRealizationMonoidalClosed
  cupRealizationHasFunctorialFlatResolution cupRealizationIsGrothendieckAbelian
  cupRealizationDerivedMonoidal cupRealizationQLax

attribute [local irreducible] Functor.rightDerivedFunctor
  moduleCup_comparisonNatTrans

private theorem transport_pairing
    {Acat Bcat : Type*} [Category Acat] [Category Bcat]
    [MonoidalCategory Acat] [MonoidalCategory Bcat] (R : Acat ⥤ Bcat)
    (μ : ∀ A B : Acat, R.obj A ⊗ R.obj B ⟶ R.obj (A ⊗ B))
    (hμ : ∀ (A A' B B' : Acat) (f : A ⟶ A') (g : B ⟶ B'),
      (R.map f ⊗ₘ R.map g) ≫ μ A' B' = μ A B ≫ R.map (f ⊗ₘ g))
    {A A' B B' Z Z' : Acat} (a : A ⟶ A') (b : B ⟶ B') (c : Z ⟶ Z')
    [IsIso a] [IsIso b] [IsIso c] (δ : A' ⊗ B' ⟶ Z')
    {U V W : Bcat} (βU : U ⟶ R.obj A') (βV : V ⟶ R.obj B')
    (βW : W ⟶ R.obj Z') (τ : U ⊗ V ⟶ W)
    (hd : (βU ⊗ₘ βV) ≫ μ A' B' ≫ R.map δ = τ ≫ βW) :
    ((βU ≫ R.map (inv a)) ⊗ₘ (βV ≫ R.map (inv b))) ≫
        μ A B ≫ R.map ((a ⊗ₘ b) ≫ δ ≫ inv c) =
      τ ≫ βW ≫ R.map (inv c) := by
  rw [← tensorHom_comp_tensorHom, Category.assoc,
    ← Category.assoc (R.map (inv a) ⊗ₘ R.map (inv b)), hμ]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, tensorHom_comp_tensorHom,
    IsIso.inv_hom_id, IsIso.inv_hom_id, id_tensorHom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ R.map (inv c)) hd

private theorem localizedCycleClass_map {k : Type u} [CommRing k]
    [HasDerivedCategory.{u} (ModuleCat.{u} k)]
    {K L : CochainComplex (ModuleCat.{u} k) ℤ} (f : K ⟶ L) (n : ℤ)
    (z : K.cycles n) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).map (DerivedCategory.Q.map f)
        (cupLocalizedCycleClass K n z) =
      cupLocalizedCycleClass L n (HomologicalComplex.cyclesMap f n z) := by
  unfold cupLocalizedCycleClass
  have hn := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).inv.naturality f
  simp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at hn
  have hπ := congrArg (fun g ↦ g z) (HomologicalComplex.homologyπ_naturality f n)
  have hh := congrArg (fun g ↦ g (K.homologyπ n z)) hn
  simp only [ModuleCat.comp_apply] at hh hπ
  exact hh.symm.trans (congrArg
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).app L).inv hπ)

private theorem evaluate_pairing {k : Type u} [CommRing k]
    [HasDerivedCategory.{u} (ModuleCat.{u} k)] (P : CupDerivedHomologyTensor k)
    {A A' B B' W N N' : DerivedCategory (ModuleCat.{u} k)}
    (α : A ⟶ A') (β : B ⟶ B') (δ : A ⊗ B ⟶ W) (f : W ⟶ N) (γ : N ⟶ N')
    (σ : A' ⊗ B' ⟶ N') (hd : (α ⊗ₘ β) ≫ σ = δ ≫ f ≫ γ) (p q : ℕ)
    (a : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) p).obj A)
    (b : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) q).obj B)
    (a' : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) p).obj A')
    (b' : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) q).obj B')
    (w : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p + q : ℕ)).obj W)
    (c : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p + q : ℕ)).obj N)
    (c' : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p + q : ℕ)).obj N')
    (ha : a' = (DerivedCategory.homologyFunctor (ModuleCat.{u} k) p).map α a)
    (hb : b' = (DerivedCategory.homologyFunctor (ModuleCat.{u} k) q).map β b)
    (hw : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p + q : ℕ)).map δ
      (P.pair A B p q a b) = w)
    (hc : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p + q : ℕ)).map f w = c)
    (hc' : c' = (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p + q : ℕ)).map γ c) :
    c' = (DerivedCategory.homologyFunctor (ModuleCat.{u} k) (p + q : ℕ)).map σ
      (P.pair A' B' p q a' b') := by
  rw [ha, hb, P.natural, ← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp, hd]
  simp only [CategoryTheory.Functor.map_comp, ModuleCat.comp_apply]
  rw [hw, hc]
  exact hc'

set_option maxHeartbeats 1000000 in
-- Matching the sheaf tensor instances needs extra definitional equality work.
/-- A realized pairing evaluates to the derived tensor of its input classes.
Source: Stacks Project, Tag 0FKU, global diagram following Lemma 20.31.3.
(blueprint: new-module-cup-one-pairing-homology)
Proof: use C.on_cycles to lift the three nonnegative cycles to the extended
integer complexes. The two input lifts give a tensor cycle by P.on_cycles.
The summand formula for ν and ht identify its image under ν followed by global
t with the output lift, since extendXIso is invertible and iCycles is monic.
Naturality of the homology factorization of Q therefore identifies the localized
output class with homology of Q(ν followed by global t) on this tensor class.
Postcompose hdiagram with R(Q(t)) and R(inv target augmentation). Naturality
of the comparison unit moves Q(t) across the diagram. Naturality hμ moves the
inverse input augmentations across μ. The definition of D.derivedMap cancels
these inverse augmentations against the input augmentations. Apply homology
and P.natural to obtain the displayed identity, using C.on_cycles for all
three class identifications. This argument works in degree zero and for zero
cycles and zero modules, and requires no flatness of the resolution complexes. -/
theorem moduleCup_one_pairing_homology
    (C : CupDerivedClassComparison X) (P : CupDerivedHomologyTensor Γ(X, ⊤))
    (μ : ∀ A B : DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj A ⊗
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj B ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj (A ⊗ B))
    (hμ : ∀ (A A' B B' : DerivedCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))) (f : A ⟶ A') (g : B ⟶ B'),
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map f ⊗ₘ
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map g) ≫
        μ A' B' = μ A B ≫
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map (f ⊗ₘ g))
    {F G : X.Modules} (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex)
    (ht : D.Realizes t)
    (ν : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj D.left.integerComplex ⊗
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj D.right.integerComplex ⟶
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (D.left.integerComplex ⊗ D.right.integerComplex))
    (hν : ∀ (i j n : ℤ) (h : i + j = n)
      (x : Γ(D.left.integerComplex.X i, ⊤)) (y : Γ(D.right.integerComplex.X j, ⊤)),
      (ν.f n).hom
        ((HomologicalComplex.ιTensorObj
          (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj D.left.integerComplex)
          (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj D.right.integerComplex) i j n h).hom
          (TensorProduct.tmul Γ(X, ⊤) x y)) =
        (HomologicalComplex.ιTensorObj D.left.integerComplex D.right.integerComplex
          i j n h).val.app (op ⊤) (tmulSection x y))
    (hdiagram :
        (moduleCup_globalComparison X D.left.integerComplex ⊗ₘ
        moduleCup_globalComparison X D.right.integerComplex) ≫
          μ (DerivedCategory.Q.obj D.left.integerComplex)
            (DerivedCategory.Q.obj D.right.integerComplex) ≫
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map
            (Functor.LaxMonoidal.μ DerivedCategory.Q
              D.left.integerComplex D.right.integerComplex) =
      Functor.LaxMonoidal.μ DerivedCategory.Q
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj D.left.integerComplex)
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj D.right.integerComplex) ≫
        DerivedCategory.Q.map ν ≫
        moduleCup_globalComparison X (D.left.integerComplex ⊗ D.right.integerComplex))
    (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = D.pair p q ⊤ a.val b.val) :
    C.equiv (F ⊗ G) (p + q) (D.target.class (p + q) c) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) ((p + q : ℕ) : ℤ)).map
        (μ ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map
            (D.derivedMap t))
        (P.pair (cupDerivedSections X F) (cupDerivedSections X G) p q
          (C.equiv F p (D.left.class p a)) (C.equiv G q (D.right.class q b))) := by
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let T := S.mapHomologicalComplex (ComplexShape.up ℤ)
  let R := S.rightDerivedFunctor
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤))
    ((p + q : ℕ) : ℤ)
  let K := T.obj D.left.integerComplex
  let L := T.obj D.right.integerComplex
  let M := T.obj D.target.integerComplex
  obtain ⟨za, hza, hca⟩ := C.on_cycles D.left p a
  obtain ⟨zb, hzb, hcb⟩ := C.on_cycles D.right q b
  obtain ⟨zc, hzc, hcc⟩ := C.on_cycles D.target (p + q) c
  obtain ⟨z, hz, hp⟩ := P.on_cycles K L p q za zb
  have hcycle : HomologicalComplex.cyclesMap (ν ≫ T.map t) (p + q) z = zc := by
    clear C P μ hμ hdiagram hca hcb hcc hp
    have hza' : K.iCycles p za =
        (D.left.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op ⊤) a.val := by
      have hh := congrArg
        (S.map (D.left.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv) hza
      have hi := (S.mapIso
        (D.left.K.extendXIso ComplexShape.embeddingUpNat (by rfl))).hom_inv_id_apply
          (K.iCycles p za)
      exact hi.symm.trans hh
    have hzb' : L.iCycles q zb =
        (D.right.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv.val.app (op ⊤) b.val := by
      have hh := congrArg
        (S.map (D.right.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).inv) hzb
      have hi := (S.mapIso
        (D.right.K.extendXIso ComplexShape.embeddingUpNat (by rfl))).hom_inv_id_apply
          (L.iCycles q zb)
      exact hi.symm.trans hh
    apply (ModuleCat.mono_iff_injective (M.iCycles (p + q))).mp inferInstance
    apply (ModuleCat.mono_iff_injective
      (S.map (D.target.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom)).mp
        inferInstance
    change (S.map (D.target.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom)
      (M.iCycles (p + q) zc) = c.val at hzc
    erw [hzc, hc]
    have hi := congrArg (fun f ↦ f z)
      (HomologicalComplex.cyclesMap_i (ν ≫ T.map t) (p + q))
    simp only [ModuleCat.comp_apply] at hi
    erw [hi]
    change (S.map (D.target.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom)
      ((ν ≫ T.map t).f (p + q) ((K ⊗ L).iCycles (p + q) z)) = _
    erw [hz]
    change (S.map (D.target.K.extendXIso ComplexShape.embeddingUpNat (by rfl)).hom)
      ((T.map t).f (p + q) ((ν.f (p + q))
        ((HomologicalComplex.ιTensorObj K L p q (p + q) (by omega))
          (TensorProduct.tmul Γ(X, ⊤) (K.iCycles p za) (L.iCycles q zb))))) = _
    erw [hν, hza', hzb']
    exact ht p q ⊤ a.val b.val
  have htransport :
      ((moduleCup_globalComparison X D.left.integerComplex ≫
          R.map (inv D.left.derivedAugmentation)) ⊗ₘ
        (moduleCup_globalComparison X D.right.integerComplex ≫
          R.map (inv D.right.derivedAugmentation))) ≫
        μ ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫ R.map (D.derivedMap t) =
      Functor.LaxMonoidal.μ DerivedCategory.Q K L ≫
        DerivedCategory.Q.map (ν ≫ T.map t) ≫
          moduleCup_globalComparison X D.target.integerComplex ≫
            R.map (inv D.target.derivedAugmentation) := by
    have hn := (moduleCup_comparisonNatTrans X).naturality t
    change DerivedCategory.Q.map (T.map t) ≫ moduleCup_globalComparison X
        D.target.integerComplex =
      moduleCup_globalComparison X (D.left.integerComplex ⊗ D.right.integerComplex) ≫
        R.map (DerivedCategory.Q.map t) at hn
    have hd : (moduleCup_globalComparison X D.left.integerComplex ⊗ₘ
        moduleCup_globalComparison X D.right.integerComplex) ≫
        μ (DerivedCategory.Q.obj D.left.integerComplex)
          (DerivedCategory.Q.obj D.right.integerComplex) ≫
        R.map (Functor.LaxMonoidal.μ DerivedCategory.Q
          D.left.integerComplex D.right.integerComplex ≫ DerivedCategory.Q.map t) =
      (Functor.LaxMonoidal.μ DerivedCategory.Q K L ≫
        DerivedCategory.Q.map (ν ≫ T.map t)) ≫
          moduleCup_globalComparison X D.target.integerComplex := by
      calc
        _ = Functor.LaxMonoidal.μ DerivedCategory.Q K L ≫
            DerivedCategory.Q.map ν ≫
            moduleCup_globalComparison X (D.left.integerComplex ⊗ D.right.integerComplex) ≫
              R.map (DerivedCategory.Q.map t) := by
          simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using
            congrArg (fun f ↦ f ≫ R.map (DerivedCategory.Q.map t)) hdiagram
        _ = _ := by
          rw [← hn]
          simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    unfold CupResolutionPairing.derivedMap
    have hh :=
      (transport_pairing R μ hμ D.left.derivedAugmentation D.right.derivedAugmentation
        D.target.derivedAugmentation
        (Functor.LaxMonoidal.μ DerivedCategory.Q _ _ ≫ DerivedCategory.Q.map t)
        (moduleCup_globalComparison X D.left.integerComplex)
        (moduleCup_globalComparison X D.right.integerComplex)
        (moduleCup_globalComparison X D.target.integerComplex)
        (Functor.LaxMonoidal.μ DerivedCategory.Q K L ≫
          DerivedCategory.Q.map (ν ≫ T.map t)) hd)
    simp only [Category.assoc] at hh
    with_unfolding_all exact hh
  let α := moduleCup_globalComparison X D.left.integerComplex ≫
    R.map (inv D.left.derivedAugmentation)
  let β := moduleCup_globalComparison X D.right.integerComplex ≫
    R.map (inv D.right.derivedAugmentation)
  let γ := moduleCup_globalComparison X D.target.integerComplex ≫
    R.map (inv D.target.derivedAugmentation)
  let σ := μ ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫ R.map (D.derivedMap t)
  have hd : (α ⊗ₘ β) ≫ σ = Functor.LaxMonoidal.μ DerivedCategory.Q K L ≫
      DerivedCategory.Q.map (ν ≫ T.map t) ≫ γ := by
    simpa only [α, β, γ, σ, Category.assoc] using htransport
  have hout : H.map (DerivedCategory.Q.map (ν ≫ T.map t))
      (cupLocalizedCycleClass (K ⊗ L) (p + q) z) =
      cupLocalizedCycleClass M (p + q) zc :=
    (localizedCycleClass_map (ν ≫ T.map t) (p + q) z).trans
      (congrArg (cupLocalizedCycleClass M (p + q)) hcycle)
  exact evaluate_pairing P α β (Functor.LaxMonoidal.μ DerivedCategory.Q K L)
    (DerivedCategory.Q.map (ν ≫ T.map t)) γ σ hd p q
    (cupLocalizedCycleClass K p za) (cupLocalizedCycleClass L q zb)
    (C.equiv F p (D.left.class p a)) (C.equiv G q (D.right.class q b))
    (cupLocalizedCycleClass (K ⊗ L) (p + q) z) (cupLocalizedCycleClass M (p + q) zc)
    (C.equiv (F ⊗ G) (p + q) (D.target.class (p + q) c)) hca hcb hp hout hcc

end
end AlgebraicGeometry.Scheme.Modules
