/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.ModuleCupDerivedClassComparison
public import Sheaf.Paper.ModuleCupNaiveDerivedCompatibility
public import Sheaf.Paper.ModuleCupDerivedHomologyTensor
import Sheaf.Paper.ModuleCupTensorCycleImage
import Sheaf.Paper.ModuleCupComparisonDiagram

/-! # Evaluating one realized pairing in derived homology

Source: Stacks Project, Section 20.31, Tags 0FKU and 0FKV.
(blueprint: lem-sc-module-cup-single-pairing-homology)
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

attribute [local instance] cupRealizationMonoidalCategory cupRealizationSymmetricCategory
  cupRealizationHasColimitsOfSize cupRealizationMonoidalPreadditive cupRealizationMonoidalClosed
  cupRealizationHasFunctorialFlatResolution cupRealizationIsGrothendieckAbelian
  cupRealizationDerivedMonoidal cupRealizationQLax

local instance : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))

attribute [local irreducible] Functor.rightDerivedFunctor moduleCup_globalComparison

private theorem localizedCycle_natural {k : Type u} [CommRing k]
    [HasDerivedCategory.{u} (ModuleCat.{u} k)]
    {K L : CochainComplex (ModuleCat.{u} k) ℤ} (f : K ⟶ L)
    (n : ℤ) (z : K.cycles n) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).map (DerivedCategory.Q.map f)
        (cupLocalizedCycleClass K n z) =
      cupLocalizedCycleClass L n (HomologicalComplex.cyclesMap f n z) := by
  have h := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).inv.naturality f
  change HomologicalComplex.homologyMap f n ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).app L).inv =
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).app K).inv ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).map
        (DerivedCategory.Q.map f) at h
  change (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).app K).inv ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).map
      (DerivedCategory.Q.map f)) (K.homologyπ n z) = _
  rw [← h]
  change (K.homologyπ n ≫ HomologicalComplex.homologyMap f n ≫
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} k) n).app L).inv) z = _
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  rfl



private theorem functor_evaluated_diagram {C : Type*} [Category C]
    {k : Type u} [Ring k] (H : C ⥤ ModuleCat.{u} k)
    {A B M N D : C} (u : A ⟶ B) (d : B ⟶ D) (m : A ⟶ M)
    (f : M ⟶ N) (w : N ⟶ D)
    (P : H.obj A) (a : H.obj B) (z : H.obj M) (c : H.obj N)
    (hm : u ≫ d = m ≫ f ≫ w) (ha : a = H.map u P)
    (hz : H.map m P = z) (hc : H.map f z = c) :
    H.map w c = H.map d a := by
  have h := congrArg (fun g ↦ H.map g P) hm
  simp only [Functor.map_comp, ModuleCat.comp_apply] at h
  rw [hz, hc] at h
  rw [ha]
  exact h.symm

private theorem derivedMap_formula {F G : X.Modules} (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex) :
    D.derivedMap t = (D.left.derivedAugmentation ⊗ₘ D.right.derivedAugmentation) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q D.left.integerComplex D.right.integerComplex ≫
      DerivedCategory.Q.map t ≫ inv D.target.derivedAugmentation := by
  rfl

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom DerivedCategory.singleFunctors
  HomotopyCategory.singleFunctors CochainComplex.singleFunctors

attribute [local irreducible] CupAcyclicResolution.class CupResolutionPairing.derivedMap
  RingedSpace.moduleCohomology cupLocalizedCycleClass

set_option maxHeartbeats 1000000 in
-- Explicit cycle witnesses compare several presentations of the module-sheaf category.
/-- A single realized pairing is evaluated by the tensor operation on derived
homology and the supplied global cup diagram.
Source: Stacks Project, Tag 0FKU, Lemma 20.31.3 and its global specialization.
(blueprint: lem-sc-module-cup-single-pairing-homology)
Proof: use J.on_cycles to extend the two input cycles and the output cycle to
integer degrees. Apply hdiagram to the two integer resolution complexes.
Postcompose it with RΓ(Q(t)) and RΓ(inv target.derivedAugmentation).
Naturality of the comparison moves Q(t) past the target comparison; hnatural
moves the two input augmentations across μ. Thus the bottom composite is
μ on the coefficient objects, followed by RΓ(D.derivedMap t).
Use V.natural for the input comparisons, and V.on_cycles for their localized
integer cycles. The section formula for ν and ht identify the image of the
tensor cycle with the extended output cycle: after extendXIso its component is
D.pair p q top a.val b.val, which equals c.val by hc. Injectivity of the cycle
inclusion gives equality of those cycles. Naturality of homologyπ and of the
homology factorization then identify the upper composite with J.equiv applied
to D.target.class. The input formulas from J.on_cycles identify the other
composite with the right side below. No comparison of two resolutions, equality
of input classes, or normalization of the derived morphism is assumed. The
argument also applies when p or q is zero, since extension by zero and the tensor
summand formula hold in those degrees without a predecessor. -/
theorem moduleCup_single_pairing_homology
    (V : CupDerivedHomologyTensor Γ(X, ⊤)) (J : CupDerivedClassComparison X)
    (μ : ∀ A B : DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)),
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj A ⊗
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj B ⟶
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj (A ⊗ B))
    (hnatural : ∀ (A A' B B' : DerivedCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) (f : A ⟶ A') (g : B ⟶ B'),
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map f ⊗ₘ
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map g) ≫
        μ A' B' = μ A B ≫
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map (f ⊗ₘ g))
    (hdiagram : ∀ K L : CochainComplex
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let R := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor
    ∃ ν : T.obj K ⊗ T.obj L ⟶ T.obj (K ⊗ L),
      (∀ (i j n : ℤ) (h : i + j = n) (x : Γ(K.X i, ⊤)) (y : Γ(L.X j, ⊤)),
        (ν.f n).hom
            ((HomologicalComplex.ιTensorObj (T.obj K) (T.obj L) i j n h).hom
              (TensorProduct.tmul Γ(X, ⊤) x y)) =
          (HomologicalComplex.ιTensorObj K L i j n h).val.app (op ⊤)
            (tmulSection x y)) ∧
      (moduleCup_globalComparison X K ⊗ₘ moduleCup_globalComparison X L) ≫
          μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
          R.map (Functor.LaxMonoidal.μ DerivedCategory.Q K L) =
        Functor.LaxMonoidal.μ DerivedCategory.Q (T.obj K) (T.obj L) ≫
          DerivedCategory.Q.map ν ≫ moduleCup_globalComparison X (K ⊗ L))
    {F G : X.Modules}
    (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex)
    (ht : D.Realizes t) (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = D.pair p q ⊤ a.val b.val) :
    J.equiv (F ⊗ G) (p + q) (D.target.class (p + q) c) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) ((p + q : ℕ) : ℤ)).map
        (μ ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map
            (D.derivedMap t))
        (V.pair (cupDerivedSections X F) (cupDerivedSections X G) p q
          (J.equiv F p (D.left.class p a)) (J.equiv G q (D.right.class q b))) := by
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let T : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ⥤
      CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℤ :=
    S.mapHomologicalComplex (ComplexShape.up ℤ)
  let R : DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u} Γ(X, ⊤)) := S.rightDerivedFunctor
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) ((p + q : ℕ) : ℤ)
  have hleft := J.on_cycles (F := F) D.left p a
  have hright := J.on_cycles (F := G) D.right q b
  have htarget := J.on_cycles (F := F ⊗ G) D.target (p + q) c
  let za := hleft.choose
  let zb := hright.choose
  let zc := htarget.choose
  have ha := hleft.choose_spec.1
  have hb := hright.choose_spec.1
  have hcc := htarget.choose_spec.1
  have hJa := hleft.choose_spec.2
  have hJb := hright.choose_spec.2
  have hJc := htarget.choose_spec.2
  have hglobal := hdiagram D.left.integerComplex D.right.integerComplex
  let ν := hglobal.choose
  have hν := hglobal.choose_spec.1
  have hdiag := hglobal.choose_spec.2
  have htensor := V.on_cycles
    (T.obj D.left.integerComplex) (T.obj D.right.integerComplex) p q za zb
  let z := htensor.choose
  have hz := htensor.choose_spec.1
  have hVz := htensor.choose_spec.2
  have hcycle := moduleCup_tensor_cycle_image D t ht p q a b c hc
    ν hν za zb zc ha hb hcc z hz
  have hlocal : H.map (DerivedCategory.Q.map (ν ≫ T.map t))
      (cupLocalizedCycleClass _ (p + q : ℕ) z) =
      cupLocalizedCycleClass (T.obj D.target.integerComplex) (p + q : ℕ) zc := by
    rw [localizedCycle_natural]
    exact congrArg (cupLocalizedCycleClass (T.obj D.target.integerComplex)
      (p + q : ℕ)) hcycle
  let u := moduleCup_globalComparison X D.left.integerComplex ≫
    R.map (inv D.left.derivedAugmentation)
  let v := moduleCup_globalComparison X D.right.integerComplex ≫
    R.map (inv D.right.derivedAugmentation)
  let w := moduleCup_globalComparison X D.target.integerComplex ≫
    R.map (inv D.target.derivedAugmentation)
  let d := μ ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
      R.map (D.derivedMap t)
  let P := V.pair (DerivedCategory.Q.obj (T.obj D.left.integerComplex))
    (DerivedCategory.Q.obj (T.obj D.right.integerComplex)) p q
      (cupLocalizedCycleClass _ p za) (cupLocalizedCycleClass _ q zb)
  have hmor : (u ⊗ₘ v) ≫ d =
      Functor.LaxMonoidal.μ DerivedCategory.Q
          (T.obj D.left.integerComplex) (T.obj D.right.integerComplex) ≫
        DerivedCategory.Q.map (ν ≫ T.map t) ≫ w := by
    exact moduleCup_comparison_diagram R DerivedCategory.Q μ hnatural
      D.left.derivedAugmentation D.right.derivedAugmentation
      (moduleCup_globalComparison X D.left.integerComplex)
      (moduleCup_globalComparison X D.right.integerComplex)
      (Functor.LaxMonoidal.μ DerivedCategory.Q
        D.left.integerComplex D.right.integerComplex)
      (DerivedCategory.Q.map t) (inv D.target.derivedAugmentation)
      (D.derivedMap t) (derivedMap_formula D t)
      (Functor.LaxMonoidal.μ DerivedCategory.Q
        (T.obj D.left.integerComplex) (T.obj D.right.integerComplex))
      ν (T.map t)
      (moduleCup_globalComparison X (D.left.integerComplex ⊗ D.right.integerComplex))
      (moduleCup_globalComparison X D.target.integerComplex) hdiag
      (by
        simpa only [moduleCup_globalComparison, Functor.comp_map] using
          (moduleCup_comparisonNatTrans X).naturality t)
  have hab := congrArg₂
    (fun a b ↦ V.pair (cupDerivedSections X F) (cupDerivedSections X G) p q a b)
    hJa hJb
  have hpair := V.natural _ _ _ _ u v p q
    (cupLocalizedCycleClass _ p za) (cupLocalizedCycleClass _ q zb)
  have hin := hab.trans hpair
  exact hJc.trans (functor_evaluated_diagram H (u ⊗ₘ v) d
    (Functor.LaxMonoidal.μ DerivedCategory.Q
      (T.obj D.left.integerComplex) (T.obj D.right.integerComplex))
    (DerivedCategory.Q.map (ν ≫ T.map t)) w P _ _ _ hmor hin hVz hlocal)

end
end AlgebraicGeometry.Scheme.Modules
