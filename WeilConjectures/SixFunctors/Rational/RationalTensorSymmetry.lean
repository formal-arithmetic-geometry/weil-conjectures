/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Rational.RationalVerdier
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import all WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import all WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorBraiding
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.SmoothPurity.Integral.IntegralBraidingNaturality
import WeilConjectures.SixFunctors.Supporting.Tensor.LocalizedTensorBraidingNaturality

/-! # Naturality and involutivity of the recorded rational Koszul symmetry

Source: blueprint lem-coef-rational-retract-evaluation, proof paragraph 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] WeilConjectures.rationalDerivedTensor
  WeilConjectures.pullbackTensorRationalBraiding

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open scoped MonoidalCategory

section CoherentSymmetry
attribute [local implicit_reducible] Functor.map₂HomologicalComplex coefficientTotalTensor
attribute [local irreducible] CochainComplex.Monoidal.braiding
  SheafOfModules.monoidalCategory PresheafOfModules.sheafificationAdjunction
  SheafOfModules.tensorObjIsoSheafification
attribute [local irreducible] pullbackTensorBraiding CoefficientTensorModels.iso
  pullbackTensorSignedTotal
variable {C : Type (u + 1)} [Category.{u} C]
  (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (A : Sheaf J CommRingCat.{u + 1})

attribute [local instance] pullbackTensorMonoidal pullbackTensorSymmetric
  pullbackTensorZero pullbackTensorZeroObj
attribute [local instance 4000] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory

private theorem conjugatedBraiding_involutive
    {B : Type*} [Category* B] [MonoidalCategory B] [BraidedCategory B]
    (T : B × B ⥤ B) (e : ∀ X, T.obj X ≅ X.1 ⊗ X.2)
    (he : ∀ {X Y} (f : X ⟶ Y),
      T.map f ≫ (e Y).hom = (e X).hom ≫ (f.1 ⊗ₘ f.2))
    (hs : ∀ X Y : B, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _)
    (P Q : B) :
    (pullbackTensorGenericIso T e he).hom.app (P, Q) ≫
      (pullbackTensorGenericIso T e he).hom.app (Q, P) = 𝟙 _ := by
  dsimp only [pullbackTensorGenericIso, Iso.trans_hom, NatTrans.comp_app,
    NatIso.ofComponents_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, NatIso.ofComponents_inv_app,
    pullbackTensorSwap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (β_ P Q).hom, hs, Category.id_comp, Iso.hom_inv_id]

private theorem signedTotal_involutive
    (P Q : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ℤ) :
    (pullbackTensorSignedTotal J A P Q).hom ≫
      (pullbackTensorSignedTotal J A Q P).hom = 𝟙 _ := by
  rw [pullbackTensorSignedTotal_eq, pullbackTensorSignedTotal_eq]
  unfold pullbackTensorNative pullbackTensorNativeIso
  exact conjugatedBraiding_involutive _ _ (by
    intro X Y f
    dsimp only [Iso.refl_hom]
    erw [Category.comp_id, Category.id_comp]
    exact pullbackTensorTotal_map J A f.1 f.2)
    (fun P Q ↦ CategoryTheory.RingedDerivedNative.complex_symmetry P Q) P Q

private theorem reverse_square {B : Type*} [Category* B]
    {A A' U U' : B} (f : A ⟶ A') (g : A' ⟶ A)
    (hfg : f ≫ g = 𝟙 A) (a : A ⟶ U) (b : A' ⟶ U') (e : U' ≅ U)
    (h : g ≫ a = b ≫ e.hom) : f ≫ b = a ≫ e.inv := by
  apply (cancel_mono e.hom).1
  rw [Category.assoc, ← h, ← Category.assoc, hfg, Category.id_comp,
    Category.assoc, e.inv_hom_id, Category.comp_id]

variable [EssentiallySmall.{u + 1} C]
  [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u + 1, u, u, u + 2} J A))
  (T : CoefficientTensorModels.{u, u + 1, u, u + 2} J A S)

private theorem coherentBraiding_involutive (M N : DerivedCategory (SheafOfModules.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))) :
    (pullbackTensorBraiding J A S T).hom.app (M, N) ≫
      (pullbackTensorBraiding J A S T).hom.app (N, M) = 𝟙 _ := by
  unfold pullbackTensorBraiding
  let β := (pullbackTensorBraiding_existsUnique J A S T).exists.choose
  let e : S.tensor ≅ pullbackTensorSwap _ ⋙ S.tensor :=
    Functor.isoWhiskerLeft (pullbackTensorSwap _) β.symm
  have he : ∀ P Q hP hQ,
      DerivedCategory.Q.map (pullbackTensorSignedTotal J A P Q).hom ≫
        (CoefficientTensorModels.iso J A S T Q P hQ hP).hom =
      (CoefficientTensorModels.iso J A S T P Q hP hQ).hom ≫
        e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
    intro P Q hP hQ
    change _ = _ ≫ β.inv.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P)
    have hb := (pullbackTensorBraiding_existsUnique J A S T).exists.choose_spec Q P hQ hP
    exact reverse_square _ _
      (by rw [← Functor.map_comp, signedTotal_involutive, CategoryTheory.Functor.map_id]) _ _
      (β.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P)) hb
  have h := (pullbackTensorBraiding_existsUnique J A S T).unique
    (pullbackTensorBraiding_existsUnique J A S T).exists.choose_spec he
  have hh := congrArg (fun i ↦ i.hom.app (N, M)) h
  change β.hom.app (N, M) = β.inv.app (M, N) at hh
  rw [hh]
  exact β.hom_inv_id_app (M, N)

end CoherentSymmetry

section IntegralSymmetry
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]

attribute [local irreducible] pullbackTensorIntegralBraiding
  pullbackTensorIntegralReductionTensor

private theorem reflected_involution
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) [F.Faithful]
    {A B : C} {U V : D} (a : F.obj A ≅ U) (b : F.obj B ≅ V)
    (f : A ⟶ B) (g : B ⟶ A) (s : U ⟶ V) (t : V ⟶ U)
    (hf : F.map f ≫ b.hom = a.hom ≫ s)
    (hg : F.map g ≫ a.hom = b.hom ≫ t)
    (hst : s ≫ t = 𝟙 U) : f ≫ g = 𝟙 A := by
  apply F.map_injective
  apply (cancel_mono a.hom).1
  rw [Functor.map_comp, CategoryTheory.Functor.map_id, Category.assoc, hg,
    ← Category.assoc, hf, Category.assoc, hst, Category.comp_id, Category.id_comp]

private theorem integralBraiding_involutive
    (M N : sfIntegralConstructibleCategory l E W) :
    (pullbackTensorIntegralBraiding l E W M N).hom ≫
      (pullbackTensorIntegralBraiding l E W N M).hom = 𝟙 _ := by
  have := (coherentReduction_fullyFaithful l E W).2
  exact reflected_involution (coherentReduction l E W)
    (A := (constructibleIntegralTensor l E W).obj (M, N))
    (B := (constructibleIntegralTensor l E W).obj (N, M))
    (pullbackTensorIntegralReductionTensor l E W M N)
    (pullbackTensorIntegralReductionTensor l E W N M)
    (pullbackTensorIntegralBraiding l E W M N).hom
    (pullbackTensorIntegralBraiding l E W N M).hom _ _
    (by
      unfold pullbackTensorIntegralBraiding
      exact (pullbackTensorIntegralBraiding_existsUnique l E W M N).exists.choose_spec)
    (by
      unfold pullbackTensorIntegralBraiding
      exact (pullbackTensorIntegralBraiding_existsUnique l E W N M).exists.choose_spec)
    (coherentBraiding_involutive _ _ _ _ _ _)

private theorem transported_involution
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B : C} {U V : D} (hU : U = F.obj A) (hV : V = F.obj B)
    (f : A ⟶ B) (g : B ⟶ A) (s : U ⟶ V) (t : V ⟶ U)
    (hs : HEq s (F.map f)) (ht : HEq t (F.map g))
    (hfg : f ≫ g = 𝟙 A) : s ≫ t = 𝟙 U := by
  subst U V
  cases hs
  cases ht
  rw [← Functor.map_comp, hfg, CategoryTheory.Functor.map_id]

private theorem rationalBraiding_involutive
    (M N : sfRationalConstructibleCategory l E W) :
    (pullbackTensorRationalBraiding l E W M N).hom ≫
      (pullbackTensorRationalBraiding l E W N M).hom = 𝟙 _ := by
  exact transported_involution (sfRationalConstructibleLocalization l E W)
    (by
      unfold rationalDerivedTensor
      exact (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 (M, N))
    (by
      unfold rationalDerivedTensor
      exact (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 (N, M))
    (pullbackTensorIntegralBraiding l E W M.obj N.obj).hom
    (pullbackTensorIntegralBraiding l E W N.obj M.obj).hom
    (pullbackTensorRationalBraiding l E W M N).hom
    (pullbackTensorRationalBraiding l E W N M).hom
    (by
      unfold pullbackTensorRationalBraiding
      exact (pullbackTensorRationalBraiding_existsUnique l E W M N).exists.choose_spec)
    (by
      unfold pullbackTensorRationalBraiding
      exact (pullbackTensorRationalBraiding_existsUnique l E W N M).exists.choose_spec)
    (integralBraiding_involutive l E W M.obj N.obj)

end IntegralSymmetry

/-- The specified rational signed swap is natural and its opposite swap is inverse.
Source: blueprint lem-coef-rational-retract-evaluation, paragraph 2, and
lem-pur-derived-pullback-tensor-iso's signed total-tensor normalization
(blueprint: lem-coef-rational-tensor-symmetry-laws).

Proof: in the coherent reduction category the swap on degrees r,s sends
x tensor y to (-1)^(r*s) y tensor x. This commutes with both input maps;
the composite of the two swaps is identity since (-1)^(2*r*s)=1.
The tensor/reduction comparisons conjugate these two equations to the
completed integral tensor. Reduction is faithful on the complete inputs,
so the equations hold integrally. The rational tensor and swap are the
specified scalar localizations of these maps. Naturality for pure tensors
is the integral equation multiplied by their two scalars, and extends to
arbitrary arrows by bilinearity. Localizing the integral inverse equation
proves the last identity, including zero objects. -/
theorem rationalTensorSymmetry_laws
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (∀ (K L P Q : sfRationalConstructibleCategory l E X) (i : P ⟶ K) (j : Q ⟶ L),
      (@pullbackTensorRationalBraiding l _ E _ _ _ X
        (RationalVerdier.units D l hl X) Q P).hom ≫
          (RationalVerdier.tensor D l hl X E).map (Prod.mkHom i j) =
      (RationalVerdier.tensor D l hl X E).map (Prod.mkHom j i) ≫
        (@pullbackTensorRationalBraiding l _ E _ _ _ X
          (RationalVerdier.units D l hl X) L K).hom) ∧
    (∀ K L : sfRationalConstructibleCategory l E X,
      (@pullbackTensorRationalBraiding l _ E _ _ _ X
        (RationalVerdier.units D l hl X) K L).hom ≫
      (@pullbackTensorRationalBraiding l _ E _ _ _ X
        (RationalVerdier.units D l hl X) L K).hom = 𝟙 _) := by
  let := RationalVerdier.units D l hl X
  constructor
  · intro K L P Q i j
    exact (localizedTensorBraiding_naturality l E X
      (pullbackTensorIntegralBraiding_naturality l E X) Q L P K j i).symm
  · exact rationalBraiding_involutive l E X

end WeilConjectures
