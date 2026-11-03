/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.CategoryTheory.WeilEquivariance
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
public import WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
public import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFibreComparisons.CondensedFibreLinearComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFibreLinearOperationsLisseTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedLisseTensorOnNoetherian

/-! # Tensor and dual fibres of condensed Weil sheaves

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-a1/sec-purity-of-the-lisse-part-of-the-fourier-transform/
sk-p-dl-a1-some-weight/lem-fd-realified-kernel-real.proof.md, Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations).

All modules, point sections and local operators are the recorded condensed constructions.
The comparison maps are normalized by tensoring sections and evaluating functionals.
Finite direct sums are represented by finite products in the abelian module category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj TensorProduct

namespace WeilConjectures.CondensedFibreLinearCurrent

open NativeCondensedModule

/-- Tensor the two Weil data using the inverse pullback tensorator.
Source: latest blueprint, realified-kernel proof Step 2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
def tensorWeil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (g : T ≅ T)
    (F L : IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) :
    IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) :=
  IsoAlgebra.mk (F.carrier ⊗ L.carrier)
    ((Functor.Monoidal.μIso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) _ _).symm ≪≫
        tensorIso F.str L.str)

/-- The ordinary internal dual, with its evaluation-transpose contragredient datum.
Source: latest blueprint, realified-kernel proof Step 1, and the contragredient composite
of sk-def-sf-weil-complexes (blueprint: lem-fd-condensed-fibre-linear-operations). -/
def dualWeil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (g : T ≅ T)
    (L : IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) :
    IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) :=
  IsoAlgebra.mk ((ihom L.carrier).obj (𝟙_ (Modules l T)))
    (Functor.Monoidal.ihomObjIso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) L.carrier (𝟙_ _) ≪≫
      (ihom _).mapIso
        (Functor.Monoidal.εIso
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)).symm ≪≫
      (MonoidalClosed.internalHom.mapIso L.str.symm.op).app (𝟙_ _))

/-- A finite direct sum with the direct sum of the Weil data, using the finite product model.
Source: latest blueprint, realified-kernel proof Step 2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
def sumWeil (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (g : T ≅ T) (n : ℕ)
    (F : Fin n → IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) :
    IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom) :=
  IsoAlgebra.mk (∏ᶜ fun i ↦ (F i).carrier)
    (PreservesProduct.iso
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)
      (fun i ↦ (F i).carrier) ≪≫ Pi.mapIso (fun i ↦ (F i).str))

/-- The section obtained by tensoring two sections and applying the pullback tensorator.
Source: latest blueprint, realified-kernel proof Step 2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
def tensorSection (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) (F L : Modules l T)
    (v : fibre l D F z) (w : fibre l D L z) : fibre l D (F ⊗ L) z :=
  (λ_ (𝟙_ (Modules l (Spec (.of D.k))))).inv ≫ (v ⊗ₘ w) ≫
    Functor.LaxMonoidal.μ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z) F L

/-- Evaluation of a fibre functional on a fibre vector, with the coefficient-unit comparison.
Source: latest blueprint, realified-kernel proof Step 1
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
def evaluation (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) (L : Modules l T)
    (f : fibre l D ((ihom L).obj (𝟙_ (Modules l T))) z) (v : fibre l D L z) :
    ULift.{u + 1} (PadicAlgCl l) :=
  (NativeCondensedModule.pointSectionsUnitIso l D.k).inv
    ((NativeCondensedModule.pointSections l D.k).map
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map
        ((ihom.ev L).app (𝟙_ _)) ≫
        (Functor.Monoidal.εIso
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z)).inv)
      (tensorSection l D z L _ v f))

/-- Natural fibre comparisons, specified by tensoring sections and by evaluation.
Source: latest blueprint, realified-kernel proof Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
structure Comparisons (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k]
    {T : Scheme.{u}} (g : T ≅ T) (z : Spec (.of D.k) ⟶ T) where
  tensor : ∀ (F L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T F.carrier →
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T L.carrier →
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier →
    fibre l D (F.carrier ⊗ L.carrier) z ≃ₗ[ULift.{u + 1} (PadicAlgCl l)]
      (fibre l D F.carrier z ⊗[ULift.{u + 1} (PadicAlgCl l)] fibre l D L.carrier z)
  tensor_sections : ∀ (F L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hF hL hLis
      (v : fibre l D F.carrier z) (w : fibre l D L.carrier z),
    tensor F L hF hL hLis (tensorSection l D z F.carrier L.carrier v w) =
      TensorProduct.tmul (ULift.{u + 1} (PadicAlgCl l)) v w
  dual : ∀ (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T L.carrier →
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier →
    fibre l D ((ihom L.carrier).obj (𝟙_ (Modules l T))) z ≃ₗ[ULift.{u + 1} (PadicAlgCl l)]
      Module.Dual (ULift.{u + 1} (PadicAlgCl l)) (fibre l D L.carrier z)
  dual_evaluation : ∀ (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hL hLis f v,
    dual L hL hLis f v = evaluation l D z L.carrier f v
  tensor_natural : ∀ (F L F' L' : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hF hL hLis hF' hL' hLis'
      (f : F.carrier ⟶ F'.carrier) (a : L.carrier ⟶ L'.carrier)
      (v : fibre l D (F.carrier ⊗ L.carrier) z),
    tensor F' L' hF' hL' hLis'
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        NativeCondensedModule.pointSections l D.k).map (f ⊗ₘ a) v) =
      TensorProduct.map
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          NativeCondensedModule.pointSections l D.k).map f).hom
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          NativeCondensedModule.pointSections l D.k).map a).hom (tensor F L hF hL hLis v)
  dual_natural : ∀ (L L' : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hL hLis hL' hLis'
      (f : L.carrier ⟶ L'.carrier)
      (a : fibre l D ((ihom L'.carrier).obj (𝟙_ (Modules l T))) z) (v : fibre l D L.carrier z),
    dual L hL hLis
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        NativeCondensedModule.pointSections l D.k).map ((MonoidalClosed.pre f).app (𝟙_ _)) a) v =
      dual L' hL' hLis' a
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          NativeCondensedModule.pointSections l D.k).map f v)

/-- Frobenius under the specified comparisons, including the finite-sum projections.
Source: latest blueprint, realified-kernel proof Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
structure WeilCompatibility (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    [IsAlgClosed D.k] {T : Scheme.{u}} (g : T ≅ T) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower g.hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) (c : Comparisons l D g z) : Prop where
  tensor_frobenius : ∀ (F L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hF hL hLis
      (v : fibre l D (F.carrier ⊗ L.carrier) z),
    c.tensor F L hF hL hLis
      ((NativeCondensedModule.operator l D g.hom (F.carrier ⊗ L.carrier)
        (tensorWeil l g F L).str z n h).hom v) =
      TensorProduct.map (NativeCondensedModule.operator l D g.hom F.carrier F.str z n h).hom
        (NativeCondensedModule.operator l D g.hom L.carrier L.str z n h).hom
        (c.tensor F L hF hL hLis v)
  dual_frobenius : ∀ (L : IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)) hL hLis
      (f : fibre l D ((ihom L.carrier).obj (𝟙_ (Modules l T))) z)
      (v : fibre l D L.carrier z),
    c.dual L hL hLis
      ((NativeCondensedModule.operator l D g.hom ((ihom L.carrier).obj (𝟙_ (Modules l T)))
        (dualWeil l g L).str z n h).hom f) v =
      c.dual L hL hLis f
        ((NativeCondensedModule.transport l D g.hom L.carrier L.str z z n h).inv.hom v)
  sum_frobenius : ∀ (r : ℕ) (F : Fin r → IsoAlgebra
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g.hom)),
    (∀ i, IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T (F i).carrier) →
    IsIso (piComparison
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        NativeCondensedModule.pointSections l D.k) (fun i ↦ (F i).carrier)) ∧
    ∀ i : Fin r,
      NativeCondensedModule.operator l D g.hom (∏ᶜ fun i ↦ (F i).carrier)
        (sumWeil l g r F).str z n h ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          NativeCondensedModule.pointSections l D.k).map (Pi.π (fun j ↦ (F j).carrier) i) =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          NativeCondensedModule.pointSections l D.k).map (Pi.π (fun j ↦ (F j).carrier) i) ≫
        NativeCondensedModule.operator l D g.hom (F i).carrier (F i).str z n h

/-- All clauses of the fibre linear-operations lemma with the fixed condensed coefficients.
Source: latest blueprint, realified-kernel proof Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations). -/
def Assertions (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    [IsSeparated T₀.hom] : Prop :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  (∀ (L : IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius T₀).hom)),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left
      L.carrier →
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier →
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
      ((ihom L.carrier).obj (𝟙_ (Modules l (D.geometricFiber T₀).left)))) ∧
  (∀ (F L : IsoAlgebra (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius T₀).hom)),
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left
      F.carrier →
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left
      L.carrier →
    IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) L.carrier →
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) (D.geometricFiber T₀).left
      (F.carrier ⊗ L.carrier) ∧
      IsIso (CondensedRing.lisseTensorDerivedComparison F.carrier L.carrier)) ∧
  ∀ (x : {x : T₀.left // x ∈ closedPoints T₀.left})
      (ι : T₀.left.residueField x.val →+* D.k)
      (hι : ι.comp (T₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k),
    ∃ c : Comparisons l D (D.geometricFrobenius T₀) (localClosedPoint D T₀ x ι hι),
      WeilCompatibility l D (D.geometricFrobenius T₀) (localClosedPoint D T₀ x ι hι)
        (localClosedPointDegree D T₀ x - 1) (localClosedPoint_return D T₀ x ι hι) c

private theorem sections_map_apply (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    {M N : Modules l (Spec (.of k))} (f : M ⟶ N) (s : (pointSections l k).obj M) :
    (pointSections l k).map f s = s ≫ f := rfl

private theorem unitHom_apply (l : ℕ) [Fact l.Prime] (k : Type u)
    [Field k] [IsSepClosed k] (a : ULift.{u + 1} (PadicAlgCl l)) :
    (pointSectionsUnitIso l k).hom a = pointUnitEndRingHom l k a.down := by
  change pointUnitEndRingHom l k a.down ≫ 𝟙 _ = _
  exact Category.comp_id _

private theorem transport_normalized (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    transport l D a M θ z z n h =
      letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
      (pointSections l D.k).mapIso
        ((CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
          (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
            (localPositivePower (frobeniusPointIso D).hom n))
          (localPositivePower a n) h).app M ≪≫
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).mapIso
            (iterate l a M θ n)) := by
  rfl

private theorem initialNaturality {C : Type*} [Category C] (F G : C ⥤ C)
    (c : F ≅ G) {M N : C} (θM : G.obj M ≅ M) (θN : G.obj N ≅ N)
    (f : M ⟶ N) (hf : G.map f ≫ θN.hom = θM.hom ≫ f) :
    F.map f ≫ (evaluateInitial F G c N θN).hom =
      (evaluateInitial F G c M θM).hom ≫ f := by
  dsimp only [evaluateInitial, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, c.hom.naturality, Category.assoc, hf, Category.assoc]

private theorem stepNaturality {C : Type*} [Category C] (F G H : C ⥤ C)
    (c : H ≅ G ⋙ F) {M N : C} (θM : G.obj M ≅ M) (θN : G.obj N ≅ N)
    (f : M ⟶ N) (hf : G.map f ≫ θN.hom = θM.hom ≫ f) :
    H.map f ≫ (evaluateStep F G H c N θN).hom =
      (evaluateStep F G H c M θM).hom ≫ F.map f := by
  dsimp only [evaluateStep, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, c.hom.naturality, Functor.comp_map, Category.assoc,
    ← F.map_comp, hf, F.map_comp, Category.assoc]

private theorem returnNaturality {C E B : Type*} [Category C] [Category E] [Category B]
    (S : E ⥤ B) (Z : C ⥤ E) (A : C ⥤ C) (c : Z ⋙ 𝟭 E ≅ A ⋙ Z)
    {M N : C} (θM : A.obj M ≅ M) (θN : A.obj N ≅ N)
    (f : M ⟶ N) (hf : A.map f ≫ θN.hom = θM.hom ≫ f) :
    (S.mapIso (c.app M ≪≫ Z.mapIso θM)).hom ≫ (Z ⋙ S).map f =
      (Z ⋙ S).map f ≫ (S.mapIso (c.app N ≪≫ Z.mapIso θN)).hom := by
  dsimp only [Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom, Functor.comp_map]
  rw [← S.map_comp, ← S.map_comp]
  congr 1
  rw [Category.assoc, ← Z.map_comp, ← hf, Z.map_comp, ← Category.assoc,
    ← Functor.comp_map, ← c.hom.naturality, Category.assoc]
  all_goals rfl

private theorem chainNaturality {C : Type*} [Category C]
    (P Q : ℕ → C) (M N : C) (f : ∀ n, P n ⟶ Q n) (a : M ⟶ N)
    (eM : P 0 ≅ M) (eN : Q 0 ≅ N)
    (sM : ∀ n, P (n + 1) ≅ P n) (sN : ∀ n, Q (n + 1) ≅ Q n)
    (h₀ : f 0 ≫ eN.hom = eM.hom ≫ a)
    (hs : ∀ n, f (n + 1) ≫ (sN n).hom = (sM n).hom ≫ f n) (n : ℕ) :
    f n ≫ (isoChain Q N eN sN n).hom = (isoChain P M eM sM n).hom ≫ a := by
  induction n with
  | zero => exact h₀
  | succ n ih =>
    change f (n + 1) ≫ ((sN n).hom ≫ (isoChain Q N eN sN n).hom) =
      ((sM n).hom ≫ (isoChain P M eM sM n).hom) ≫ a
    rw [← Category.assoc, hs, Category.assoc, ih, Category.assoc]

private theorem iterateNaturality (l : ℕ) [Fact l.Prime] {T : Scheme.{u}}
    (a : T ⟶ T) (M N : Modules l T)
    (θM : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (θN : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj N ≅ N)
    (f : M ⟶ N)
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ θN.hom =
      θM.hom ≫ f) (n : ℕ) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower a n)).map f ≫
        (iterate l a N θN n).hom = (iterate l a M θM n).hom ≫ f := by
  unfold iterate
  apply chainNaturality
    (fun k ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a k)).obj M)
    (fun k ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a k)).obj N) M N
    (fun k ↦ (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a k)).map f) f
  · exact initialNaturality _ _ _ θM θN f hf
  · intro k
    unfold iterateStep
    exact stepNaturality _ _ _ _ θM θN f hf

private theorem operatorNaturality (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M N : Modules l T)
    (θM : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (θN : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj N ≅ N)
    (f : M ⟶ N)
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ θN.hom =
      θM.hom ≫ f) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    operator l D a M θM z n h ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          pointSections l D.k).map f =
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        pointSections l D.k).map f ≫ operator l D a N θN z n h := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  unfold operator
  rw [transport_normalized, transport_normalized]
  exact returnNaturality (pointSections l D.k)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower a n))
    (CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
      (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
        (localPositivePower (frobeniusPointIso D).hom n)) (localPositivePower a n) h)
    (iterate l a M θM n) (iterate l a N θN n) f
    (iterateNaturality l a M N θM θN f hf n)

private def normalizedComparisons (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    [IsAlgClosed D.k] {T : Scheme.{u}} (g : T ≅ T) (z : Spec (.of D.k) ⟶ T)
    (c : CondensedFibreComparisons.Comparisons l D g z) : Comparisons l D g z where
  tensor := c.tensor
  tensor_sections := c.tensor_sections
  dual := c.dual
  dual_evaluation := by
    intro L hL hLis f v
    have he := c.dual_evaluation L hL hLis f v
    apply (pointSectionsUnitIso l D.k).toLinearEquiv.injective
    change (pointSectionsUnitIso l D.k).hom (c.dual L hL hLis f v) =
      (pointSectionsUnitIso l D.k).hom ((pointSectionsUnitIso l D.k).inv _)
    rw [ModuleCat.hom_inv_apply, unitHom_apply, sections_map_apply]
    unfold pointSections
    simpa only [CondensedFibreComparisons.evaluation, tensorSection,
      CondensedFibreComparisons.tensorSection, Category.assoc] using he
  tensor_natural := c.tensor_natural
  dual_natural := c.dual_natural

private theorem normalizedCompatibility (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) [IsAlgClosed D.k] {T : Scheme.{u}}
    (g : T ≅ T) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower g.hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z)
    (c : CondensedFibreComparisons.Comparisons l D g z)
    (hc : CondensedFibreComparisons.WeilCompatibility l D g z n h c) :
    WeilCompatibility l D g z n h (normalizedComparisons l D g z c) := by
  refine ⟨hc.tensor_frobenius, hc.dual_frobenius, ?_⟩
  intro r F _hF
  constructor
  · unfold pointSections
    infer_instance
  · intro i
    apply operatorNaturality l D g.hom
      (∏ᶜ fun j ↦ (F j).carrier) (F i).carrier (sumWeil l g r F).str (F i).str
      (Pi.π (fun j ↦ (F j).carrier) i)
    simp [sumWeil]

/-- Tensor, dual and finite-sum fibres, with the canonical local geometric Frobenius.
Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-deligne-laumon-a1/sec-purity-of-the-lisse-part-of-the-fourier-transform/
sk-p-dl-a1-some-weight/lem-fd-realified-kernel-real.proof.md, Steps 1--2
(blueprint: lem-fd-condensed-fibre-linear-operations).

Proof:
1. The geometric fibre over the chosen closure is of finite type over a field and
quasi-compact, hence Noetherian. Apply lem-fd-condensed-lisse-tensor-noetherian to the
underlying constructible module F and lisse module L (with F = L for the dual clause):
the internal dual is lisse, tensor preserves constructibility, and the specified
comparison lisseTensorDerivedComparison from F[0] tensor-derived L[0] to (F tensor L)[0]
is an isomorphism.
2. Apply lem-fd-condensed-fibre-linear-operations-comparisons to the given Weil data.
The module contragredient is the evaluation-transpose composite specified for Weil duals;
locally a finite free dual is exact, and evaluation characterizes the comparison maps.
Tensoring point sections and transposing evaluation give the natural normalized tensor
and dual isomorphisms. Iterating tensor data and the canonical pullback compositors
commutes with point return, hence gives the tensor of the two local operators.
Invariance of evaluation gives (B f)(A v) = f(v), so B is the inverse transpose of A.
Its scalar evaluation normalization is converted through pointSectionsUnitIso.
3. Finally the finite-sum comparison commutes with each projection and its local operator,
by naturality of the iterate-and-return operator applied to the product projections;
point sections preserve products, so this is block-diagonal Frobenius, also for the
empty sum. -/
theorem condensed_fibre_linear_operations
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    [IsSeparated T₀.hom] : Assertions D l hl T₀ := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : LocallyOfFiniteType (D.geometricFiber T₀).hom := by
    change LocallyOfFiniteType (pullback.snd T₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance
  have : QuasiCompact (D.geometricFiber T₀).hom := by
    change QuasiCompact (pullback.snd T₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance
  have : IsLocallyNoetherian (D.geometricFiber T₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber T₀).hom
  have : CompactSpace (D.geometricFiber T₀).left :=
    QuasiCompact.compactSpace_of_compactSpace (D.geometricFiber T₀).hom
  have : IsNoetherian (D.geometricFiber T₀).left := ⟨⟩
  obtain ⟨_, hw⟩ :=
    CondensedFibreComparisons.condensed_fibre_linear_operations_comparisons D l hl T₀
  refine ⟨?_, ?_, ?_⟩
  · intro L hL hLis
    exact (CondensedRing.lisseTensor_on_noetherian l L.carrier L.carrier hL hLis).1
  · intro F L hF _hL hLis
    exact (CondensedRing.lisseTensor_on_noetherian l F.carrier L.carrier hF hLis).2
  · intro x ι hι
    obtain ⟨h, c, hc⟩ := hw x ι hι (localClosedPoint D T₀ x ι hι)
      (by simp [localClosedPoint]) (by simp [localClosedPoint])
    exact ⟨normalizedComparisons l D _ _ c,
      normalizedCompatibility l D _ _ _ h c hc⟩

set_option maxHeartbeats 800000 in
-- The dependent fibre tensor-section equation needs this elaboration budget.
end WeilConjectures.CondensedFibreLinearCurrent
