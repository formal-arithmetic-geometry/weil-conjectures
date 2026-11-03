/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealWeights
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.Data.Fin.Rev
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstantWeil.CondensedConstantWeilTwist
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Operations
public import WeilConjectures.RepresentationTheory.CompositionSeries
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.Algebra.Field.ULift
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstantWeil.CondensedConstantWeilTwist
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import Mathlib.Analysis.SpecialFunctions.Log.Base
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import WeilConjectures.CategoryTheory.Monoidal.EndTensorUnit

/-! # Elementary operations on condensed Weil weights

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-weights-deligne-theorem/sec-wdef-weights/sk-r-real-linear/_section.md
and sk-r-real-linear.proof.md; Wei Yang, Zulip #1441, items 34--35.
(blueprint: sk-r-real-linear).

Duals here are coefficient internal duals. The mixed-dual theorem makes no
assumption on a chosen filtration; the annihilator theorem requires lisse gradeds.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v z
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.MonoidalCategory CategoryTheory.Endofunctor
open scoped CategoryTheory.Obj
namespace WeilConjectures.RealLinearWeights
open NativeL2 NativeCondensedModule

private instance nativePointUnit_projective (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] [IsSepClosed k] :
    Projective (MonoidalCategoryStruct.tensorUnit
      (NativeCondensedModule.Modules l (Spec (.of k)))) :=
  projective_regular_of_isSepClosed (k := k) _

private instance nativePointSections_preservesFiniteLimits (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] [IsSepClosed k] :
    PreservesFiniteLimits (NativeCondensedModule.pointSections l k) := by
  unfold NativeCondensedModule.pointSections
  infer_instance

private instance nativePointSections_preservesFiniteColimits (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] [IsSepClosed k] :
    PreservesFiniteColimits (NativeCondensedModule.pointSections l k) := by
  unfold NativeCondensedModule.pointSections
  infer_instance

private instance nativePointSections_additive (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] [IsSepClosed k] :
    (NativeCondensedModule.pointSections l k).Additive := by
  unfold NativeCondensedModule.pointSections
  infer_instance

attribute [local irreducible] NativeCondensedModule.pointSections
  NativeCondensedModule.pointScalarsOp NativeCondensedModule.pointUnitEndRingHom
  CondensedRing.upperStar

private theorem chain_naturality {C : Type v} [Category.{z} C]
    (G : C ⥤ C) (F : ℕ → C ⥤ C) (c₀ : F 0 ≅ G)
    (c : ∀ n, F (n + 1) ≅ G ⋙ F n)
    {A B : C} (θA : G.obj A ≅ A) (θB : G.obj B ≅ B)
    (f : A ⟶ B) (hf : G.map f ≫ θB.hom = θA.hom ≫ f) (n : ℕ) :
    (F n).map f ≫ (isoChain (fun n ↦ (F n).obj B) B
      (evaluateInitial (F 0) G c₀ B θB)
      (fun n ↦ evaluateStep (F n) G (F (n + 1)) (c n) B θB) n).hom =
    (isoChain (fun n ↦ (F n).obj A) A
      (evaluateInitial (F 0) G c₀ A θA)
      (fun n ↦ evaluateStep (F n) G (F (n + 1)) (c n) A θA) n).hom ≫ f := by
  induction n with
  | zero =>
    change (F 0).map f ≫ c₀.hom.app B ≫ θB.hom =
      (c₀.hom.app A ≫ θA.hom) ≫ f
    rw [← Category.assoc, c₀.hom.naturality, Category.assoc, hf, Category.assoc]
  | succ n ih =>
    have hs : (F (n + 1)).map f ≫
        (evaluateStep (F n) G (F (n + 1)) (c n) B θB).hom =
        (evaluateStep (F n) G (F (n + 1)) (c n) A θA).hom ≫ (F n).map f := by
      change (F (n + 1)).map f ≫ (c n).hom.app B ≫ (F n).map θB.hom =
        ((c n).hom.app A ≫ (F n).map θA.hom) ≫ (F n).map f
      rw [← Category.assoc, (c n).hom.naturality]
      simp only [Functor.comp_map, Category.assoc]
      rw [← (F n).map_comp, hf, (F n).map_comp]
    change (F (n + 1)).map f ≫
      (evaluateStep (F n) G (F (n + 1)) (c n) B θB).hom ≫ _ =
      ((evaluateStep (F n) G (F (n + 1)) (c n) A θA).hom ≫ _) ≫ f
    dsimp only [isoChain] at ih
    rw [← Category.assoc, hs, Category.assoc, ih, ← Category.assoc]

private theorem intertwines_of_eq {C : Type*} [Category C] {A B : C}
    (f : A ⟶ B) (a a' : End A) (b b' : End B)
    (ha : a = a') (hb : b = b') (h : f ≫ b' = a' ≫ f) : f ≫ b = a ≫ f := by
  rw [ha, hb]
  exact h

private theorem intertwines_of_iso_eq {C : Type*} [Category C] {A B : C}
    (f : A ⟶ B) (a a' : A ≅ A) (b b' : B ≅ B)
    (ha : a = a') (hb : b = b') (h : f ≫ b'.hom = a'.hom ≫ f) :
    f ≫ b.hom = a.hom ≫ f := by
  rw [ha, hb]
  exact h

private theorem transport_eq_mapIso
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ NativeCondensedModule.localPositivePower a n =
      NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom n ≫ z) :
    transport l D a M θ z z n h =
      let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
      (pointSections l D.k).mapIso
        ((CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
          (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
            (NativeCondensedModule.localPositivePower
              (NativeCondensedModule.frobeniusPointIso D).hom n))
          (NativeCondensedModule.localPositivePower a n) h).app M ≪≫
          (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).mapIso
            (iterate l a M θ n)) := rfl

private def nativeFibreMap (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) {A B : Modules l T} (f : A ⟶ B) :
    fibre l D A z ⟶ fibre l D B z :=
  (pointSections l D.k).map
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f)

-- Keep computed `mapIso` projections inside the abstract proof. Specializing a
-- single bundled conclusion avoids expensive repeated kernel conversion of the
-- concrete condensed pullback and point-section functors.
private theorem operator_naturality_abstract
    {C E H : Type*} [Category C] [Category E] [Category H]
    (Q : C ⥤ C) (Z : C ⥤ E) (P : E ⥤ H) (c : Z ⋙ 𝟭 E ≅ Q ⋙ Z)
    {A B : C} (θA : Q.obj A ≅ A) (θB : Q.obj B ≅ B) (f : A ⟶ B)
    (hf : Q.map f ≫ θB.hom = θA.hom ≫ f)
    (a : P.obj (Z.obj A) ≅ P.obj (Z.obj A))
    (b : P.obj (Z.obj B) ≅ P.obj (Z.obj B))
    (a₀ : End (P.obj (Z.obj A))) (b₀ : End (P.obj (Z.obj B)))
    (ha : a = P.mapIso (c.app A ≪≫ Z.mapIso θA))
    (hb : b = P.mapIso (c.app B ≪≫ Z.mapIso θB))
    (ha₀ : a₀ = a.hom) (hb₀ : b₀ = b.hom) :
    P.map (Z.map f) ≫ b₀ = a₀ ≫ P.map (Z.map f) := by
  exact intertwines_of_eq _ a₀ _ b₀ _ ha₀ hb₀
    (intertwines_of_iso_eq _ a _ b _ ha hb
      (transport_naturality_abstract Q Z P c θA θB f hf))

private theorem operator_naturality
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) {A B : Modules l T}
    (θA : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj A ≅ A)
    (θB : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj B ≅ B)
    (f : A ⟶ B)
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ θB.hom =
      θA.hom ≫ f)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ NativeCondensedModule.localPositivePower a n =
      NativeCondensedModule.localPositivePower
        (NativeCondensedModule.frobeniusPointIso D).hom n ≫ z) :
    nativeFibreMap l D z f ≫ operator l D a B θB z n h =
    operator l D a A θA z n h ≫
      nativeFibreMap l D z f := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  exact operator_naturality_abstract
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (NativeCondensedModule.localPositivePower a n))
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z)
    (pointSections l D.k)
    (CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
      (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
        (NativeCondensedModule.localPositivePower
          (NativeCondensedModule.frobeniusPointIso D).hom n))
      (NativeCondensedModule.localPositivePower a n) h)
    (iterate l a A θA n) (iterate l a B θB n) f
    (iterate_naturality l a θA θB f hf n)
    (transport l D a A θA z z n h) (transport l D a B θB z z n h)
    (operator l D a A θA z n h) (operator l D a B θB z n h)
    (transport_eq_mapIso l D a A θA z n h) (transport_eq_mapIso l D a B θB z n h)
    (operator_eq_transport l D a A θA z n h) (operator_eq_transport l D a B θB z n h)


private theorem eigenvalue_mem_of_injective {K : Type v} [Field K]
    {V₁ V₂ : Type z} [AddCommGroup V₁] [AddCommGroup V₂] [Module K V₁] [Module K V₂]
    (F₁ : Module.End K V₁) (F₂ : Module.End K V₂)
    (i : V₁ →ₗ[K] V₂) (hi : Function.Injective i)
    (hiF : ∀ v, i (F₁ v) = F₂ (i v))
    {α : K} (hα : F₁.HasEigenvalue α) : F₂.HasEigenvalue α := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := i v)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
  · rw [← hiF, hv.apply_eq_smul, map_smul]
  · exact fun h ↦ hv.2 (hi (h.trans (map_zero i).symm))

private theorem nativeWeilFibre_exact (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :
    PreservesFiniteLimits (nativeWeilFibre D l X₀ z) ∧
      PreservesFiniteColimits (nativeWeilFibre D l X₀ z) ∧
      (nativeWeilFibre D l X₀ z).Additive := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  unfold nativeWeilFibre
  exact ⟨inferInstance, inferInstance, inferInstance⟩


private instance nativeWeilFibre_limits
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :
    PreservesFiniteLimits (nativeWeilFibre D l X₀ z) :=
  (nativeWeilFibre_exact D l X₀ z).1

private instance nativeWeilFibre_colimits
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) :
    PreservesFiniteColimits (nativeWeilFibre D l X₀ z) :=
  (nativeWeilFibre_exact D l X₀ z).2.1

private theorem eigenvalue_mem_of_surjective {K : Type v} [Field K]
    {V₁ V₂ : Type z} [AddCommGroup V₁] [AddCommGroup V₂] [Module K V₁] [Module K V₂]
    [FiniteDimensional K V₁] [FiniteDimensional K V₂]
    (F₁ : Module.End K V₁) (F₂ : Module.End K V₂)
    (p : V₁ →ₗ[K] V₂) (hp : Function.Surjective p)
    (hpF : ∀ v, p (F₁ v) = F₂ (p v))
    {α : K} (hα : F₂.HasEigenvalue α) : F₁.HasEigenvalue α := by
  have hker : LinearMap.ker p ≤ (LinearMap.ker p).comap F₁ := by
    intro v hv
    change p (F₁ v) = 0
    rw [hpF, LinearMap.mem_ker.mp hv, map_zero]
  let e := p.quotKerEquivOfSurjective hp
  have hc := LinearMap.charpoly_eq_of_comp_eq e
    (f := (LinearMap.ker p).mapQ (LinearMap.ker p) F₁ hker) (g := F₂) (by
      ext x
      simpa [e] using hpF x)
  apply (Module.End.hasEigenvalue_iff_isRoot_charpoly F₁ α).mpr
  apply ((Module.End.hasEigenvalue_iff_isRoot_charpoly F₂ α).mp hα).dvd
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ F₁ (LinearMap.ker p) hker,
    hc]
  exact dvd_mul_left _ _

private theorem shift_homology_comp
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory C) (r n : ℤ) (φ : F.mapDerivedCategory.obj K ⟶ K) :
    let e := (DerivedCategory.homologyFunctor C 0).shiftIso r n (r + n) rfl
    F.map (e.hom.app K) ≫
        (F.mapDerivedCategoryHomologyFunctorIso (r + n)).hom.app K ≫
          (DerivedCategory.homologyFunctor C (r + n)).map φ =
      ((F.mapDerivedCategoryHomologyFunctorIso n).hom.app (K⟦r⟧) ≫
        (DerivedCategory.homologyFunctor C n).map
          ((F.mapDerivedCategory.commShiftIso r).hom.app K ≫
            (shiftFunctor _ r).map φ)) ≫ e.hom.app K := by
  dsimp only
  rw [← Category.assoc,
    F.mapDerivedCategoryHomologyFunctorIso_hom_app_shiftIso r n (r + n) rfl K]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  congr 1
  exact ((DerivedCategory.homologyFunctor C 0).shiftIso r n (r + n) rfl).hom.naturality φ |>.symm

private def genericShiftPair
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : IsoAlgebra F.mapDerivedCategory) (r : ℤ) : IsoAlgebra F.mapDerivedCategory :=
  IsoAlgebra.mk (K.carrier⟦r⟧)
    ((F.mapDerivedCategory.commShiftIso r).app K.carrier ≪≫
      (shiftFunctor _ r).mapIso K.str)

private def genericHomologyPair
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : IsoAlgebra F.mapDerivedCategory) (n : ℤ) : IsoAlgebra F :=
  IsoAlgebra.mk ((DerivedCategory.homologyFunctor C n).obj K.carrier)
    ((F.mapDerivedCategoryHomologyFunctorIso n).app K.carrier ≪≫
      (DerivedCategory.homologyFunctor C n).mapIso K.str)

private def genericHomologyShiftIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : IsoAlgebra F.mapDerivedCategory) (r n : ℤ) :
    genericHomologyPair F (genericShiftPair F K r) n ≅
      genericHomologyPair F K (r + n) := by
  let e := (DerivedCategory.homologyFunctor C 0).shiftIso r n (r + n) rfl
  refine ObjectProperty.isoMk _ (Algebra.isoMk (e.app K.carrier) ?_)
  change F.map (e.hom.app K.carrier) ≫
      (F.mapDerivedCategoryHomologyFunctorIso (r + n)).hom.app K.carrier ≫
        (DerivedCategory.homologyFunctor C (r + n)).map K.str.hom =
    ((F.mapDerivedCategoryHomologyFunctorIso n).hom.app (K.carrier⟦r⟧) ≫
      (DerivedCategory.homologyFunctor C n).map
        ((F.mapDerivedCategory.commShiftIso r).hom.app K.carrier ≫
          (shiftFunctor _ r).map K.str.hom)) ≫ e.hom.app K.carrier
  exact shift_homology_comp F K.carrier r n K.str.hom

section Geometric

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [hsep : IsSeparated X₀.hom]

include hsep

set_option linter.unusedSectionVars false in
/-- Subobjects and quotients retain the specified pure weight.
Proof: exact Frobenius fibres turn the arrow into an invariant subspace or quotient.
The block triangular characteristic polynomial factors, so all surviving eigenvalues
have the original modulus; a zero fibre has no eigenvalues.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem pure_mono (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    {M N : WeilModule D l X₀} (f : N ⟶ M) [Mono f]
    (_hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (_hN : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left N.carrier) (w : ℝ)
    (h : Pure D l X₀ M iota w) : Pure D l X₀ N iota w := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  intro x i hi α hα
  let V := nativeWeilFibre D l X₀ (localClosedPoint D X₀ x i hi)
  have hinj : Function.Injective (V.map f).hom :=
    (ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (V.map f))
  apply h x i hi α
  apply eigenvalue_mem_of_injective (closedOperator D l X₀ N x i hi).hom
    (closedOperator D l X₀ M x i hi).hom (V.map f).hom hinj _ hα
  intro v
  exact (congrArg (fun g ↦ g.hom v)
    (closedOperator_naturality D l X₀ x i hi f)).symm

set_option linter.unusedSectionVars false in
/-- Subobjects and quotients retain the specified pure weight.
Proof: exact Frobenius fibres turn the arrow into an invariant subspace or quotient.
The block triangular characteristic polynomial factors, so all surviving eigenvalues
have the original modulus; a zero fibre has no eigenvalues.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem pure_epi (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    {M N : WeilModule D l X₀} (f : M ⟶ N) [Epi f]
    (_hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier)
    (_hN : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left N.carrier) (w : ℝ)
    (h : Pure D l X₀ M iota w) : Pure D l X₀ N iota w := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  intro x i hi α hα
  let V := nativeWeilFibre D l X₀ (localClosedPoint D X₀ x i hi)
  let : FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
      (fibre l D M.carrier (localClosedPoint D X₀ x i hi)) :=
    NativeCondensedModule.constructible_fibre_finiteDimensional D l M.carrier _hM
      (localClosedPoint D X₀ x i hi)
  let : FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
      (fibre l D N.carrier (localClosedPoint D X₀ x i hi)) :=
    NativeCondensedModule.constructible_fibre_finiteDimensional D l N.carrier _hN
      (localClosedPoint D X₀ x i hi)
  have hsurj : Function.Surjective (V.map f).hom :=
    (ModuleCat.epi_iff_surjective _).mp (inferInstance : Epi (V.map f))
  apply h x i hi α
  apply eigenvalue_mem_of_surjective (closedOperator D l X₀ M x i hi).hom
    (closedOperator D l X₀ N x i hi).hom (V.map f).hom hsurj _ hα
  intro v
  exact (congrArg (fun g ↦ g.hom v)
    (closedOperator_naturality D l X₀ x i hi f)).symm

omit hsep in
private theorem mixed_of_iso {M N : WeilModule D l X₀} (e : M ≅ N)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) (h : Mixed D l X₀ M iota w) :
    Mixed D l X₀ N iota w := by
  obtain ⟨n, G, φ, hC, h0, ⟨hn⟩, hm, hwt⟩ := h
  exact ⟨n, G, φ, hC, h0, ⟨hn ≪≫ e⟩, hm, hwt⟩

private def shiftWeilCohomologyIso
    (K : IsoAlgebra (CondensedRing.StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
      (CondensedRing.StrictWeilCondensed.modelFrobenius D X₀))) (r n : ℤ) :
    complexWeilCohomology D l X₀ (shiftComplex D l X₀ K r) n ≅
      complexWeilCohomology D l X₀ K (r + n) := by
  exact genericHomologyShiftIso
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) K r n

set_option linter.unusedSectionVars false in
/-- A cohomological shift by r raises an upper complex weight by r.
Proof: the canonical comparison identifies H^i(K[r]) with H^(i+r)(K), including
its induced Weil datum. The old bound w+(i+r) equals (w+r)+i for every integer i.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem shift_weights (_hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (K : IsoAlgebra (CondensedRing.StrictWeilCondensed.action (Profinite.padicAlgClRingObj l)
      (CondensedRing.StrictWeilCondensed.modelFrobenius D X₀))) (w : ℝ) (r : ℤ)
    (_hKbc : constantModelBoundedConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left K.carrier)
    (hK : complexMixedOfWeightsAtMost D l X₀ K iota w) :
    complexMixedOfWeightsAtMost D l X₀
      (shiftComplex D l X₀ K r) iota (w + (r : ℝ)) := by
  intro n
  have h := mixed_of_iso D l X₀ (shiftWeilCohomologyIso D l X₀ K r n).symm
    iota (w + ((r + n : ℤ) : ℝ)) (hK (r + n))
  simpa only [Int.cast_add, add_assoc] using h

/-- Constant Weil twisting shifts every pure weight.
Proof: the degree-d local eigenvalue of the constant line is b^d. Tensor
eigenvalues are multiplied by it. Its weight is 2*log(norm(iota b))/log(q),
since both logarithms at degree d are multiplied by d. Tensoring is exact
with inverse twist b inverse, so the same computation applies to every graded piece.
Source: latest blueprint, sk-r-real-linear.proof.md
(blueprint: sk-r-real-linear). -/
theorem constant_twist_pure (hl : l ≠ D.p) (iota : PadicAlgCl l →+* ℂ)
    (M : condensedConstructibleWeilSheaves (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom) (b : (PadicAlgCl l)ˣ) (w : ℝ)
    (hM : Pure D l X₀ M.obj iota w) :
    Pure D l X₀ (CondensedRing.ConstantWeil.twist l D X₀ hl b M).obj iota
      (w + AlgebraicGeometry.WeilGroup.frobeniusWeight iota D.q (b : PadicAlgCl l)) := by
  apply Pure.constantTwist D l hl X₀ M iota w _ hM b
  simp only [AlgebraicGeometry.WeilGroup.frobeniusWeight, Real.logb, D.card_base]
  ring

set_option linter.unusedSectionVars false in
end Geometric

section Complement

variable {E : Type u} {V : Type v} {W : Type z} [Field E] [Group W] [AddCommGroup V] [Module E V]
  [FiniteDimensional E V]

end Complement

end WeilConjectures.RealLinearWeights
