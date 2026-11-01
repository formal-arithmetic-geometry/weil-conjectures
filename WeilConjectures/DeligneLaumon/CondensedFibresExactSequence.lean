/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
import WeilConjectures.DeligneLaumon.CondensedFibresExactFinite
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Geometric fibre sequence subargument

Source: literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-lem-wrp-l2-growth/
lem-wf-l2-upper.proof.md, opening sentence.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Endofunctor
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

attribute [local irreducible] CondensedRing.upperStar CondensedRing.pointSections
  CondensedRing.upperStarComp CondensedRing.pointComparison
  CondensedRing.upperStarIsoIdOfIsSepClosed

private theorem iterate_chain_natural
    {C : Type*} [Category C] (P : ℕ → C ⥤ C) (G : C ⥤ C)
    (initial : P 0 ≅ G) (step : ∀ n, P (n + 1) ≅ G ⋙ P n)
    {M N : C} (θ : G.obj M ≅ M) (ψ : G.obj N ≅ N) (f : M ⟶ N)
    (hf : G.map f ≫ ψ.hom = θ.hom ≫ f) (n : ℕ) :
    (P n).map f ≫
        (CondensedModule.isoChain (fun k ↦ (P k).obj N) N
          (CondensedModule.evaluateInitial _ _ initial N ψ)
          (fun k ↦ CondensedModule.evaluateStep _ _ _ (step k) N ψ) n).hom =
      (CondensedModule.isoChain (fun k ↦ (P k).obj M) M
          (CondensedModule.evaluateInitial _ _ initial M θ)
          (fun k ↦ CondensedModule.evaluateStep _ _ _ (step k) M θ) n).hom ≫ f := by
  have hstep (k : ℕ) :
      (P (k + 1)).map f ≫
          (CondensedModule.evaluateStep _ _ _ (step k) N ψ).hom =
        (CondensedModule.evaluateStep _ _ _ (step k) M θ).hom ≫ (P k).map f := by
    simp only [CondensedModule.evaluateStep, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom]
    rw [← Category.assoc, (step k).hom.naturality, Functor.comp_map, Category.assoc,
      ← Functor.map_comp, hf, Functor.map_comp, ← Category.assoc]
  induction n with
  | zero =>
    change (P 0).map f ≫ (initial.hom.app N ≫ ψ.hom) =
      (initial.hom.app M ≫ θ.hom) ≫ f
    rw [← Category.assoc, initial.hom.naturality, Category.assoc, hf, Category.assoc]
  | succ n ih =>
    change (P (n + 1)).map f ≫
        ((CondensedModule.evaluateStep _ _ _ (step n) N ψ).hom ≫ _) =
      ((CondensedModule.evaluateStep _ _ _ (step n) M θ).hom ≫ _) ≫ f
    dsimp only [CondensedModule.isoChain] at ih
    rw [← Category.assoc, hstep, Category.assoc, ih, ← Category.assoc]

private theorem iterate_natural
    (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (a : T ⟶ T)
    {M N : CondensedModule.Modules l T}
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (ψ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj N ≅ N)
    (f : M ⟶ N)
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ ψ.hom =
      θ.hom ≫ f) (n : ℕ) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (localPositivePower a n)).map f ≫ (CondensedModule.iterate l a N ψ n).hom =
      (CondensedModule.iterate l a M θ n).hom ≫ f := by
  unfold CondensedModule.iterate CondensedModule.iterateStep
  exact iterate_chain_natural _ _ _ _ θ ψ f hf n

private theorem transport_chain_natural
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : C ⥤ C) (V : C ⥤ D) (W : D ⥤ E) (c : V ⋙ 𝟭 D ≅ P ⋙ V)
    {M N : C} (θ : P.obj M ≅ M) (ψ : P.obj N ≅ N) (f : M ⟶ N)
    (hf : P.map f ≫ ψ.hom = θ.hom ≫ f) :
    (V ⋙ W).map f ≫ (W.mapIso (c.app N ≪≫ V.mapIso ψ)).hom =
      (W.mapIso (c.app M ≪≫ V.mapIso θ)).hom ≫ (V ⋙ W).map f := by
  simp only [Functor.comp_map, Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom]
  have hc := c.hom.naturality f
  simp only [Functor.comp_map, Functor.id_map] at hc
  rw [← W.map_comp, ← W.map_comp]
  congr 1
  rw [← Category.assoc, hc, Category.assoc, ← V.map_comp, hf,
    V.map_comp, ← Category.assoc]

private theorem operator_natural
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T)
    {M N : CondensedModule.Modules l T}
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (ψ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj N ≅ N)
    (f : M ⟶ N)
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ ψ.hom =
      θ.hom ≫ f) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        CondensedRing.pointSections l D.k).map f ≫
        CondensedModule.operator l D a N ψ z n h =
      CondensedModule.operator l D a M θ z n h ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
          CondensedRing.pointSections l D.k).map f := by
  unfold CondensedModule.operator CondensedModule.transport
  exact transport_chain_natural
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) (localPositivePower a n))
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z)
    (CondensedRing.pointSections l D.k)
    (CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
      (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
        (localPositivePower (frobeniusPointIso D).hom n)) (localPositivePower a n) h)
    (CondensedModule.iterate l a M θ n) (CondensedModule.iterate l a N ψ n) f
    (iterate_natural l a θ ψ f hf n)

private theorem fibre_sequence_assertions_of
    {C : Type*} [Category C] [Preadditive C] {K : Type*} [Field K]
    (P : ObjectProperty C) (G : C ⥤ C) (V : C ⥤ ModuleCat K)
    [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (τ : ∀ M : IsoAlgebra G, End (V.obj M.carrier))
    (hinv : ∀ M, IsIso (τ M))
    (hfinite : ∀ M, P M → FiniteDimensional K (V.obj M))
    (hnatural : ∀ {M N : IsoAlgebra G} (f : M ⟶ N),
      V.map f.hom.f ≫ τ N = τ M ≫ V.map f.hom.f) :
    fibreWeilSequenceAssertions P G V τ := by
  intro F₁ F₂ F₃ f g h₁ h₂ h₃ hf hg hfg
  let := hf
  let := hg
  let S := (ComposableArrows.mk₂ f.hom.f g.hom.f).sc' hfg.toIsComplex 0 1 2
  have hs : S.ShortExact :=
    { exact := hfg.exact 0 (by decide)
      mono_f := by change Mono f.hom.f; infer_instance
      epi_g := by change Epi g.hom.f; infer_instance }
  have hsV := hs.map_of_exact V
  exact ⟨hinv F₁, hinv F₂, hinv F₃,
    hfinite F₁.carrier h₁, hfinite F₂.carrier h₂, hfinite F₃.carrier h₃,
    hsV.moduleCat_injective_f,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hsV.exact,
    hsV.moduleCat_surjective_g, hnatural f, hnatural g⟩

private theorem geometric_fibre_exact
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (z : Spec (.of D.k) ⟶ T) :
    let V := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
      CondensedRing.pointSections l D.k
    V.Additive ∧ PreservesFiniteLimits V ∧ PreservesFiniteColimits V := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let V := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
    CondensedRing.pointSections l D.k
  have : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).Additive :=
    CondensedRing.upperStar_additive _ z
  have : PreservesFiniteLimits
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z) :=
    CondensedRing.preservesFiniteLimits_upperStar _ z
  have : PreservesFiniteColimits
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z) :=
    CondensedRing.preservesFiniteColimits_upperStar _ z
  have : (CondensedRing.pointSections l D.k).Additive :=
    CondensedRing.instAdditivePointModModuleCatULiftPadicAlgClPointSections l D.k
  have : PreservesFiniteLimits (CondensedRing.pointSections l D.k) :=
    CondensedRing.instPreservesFiniteLimitsPointModModuleCatULiftPadicAlgClPointSections l D.k
  have : PreservesFiniteColimits (CondensedRing.pointSections l D.k) :=
    CondensedRing.instPreservesFiniteColimitsPointModModuleCatULiftPadicAlgClPointSections l D.k
  have : V.Additive := by dsimp only [V]; infer_instance
  have : PreservesFiniteLimits V := by dsimp only [V]; infer_instance
  have : PreservesFiniteColimits V := by dsimp only [V]; infer_instance
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem local_operator_isIso
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (M : CondensedModule.Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z) :
    IsIso (CondensedModule.operator l D a M θ z n h) := by
  unfold CondensedModule.operator
  infer_instance

private theorem local_point_finite
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    ∀ M : CondensedModule.Modules l (D.geometricFiber Y₀).left,
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber Y₀).left M →
      FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
          (localClosedPoint D Y₀ y ι hι) ⋙ CondensedRing.pointSections l D.k).obj M) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let z := localClosedPoint D Y₀ y ι hι
  have hfinite := condensed_fibres_point_finiteness D l hl Y₀ z (by
    simp [z, localClosedPoint, FiniteFieldDatum.geometricFiber])
  intro M hM
  exact hfinite.2.2.2.1 ⟨M, hM⟩

private theorem module_point_sequence
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})
    {T : Scheme.{u}} (a : T ⟶ T) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z)
    (P : ObjectProperty (CondensedModule.Modules l T))
    (hfinite : ∀ M, P M → FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
      ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        CondensedRing.pointSections l D.k).obj M)) :
    fibreWeilSequenceAssertions P
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
        CondensedRing.pointSections l D.k)
      (fun M ↦ CondensedModule.operator l D a M.carrier M.str z n h) := by
  let V := CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z ⋙
    CondensedRing.pointSections l D.k
  have hgeom := geometric_fibre_exact l D z
  let : V.Additive := hgeom.1
  let : PreservesFiniteLimits V := hgeom.2.1
  let : PreservesFiniteColimits V := hgeom.2.2
  refine fibre_sequence_assertions_of P _ V _ ?_ hfinite ?_
  · intro M
    exact local_operator_isIso l D a M.carrier M.str z n h
  · intro M N f
    exact operator_natural l D a M.str N.str f.hom.f f.hom.h z n h

/-- The canonical local Frobenius intertwines both maps of each constructible exact sequence.
Source: latest blueprint lem-wf-l2-upper.proof.md, opening sentence
(blueprint: lem-wf-condensed-fibres-point-sequence).

Proof: Each factor of CondensedModule.transport is an isomorphism, so each recorded
operator is invertible. For a morphism of Weil objects, induct on the positive exponent
in CondensedModule.iterate: the initial case is the Weil-morphism square; the successor
case follows from naturality of upperStarComp and functoriality of pullback. Naturality
of pointComparison and pointSections then gives the two operator squares. Apply the
exact geometric fibre functor to the ambient short exact sequence. Preservation of
kernels and cokernels gives injectivity, exactness and surjectivity of its underlying
linear maps. Constructibility gives finite-dimensional values by the split-point-cover
finite constant model argument. Apply it separately to the three carriers. -/
theorem condensed_fibres_point_sequence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    fibreWeilSequenceAssertions
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber Y₀).left)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius Y₀).hom)
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (localClosedPoint D Y₀ y ι hι) ⋙ CondensedRing.pointSections l D.k)
      (fun M ↦ CondensedModule.operator l D (D.geometricFrobenius Y₀).hom M.carrier M.str
        (localClosedPoint D Y₀ y ι hι) (localClosedPointDegree D Y₀ y - 1)
        (localClosedPoint_return D Y₀ y ι hι)) := by
  exact module_point_sequence l D (D.geometricFrobenius Y₀).hom
    (localClosedPoint D Y₀ y ι hι) (localClosedPointDegree D Y₀ y - 1)
    (localClosedPoint_return D Y₀ y ι hι) _ (local_point_finite D l hl Y₀ y ι hι)

end WeilConjectures
