/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import WeilConjectures.WeilSheaf.BaseChangeField.Transport
import WeilConjectures.SixFunctors.ProEtale.Adic.IrreducibleLisse
import WeilConjectures.WeilSheaf.LisseFiltration
import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-! # Pullback along a map intertwining a power of geometric Frobenius

The construction uses the source pro-etale category throughout. No comparison with a
common-stage coefficient category is required.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ w₁ w₂

open CategoryTheory Limits Endofunctor
open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

/-- A named universal-property comparison, with category data kept abstract.
Source: exact inverse image of the diagram in blueprint
`thm-zl-real-mixed-by-curves.proof.md`, paragraph 2
(blueprint: def-zl-powered-geometric-pullback). -/
noncomputable def exactFunctorCokernelIso
    {A : Type v₁} {B : Type v₂} [Category.{w₁} A] [Category.{w₂} B]
    [HasZeroMorphisms A] [HasZeroMorphisms B]
    (F : A ⥤ B) [F.PreservesZeroMorphisms] {V W : A} (i : V ⟶ W)
    [HasCokernel i] [HasCokernel (F.map i)]
    [PreservesColimit (parallelPair i 0) F] :
    F.obj (cokernel i) ≅ cokernel (F.map i) :=
  PreservesCokernel.iso F i

attribute [irreducible] exactFunctorCokernelIso

variable {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
  {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
  (u : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
  (r : ℕ)
  (hu : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫ u =
    u ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom)

/-- Pullback commutes with the indicated Frobenius powers.
Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraphs 1--2
(blueprint: def-zl-powered-geometric-pullback). -/
noncomputable def poweredGeometricPullbackCommIso :
    (u)^*ᵃ[l] ⋙ frobeniusPullback k₁ l C ≅
      ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r ⋙ (u)^*ᵃ[l] :=
  Functor.isoWhiskerLeft _
      (ProEtale.adicUpperStarIsoLowerStarInv l
        (C ↘ Spec (.of k₁)).geometricGaloisFrobenius).symm ≪≫
    (ProEtale.adicUpperStarComp l _ _).symm ≪≫
    ProEtale.adicUpperStarCongr l hu ≪≫
    ProEtale.adicUpperStarComp l _ _ ≪≫
    Functor.isoWhiskerRight
      (ProEtale.adicUpperStarIsoLowerStarInv l
        ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r)) _

/-- The actual exact pullback of source pro-etale Weil sheaves, with iterated Weil map.
Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraphs 1--2
(blueprint: def-zl-powered-geometric-pullback). -/
noncomputable def poweredGeometricPullbackAll :
    ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₁ l C :=
  ProEtaleWeilSheaf.powFunctor k₀ l X r ⋙
    IsoAlgebra.mapOfNatIso (poweredGeometricPullbackCommIso u r hu)

instance : PreservesFiniteLimits (poweredGeometricPullbackAll (l := l) u r hu) := by
  unfold poweredGeometricPullbackAll
  infer_instance

instance : PreservesFiniteColimits (poweredGeometricPullbackAll (l := l) u r hu) := by
  unfold poweredGeometricPullbackAll
  infer_instance

omit [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)] in
@[simp]
theorem poweredGeometricPullbackAll_obj_carrier (G : ProEtaleWeilSheaf k₀ l X) :
    ((poweredGeometricPullbackAll u r hu).obj G).carrier = (u)^*ᵃ[l].obj G.carrier := by
  change ((IsoAlgebra.mapOfNatIso (poweredGeometricPullbackCommIso u r hu)).obj
    ((ProEtaleWeilSheaf.powFunctor k₀ l X r).obj G)).carrier = _
  rw [IsoAlgebra.mapOfNatIso_obj_carrier, ProEtaleWeilSheaf.powFunctor_obj_carrier]

/-- The same pullback restricted to constructible source Weil sheaves.
Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraphs 1--2
(blueprint: def-zl-powered-geometric-pullback). -/
noncomputable def poweredGeometricPullback : WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l C :=
  (objectProperty k₀ l X).liftFullSubcategory (objectProperty k₁ l C)
    (poweredGeometricPullbackAll u r hu)
    (fun _ h ↦ ProEtale.IsAdicConstructibleSheaf.upperStar u h)

@[simp]
theorem poweredGeometricPullback_obj_carrier (G : WeilSheaf k₀ l X) :
    ((poweredGeometricPullback u r hu).obj G).obj.carrier =
      (u)^*ᵃ[l].obj G.obj.carrier :=
  poweredGeometricPullbackAll_obj_carrier u r hu G.obj

variable [LocallyOfFiniteType (X ↘ Spec (.of k₀))]
  [LocallyOfFiniteType (C ↘ Spec (.of k₁))]

instance : PreservesFiniteLimits (poweredGeometricPullback (l := l) u r hu) := by
  have : PreservesFiniteLimits (poweredGeometricPullback (l := l) u r hu ⋙
      (objectProperty k₁ l C).ι) :=
    preservesFiniteLimits_of_natIso (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm
  have : ReflectsLimitsOfSize.{0, 0} (objectProperty k₁ l C).ι := inferInstance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (objectProperty k₁ l C).ι

instance : PreservesFiniteColimits (poweredGeometricPullback (l := l) u r hu) := by
  have : PreservesFiniteColimits (poweredGeometricPullback (l := l) u r hu ⋙
      (objectProperty k₁ l C).ι) :=
    preservesFiniteColimits_of_natIso (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm
  have : ReflectsColimitsOfSize.{0, 0} (objectProperty k₁ l C).ι := inferInstance
  exact preservesFiniteColimits_of_reflects_of_preserves _ (objectProperty k₁ l C).ι

omit [LocallyOfFiniteType (C ↘ Spec (.of k₁))] in
/-- Expose the constructed exact functor through its canonical defining equality.
Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraph 2
(blueprint: def-zl-powered-geometric-pullback).
Proof: take the explicit powered pullback and its proved exactness instances. The
last equality determines the functor, rather than asserting an unspecified witness. -/
theorem exists_poweredGeometricPullback :
    ∃ P : WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l C,
      PreservesFiniteLimits P ∧ PreservesFiniteColimits P ∧
        poweredGeometricPullback u r hu = P :=
  ⟨poweredGeometricPullback u r hu, inferInstance, inferInstance, rfl⟩

omit [LocallyOfFiniteType (X ↘ Spec (.of k₀))]
  [LocallyOfFiniteType (C ↘ Spec (.of k₁))] in
/-- Powered geometric pullback preserves lissity.
Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraph 2
(blueprint: def-zl-powered-geometric-pullback). -/
theorem poweredGeometricPullback_isLisse {G : WeilSheaf k₀ l X} (hG : G.IsLisse) :
    ((poweredGeometricPullback u r hu).obj G).IsLisse := by
  unfold IsLisse
  rw [poweredGeometricPullback_obj_carrier]
  exact ProEtale.IsAdicLisseSheaf.upperStar u hG

/-- Geometric simplicity implies arithmetic lisse simplicity.
Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraph 2
(blueprint: def-zl-powered-geometric-pullback). -/
theorem isIrreducibleLisse_of_geometric {H : WeilSheaf k₁ l C}
    (hH : ProEtale.IsIrreducibleAdicLocalSystem H.obj.carrier) :
    H.IsIrreducibleLisse := by
  refine ⟨hH.1, fun hz ↦ hH.2.1 (isZero_iff_isZero_carrier.mp hz), ?_⟩
  intro A a ha hA
  let F := carrierFunctor k₁ l C
  have : Mono (F.map a) := inferInstance
  rcases hH.2.2 A.obj.carrier (F.map a) inferInstance hA with hz | hi
  · exact Or.inl (isZero_iff_isZero_carrier.mpr hz)
  · have : IsIso a.hom.hom.f := hi
    exact Or.inr (isIso_of_isIso_hom_hom_f a)

/-- Geometric simplicity can be transported through a Weil-sheaf isomorphism.
Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraph 2
(blueprint: def-zl-powered-geometric-pullback). -/
theorem isIrreducibleLisse_of_geometric_iso {A B : WeilSheaf k₁ l C}
    (e : A ≅ B) (h : ProEtale.IsIrreducibleAdicLocalSystem A.obj.carrier) :
    B.IsIrreducibleLisse :=
  (isIrreducibleLisse k₁ l C).prop_of_iso e
    (isIrreducibleLisse_of_geometric (H := A) h)

/-- Pullback by a scheme isomorphism reflects geometric simplicity.
Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraph 2
(blueprint: def-zl-powered-geometric-pullback). -/
theorem isIrreducibleAdicLocalSystem_of_iso_pullback
    {D E : Scheme.{u}} (z : D ≅ E) (M : ProEtale.AdicSheaf l E)
    (h : ProEtale.IsIrreducibleAdicLocalSystem ((z.hom)^*ᵃ[l].obj M)) :
    ProEtale.IsIrreducibleAdicLocalSystem M := by
  let F := (z.hom)^*ᵃ[l]
  have hL := h.1.upperStar z.inv
  have e : (z.inv)^*ᵃ[l].obj ((z.hom)^*ᵃ[l].obj M) ≅ M :=
    (ProEtale.adicUpperStarComp l z.inv z.hom).symm.app M ≪≫
      (ProEtale.adicUpperStarCongr l z.inv_hom_id).app M ≪≫
      (ProEtale.adicUpperStarId l E).app M
  refine ⟨hL.of_iso e, fun hz ↦ h.2.1 (F.map_isZero hz), ?_⟩
  intro A a ha hA
  have : Mono (F.map a) := inferInstance
  rcases h.2.2 (F.obj A) (F.map a) inferInstance (hA.upperStar z.hom) with hz | hi
  · exact Or.inl (IsZero.of_full_of_faithful_of_isZero F A hz)
  · have : IsIso (F.map a) := hi
    exact Or.inr (isIso_of_reflects_iso a F)

/-- Reflect simplicity from the same restriction written through an isomorphic model.
Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraph 2
(blueprint: def-zl-powered-geometric-pullback). -/
theorem isIrreducibleAdicLocalSystem_of_iso_composite
    {D E T : Scheme.{u}} (z : D ≅ E) (u : E ⟶ T) (v : D ⟶ T)
    (hz : z.hom ≫ u = v) (M : ProEtale.AdicSheaf l T)
    (h : ProEtale.IsIrreducibleAdicLocalSystem ((v)^*ᵃ[l].obj M)) :
    ProEtale.IsIrreducibleAdicLocalSystem ((u)^*ᵃ[l].obj M) := by
  apply isIrreducibleAdicLocalSystem_of_iso_pullback z
  let e : (z.hom)^*ᵃ[l].obj ((u)^*ᵃ[l].obj M) ≅ (v)^*ᵃ[l].obj M :=
    (ProEtale.adicUpperStarComp l z.hom u).symm.app M ≪≫
      (ProEtale.adicUpperStarCongr l hz).app M
  exact h.of_iso e.symm

-- Consumers use the carrier equations and exactness API rather than expanding the
-- iterated Frobenius construction during unification and kernel checking.
attribute [irreducible] poweredGeometricPullbackCommIso poweredGeometricPullbackAll
  poweredGeometricPullback

end AlgebraicGeometry.WeilSheaf
