/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraUnit
public import WeilConjectures.WeilSheaf.LowerStarComp
public import WeilConjectures.WeilSheaf.UpperStarLowerStar

/-!
# The adjunction `φ^* ⊣ φ_*` of Weil sheaves

For a morphism `φ : X ⟶ Y` of `k₀`-schemes, the adjunction `φ̄^* ⊣ φ̄_*` of `ℓ`-adic pro-étale
sheaves along the base change `φ̄ : X̄ ⟶ Ȳ` has Weil-equivariant counit
(`AlgebraicGeometry.ProEtale.adicUpperStarLowerStarAdjunction_counit_frobenius`), hence also
Weil-equivariant unit. It therefore induces an adjunction `φ^* ⊣ φ_*` of pro-étale Weil sheaves,
and of Weil sheaves, with the same components. Along an open immersion its counit is invertible.

Composing adjunctions, the pullback along a composite is the composite of the pullbacks, the
pushforward along a composite being the composite of the pushforwards
(`AlgebraicGeometry.ProEtaleWeilSheaf.lowerStarCompIso`).

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.upperStarLowerStarAdjunction`: `φ^* ⊣ φ_*` on pro-étale
  Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.upperStarLowerStarAdjunction`: `φ^* ⊣ φ_*` on Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.lowerStarCompIso`: `φ_* ⋙ ψ_* ≅ (φ ≫ ψ)_*`.
- `AlgebraicGeometry.WeilSheaf.upperStarCompIso`: `(φ ≫ ψ)^* ≅ ψ^* ⋙ φ^*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace CategoryTheory.Adjunction

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

/-- The unit of an adjunction is invertible at `X` if and only if it is at an isomorphic `Y`. -/
lemma isIso_unit_app_iff_of_iso {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {X Y : C} (e : X ≅ Y) :
    IsIso (adj.unit.app X) ↔ IsIso (adj.unit.app Y) := by
  have h := adj.unit.naturality e.hom
  simp only [Functor.id_map, Functor.comp_map] at h
  constructor
  · intro
    have : IsIso (e.hom ≫ adj.unit.app Y) := by rw [h]; infer_instance
    exact IsIso.of_isIso_comp_left e.hom _
  · intro
    have : IsIso (adj.unit.app X ≫ R.map (L.map e.hom)) := by rw [← h]; infer_instance
    exact IsIso.of_isIso_comp_right _ (R.map (L.map e.hom))

/-- If the counit of an adjunction is invertible at `Y`, the unit is invertible at `R Y`. -/
instance isIso_unit_app_obj_of_isIso_counit_app {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (Y : D)
    [IsIso (adj.counit.app Y)] : IsIso (adj.unit.app (R.obj Y)) := by
  have h : adj.unit.app (R.obj Y) ≫ R.map (adj.counit.app Y) = 𝟙 _ :=
    adj.right_triangle_components Y
  have : IsIso (adj.unit.app (R.obj Y) ≫ R.map (adj.counit.app Y)) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right _ (R.map (adj.counit.app Y))

/-- If the counit of an adjunction is invertible at `L X`, the image under `L` of the unit at `X`
is invertible. -/
instance isIso_map_unit_app_of_isIso_counit_app {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (X : C)
    [IsIso (adj.counit.app (L.obj X))] : IsIso (L.map (adj.unit.app X)) := by
  have h : L.map (adj.unit.app X) ≫ adj.counit.app (L.obj X) = 𝟙 _ :=
    adj.left_triangle_components X
  have : IsIso (L.map (adj.unit.app X) ≫ adj.counit.app (L.obj X)) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right _ (adj.counit.app (L.obj X))

/-- Let `L ⊣ R` be an adjunction whose right adjoint is a composite `R ≅ R₂ ⋙ R₁` of right
adjoints of `L₁ ⊣ R₁` and `L₂ ⊣ R₂`. If the unit of `L₁ ⊣ R₁` is invertible at `X` and the unit
of `L₂ ⊣ R₂` is invertible at `L₁ X`, then the unit of `L ⊣ R` is invertible at `X`. -/
lemma isIso_unit_app_of_iso_comp {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    {L : C ⥤ E} {R : E ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R)
    (e : R₂ ⋙ R₁ ≅ R) (X : C) [IsIso (adj₁.unit.app X)] [IsIso (adj₂.unit.app (L₁.obj X))] :
    IsIso (adj.unit.app X) := by
  set adj' := (adj₁.comp adj₂).ofNatIsoRight e
  have h := Adjunction.unit_leftAdjointUniq_hom_app adj adj' X
  have h₁ := adj'.homEquiv_id X
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id,
    Adjunction.comp_unit_app] at h₁
  have : IsIso (adj'.unit.app X) := by
    rw [← h₁]
    infer_instance
  rw [← h] at this
  exact IsIso.of_isIso_comp_right _ (R.map ((adj.leftAdjointUniq adj').hom.app X))

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {X Y Z : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- **The unit of `φ̄^* ⊣ φ̄_*` is Frobenius-equivariant**: this follows formally from the
equivariance of the counit. -/
theorem ProEtale.adicUpperStarLowerStarAdjunction_unit_frobenius :
    IsoAlgebra.UnitCompatible
      (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ (Spec (CommRingCat.of k₀))))
      (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ (Spec (CommRingCat.of k₀))))
      (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ
        (comp_over φ (Spec (CommRingCat.of k₀))))).unit :=
  IsoAlgebra.unitCompatible_of_counitCompatible _
    (ProEtale.adicUpperStarLowerStarAdjunction_counit_frobenius φ)

variable (k₀ l) in
/-- The unit `𝟭 ⟶ φ^* ⋙ φ_*` of pro-étale Weil sheaves: the unit of `φ̄^* ⊣ φ̄_*`, which is
compatible with the Weil structures. -/
noncomputable def ProEtaleWeilSheaf.upperStarCompLowerStarUnit :
    𝟭 (ProEtaleWeilSheaf k₀ l Y) ⟶
      ProEtaleWeilSheaf.upperStar k₀ l φ ⋙ ProEtaleWeilSheaf.lowerStar k₀ l φ :=
  IsoAlgebra.mapOfNatIsoCompUnit
    (adicLowerStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ (Spec (CommRingCat.of k₀))))
    (adicUpperStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ (Spec (CommRingCat.of k₀))))
    (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ
      (comp_over φ (Spec (CommRingCat.of k₀))))).unit
    (ProEtale.adicUpperStarLowerStarAdjunction_unit_frobenius φ)

variable (k₀ l) in
/-- **The adjunction `φ^* ⊣ φ_*` of pro-étale Weil sheaves**: the unit and the counit of the
adjunction `φ̄^* ⊣ φ̄_*` along the base change are Weil-equivariant. -/
noncomputable def ProEtaleWeilSheaf.upperStarLowerStarAdjunction :
    ProEtaleWeilSheaf.upperStar k₀ l φ ⊣ ProEtaleWeilSheaf.lowerStar k₀ l φ :=
  { unit := ProEtaleWeilSheaf.upperStarCompLowerStarUnit k₀ l φ
    counit := ProEtaleWeilSheaf.lowerStarCompUpperStarCounit k₀ l φ
    left_triangle_components K := ObjectProperty.hom_ext _ (Algebra.Hom.ext
      ((adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ
        (comp_over φ (Spec (CommRingCat.of k₀))))).left_triangle_components K.carrier))
    right_triangle_components K := ObjectProperty.hom_ext _ (Algebra.Hom.ext
      ((adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ
        (comp_over φ (Spec (CommRingCat.of k₀))))).right_triangle_components K.carrier)) }

@[simp]
lemma ProEtaleWeilSheaf.upperStarLowerStarAdjunction_unit_app_hom_f
    (K : ProEtaleWeilSheaf k₀ l Y) :
    ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).unit.app K).hom.f =
      (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ
        (comp_over φ (Spec (CommRingCat.of k₀))))).unit.app K.carrier :=
  rfl

@[simp]
lemma ProEtaleWeilSheaf.upperStarLowerStarAdjunction_counit_app_hom_f
    (K : ProEtaleWeilSheaf k₀ l X) :
    ((ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).counit.app K).hom.f =
      (adicUpperStarLowerStarAdjunction l (Scheme.Hom.geometricFiberMap φ
        (comp_over φ (Spec (CommRingCat.of k₀))))).counit.app K.carrier :=
  rfl

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)]

section

variable [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

omit [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] in
/-- The pullback of Weil sheaves is the pullback of pro-étale Weil sheaves. -/
noncomputable def upperStarCompιIso :
    WeilSheaf.upperStar φ ⋙ (WeilSheaf.objectProperty k₀ l X).ι ≅
      (WeilSheaf.objectProperty k₀ l Y).ι ⋙ ProEtaleWeilSheaf.upperStar k₀ l φ :=
  ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _

/-- The pushforward of Weil sheaves is the pushforward of pro-étale Weil sheaves. -/
noncomputable def lowerStarCompιIso :
    WeilSheaf.lowerStar φ ⋙ (WeilSheaf.objectProperty k₀ l Y).ι ≅
      (WeilSheaf.objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.lowerStar k₀ l φ :=
  ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _

/-- **The adjunction `φ^* ⊣ φ_*` of Weil sheaves**, restricted from the adjunction of pro-étale
Weil sheaves. -/
noncomputable def upperStarLowerStarAdjunction :
    WeilSheaf.upperStar (k₀ := k₀) (l := l) φ ⊣ WeilSheaf.lowerStar φ :=
  (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l φ).restrictFullyFaithful
    (WeilSheaf.objectProperty k₀ l Y).fullyFaithfulι
    (WeilSheaf.objectProperty k₀ l X).fullyFaithfulι (upperStarCompιIso φ).symm
    (lowerStarCompιIso φ).symm

/-- Along an open immersion `j`, the counit `j^* j_* ⟶ 𝟭` of Weil sheaves is an isomorphism: the
direct image `j_*` is fully faithful, as `j^* j_* ≅ 𝟭`
(`AlgebraicGeometry.WeilSheaf.lowerStarCompUpperStarIso`). -/
instance isIso_upperStarLowerStarAdjunction_counit [IsOpenImmersion φ] :
    IsIso (upperStarLowerStarAdjunction (k₀ := k₀) (l := l) φ).counit := by
  let h := (upperStarLowerStarAdjunction (k₀ := k₀) (l := l) φ).fullyFaithfulROfCompIsoId
    (lowerStarCompUpperStarIso φ)
  have := h.full
  have := h.faithful
  infer_instance

instance isIso_upperStarLowerStarAdjunction_counit_app [IsOpenImmersion φ]
    (F : WeilSheaf k₀ l X) : IsIso ((upperStarLowerStarAdjunction φ).counit.app F) :=
  inferInstance

end

variable [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  (ψ : Y ⟶ Z) [ψ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact ψ] [QuasiSeparated ψ]
  [LocallyOfFiniteType ψ] [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]

/-- The composition isomorphism `φ_* ⋙ ψ_* ≅ (φ ≫ ψ)_*` of pushforwards of Weil sheaves. -/
noncomputable def lowerStarCompIso :
    WeilSheaf.lowerStar φ ⋙ WeilSheaf.lowerStar ψ ≅
      WeilSheaf.lowerStar (k₀ := k₀) (l := l) (φ ≫ ψ) :=
  ((WeilSheaf.objectProperty k₀ l Z).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (lowerStarCompιIso ψ) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (lowerStarCompιIso φ) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.lowerStarCompIso k₀ l φ ψ) ≪≫
      (lowerStarCompιIso (φ ≫ ψ)).symm)

/-- The pullback along a composite is the composite of the pullbacks: both are left adjoint to
the pushforward along the composite. -/
noncomputable def upperStarCompIso :
    WeilSheaf.upperStar (φ ≫ ψ) ≅
      WeilSheaf.upperStar ψ ⋙ WeilSheaf.upperStar (k₀ := k₀) (l := l) φ :=
  (upperStarLowerStarAdjunction (φ ≫ ψ)).leftAdjointUniq
    (((upperStarLowerStarAdjunction ψ).comp (upperStarLowerStarAdjunction φ)).ofNatIsoRight
      (lowerStarCompIso φ ψ))

end WeilSheaf

end AlgebraicGeometry
