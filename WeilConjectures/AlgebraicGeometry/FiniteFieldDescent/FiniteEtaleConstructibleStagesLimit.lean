/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldDescent.FiniteEtaleConstructibleStages
public import WeilConjectures.AlgebraicGeometry.FieldExtensionLimit
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # The finite stages of an algebraic extension as an inverse system

For `Y → Spec K` and an algebraic extension `L/K`, the base changes `Y_E` over the finite
subextensions `E` of `L/K` form a directed inverse system with affine transitions, whose limit
is `Y_L`; the limit projections `Y_L ⟶ Y_E` are surjective.

Source: Stacks Project, Lemma 09YU (3) (the system of finite subextensions)
(blueprint: new-sfb-finite-etale-constructible-object-descent).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Etale.FiniteFieldDescent

variable {K : Type u} [Field K] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K))

/-- The transition attached to the identity is the identity.
Source: Stacks Lemma 09YU (3). -/
lemma projection_id (A : Type u) [Field A] [Algebra K A] :
    projection f (AlgHom.id K A) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [projection]

/-- Transitions compose contravariantly.
Source: Stacks Lemma 09YU (3). -/
lemma projection_comp {A B C : Type u} [Field A] [Field B] [Field C] [Algebra K A]
    [Algebra K B] [Algebra K C] (h : A →ₐ[K] B) (i : B →ₐ[K] C) :
    projection f (i.comp h) = projection f i ≫ projection f h := by
  apply pullback.hom_ext
  · simp [projection, Category.assoc]
  · simp only [projection, pullback.lift_snd, Category.assoc, pullback.lift_snd_assoc,
      ← Spec.map_comp]
    rfl

variable (L : Type u) [Field L] [Algebra K L]

/-- The finite stages `E ↦ Y_E` over the finite subextensions `E` of `L/K`.
Source: Stacks Lemma 09YU (3). -/
@[simps]
noncomputable def stageDiagram : (IntermediateField.FiniteSubext K L)ᵒᵖ ⥤ Scheme.{u} where
  obj E := scheme f E.unop.1
  map {E E'} h := projection f (IntermediateField.inclusion (leOfHom h.unop))
  map_id E := by
    rw [← projection_id f E.unop.1]
    congr 1
  map_comp {E E' E''} h h' := by
    rw [← projection_comp]
    rfl

/-- The structure morphism `Y_A ⟶ Spec A` of a stage. -/
noncomputable abbrev toSpec (A : Type u) [Field A] [Algebra K A] : scheme f A ⟶ Spec (.of A) :=
  pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K A)))

/-- A transition `Y_B ⟶ Y_A` is the base change of `Spec B ⟶ Spec A`. -/
lemma isPullback_projection {A B : Type u} [Field A] [Field B] [Algebra K A] [Algebra K B]
    (h : A →ₐ[K] B) :
    IsPullback (projection f h) (toSpec f B) (toSpec f A)
      (Spec.map (CommRingCat.ofHom h.toRingHom)) :=
  isPullback_pullback_map f _ _ _ (by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact h.commutes x)

/-- `Y_L` as a cone over the finite stages.
Source: Stacks Lemma 09YU (3). -/
@[simps]
noncomputable def stageCone : Cone (stageDiagram f L) where
  pt := scheme f L
  π :=
    { app E := projection f (IntermediateField.val E.unop.1)
      naturality {E _} h :=
        (Category.id_comp _).trans (projection_comp f
          (IntermediateField.inclusion (leOfHom h.unop)) (IntermediateField.val E.unop.1)) }

/-- The projections `Y_E ⟶ Spec E` form a natural transformation to the spectra of the finite
subextensions. -/
noncomputable def stageDiagramToSpec :
    stageDiagram f L ⟶ (IntermediateField.subextDiagram K L).op ⋙ Scheme.Spec where
  app E := toSpec f E.unop.1
  naturality {_ _} h :=
    (isPullback_projection f (IntermediateField.inclusion (leOfHom h.unop))).w

/-- `Y_L` is the limit of the finite stages `Y_E`: it is the base change of
`Spec L = lim Spec E`.
Source: Stacks Lemma 09YU (3). -/
noncomputable def isLimitStageCone [Algebra.IsAlgebraic K L] : IsLimit (stageCone f L) := by
  have := IsCofiltered.isConnected (IntermediateField.FiniteSubext K L)ᵒᵖ
  exact isLimitOfIsPullbackOfIsConnected (stageDiagramToSpec f L) _ (subextSpecCone K L)
    { hom := toSpec f L
      w E := (isPullback_projection f (IntermediateField.val E.unop.1)).w.symm }
    (fun E ↦ isPullback_projection f (IntermediateField.val E.unop.1))
    (isLimitSubextSpecCone K L)

instance {E E' : (IntermediateField.FiniteSubext K L)ᵒᵖ} (h : E ⟶ E') :
    IsAffineHom ((stageDiagram f L).map h) := by
  have : IsAffineHom (Spec.map (CommRingCat.ofHom
      (IntermediateField.inclusion (leOfHom h.unop)).toRingHom)) :=
    isAffineHom_of_isAffine _
  exact MorphismProperty.of_isPullback
    (isPullback_projection f (IntermediateField.inclusion (leOfHom h.unop))).flip this

instance [QuasiCompact f] (E : (IntermediateField.FiniteSubext K L)ᵒᵖ) :
    CompactSpace ((stageDiagram f L).obj E) :=
  QuasiCompact.compactSpace_of_compactSpace (toSpec f E.unop.1)

instance [IsSeparated f] (E : (IntermediateField.FiniteSubext K L)ᵒᵖ) :
    QuasiSeparatedSpace ((stageDiagram f L).obj E) :=
  quasiSeparatedSpace_of_quasiSeparated (toSpec f E.unop.1)

/-- The limit projections `Y_L ⟶ Y_E` are surjective, being base changes of the surjections
`Spec L ⟶ Spec E`.
Source: Stacks Lemma 09YU (3). -/
lemma surjective_stageCone_π_app (E : (IntermediateField.FiniteSubext K L)ᵒᵖ) :
    Function.Surjective ((stageCone f L).π.app E).base := by
  have : Surjective (Spec.map (CommRingCat.ofHom (IntermediateField.val E.unop.1).toRingHom)) :=
    ⟨fun _ ↦ ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  exact (MorphismProperty.of_isPullback (P := @Surjective)
    (isPullback_projection f (IntermediateField.val E.unop.1)).flip this).surj

end AlgebraicGeometry.Etale.FiniteFieldDescent
