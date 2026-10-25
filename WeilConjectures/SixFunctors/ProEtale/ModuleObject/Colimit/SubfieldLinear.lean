/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Linear
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.LiftLinear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-!
# Scalar multiplication by a finite subextension on `F_X`-modules

Let `Λ` be a commutative condensed ring and `φ : K →+* Γ Λ` a ring homomorphism to its global
sections. For a scheme `X`, the pullback `p_X^*` sends `φ a` to a constant global section of
`Λ_X = p_X^* Λ` (`ProEtale.CondensedRing.constRingHom`), so the category of `Λ_X`-module objects
is `K`-linear (`ProEtale.CondensedRing.modLinear`, by `Mod.linearOfRingHom`). The coefficient
morphism `η_f : Λ_Y ⟶ f_* Λ_X` sends constant global sections to constant global sections
(`ProEtale.CondensedRing.constRingHom_hom_comp_condensedPushforwardHom`), hence the pushforward
`f_*` of module objects is `K`-linear (`ProEtale.CondensedRing.linear_lowerStar`), and so are the
derived pushforward `Rf_*` (`ProEtale.CondensedRing.linear_rightDerivedLowerStar`) and its
restriction `Rg_*` to bounded constructible complexes
(`ProEtale.CondensedRing.linear_boundedConstructibleLowerStar`).

For a finite subextension `F ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and `Λ = F̲`, the constant global sections
`F →+* Γ F̲` give the `F`-linear structure on `F_X`-module objects
(`ProEtale.CondensedRing.padicSubfieldModLinear`, a scoped instance), hence on their derived
category and on `Dᵇc(X)⟦F̲⟧`: the scalar `b ∈ F` acts on every object by a natural endomorphism
of the identity functor, and `Rg_*` commutes with it
(`ProEtale.CondensedRing.boundedConstructibleLowerStar_map_smul_id`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

/-- The inverse image `p_X^*` from condensed abelian groups to abelian sheaves on `X_proét` is
additive, being a left adjoint. -/
theorem upperStarFromPoint_additive (X : Scheme.{u}) : (upperStarFromPoint X).Additive := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  exact Functor.additive_of_preservesBinaryBiproducts _

section General

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {K : Type*} [Ring K] (φ : K →+* Γ Λ)

/-- The constant global sections of `Λ_X = p_X^* Λ`: a ring homomorphism `K →+* Γ Λ` to the
global sections of the condensed ring `Λ`, followed by the pullback `p_X^*`. -/
noncomputable def constRingHom (X : Scheme.{u}) : K →+* Γ (condensedRingObj Λ X) :=
  haveI := upperStarFromPoint_additive X
  (Γ.mapFunctor (upperStarFromPoint X)).comp φ

lemma constRingHom_hom (X : Scheme.{u}) (a : K) :
    (constRingHom Λ φ X a).hom =
      Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map (φ a).hom :=
  rfl

/-- The `K`-linear structure on `Λ_X`-module objects, `a : K` acting through the constant global
section `p_X^* (φ a)` of `Λ_X`. -/
noncomputable abbrev modLinear (X : Scheme.{u}) :
    Linear K (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  Mod.linearOfRingHom (constRingHom Λ φ X)

/-- The coefficient morphism `η_f : Λ_Y ⟶ f_* Λ_X` sends constant global sections to constant
global sections. -/
lemma constRingHom_hom_comp_condensedPushforwardHom {X Y : Scheme.{u}} (f : X ⟶ Y) (a : K) :
    (constRingHom Λ φ Y a).hom ≫ condensedPushforwardHom Λ f =
      Functor.LaxMonoidal.ε (f)_*[Ab.{u + 1}] ≫
        (f)_*[Ab.{u + 1}].map (constRingHom Λ φ X a).hom := by
  rw [constRingHom_hom, constRingHom_hom, Category.assoc, condensedPushforwardHom]
  exact Adjunction.ε_comp_map_comp_unit_app_comp_map _ _ _ (upperStarFromPointComp f).hom _

/-- The pushforward `f_*` of module objects over `Λ` is `K`-linear. -/
lemma linear_lowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := modLinear Λ φ X
    letI := modLinear Λ φ Y
    ((f)_*⟦Λ⟧).Linear K :=
  Mod.linear_mapMod_comp_comap _ _ (constRingHom Λ φ X) (constRingHom Λ φ Y)
    (constRingHom_hom_comp_condensedPushforwardHom Λ φ f)

/-- The derived pushforward `Rf_*` of module objects over `Λ` is `K`-linear. -/
lemma linear_rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := modLinear Λ φ X
    letI := modLinear Λ φ Y
    (R((f)_*⟦Λ⟧)).Linear K :=
  letI := modLinear Λ φ X
  letI := modLinear Λ φ Y
  haveI := linear_lowerStar Λ φ f
  Functor.linear_rightDerivedFunctor K _

/-- On the derived category, the action of `a : K` on (the image of) a complex `M` of
`Λ_X`-module objects is the image of the action of the constant global section `p_X^* (φ a)` in
each degree. -/
lemma smul_id_Q_obj {X : Scheme.{u}}
    (M : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) (a : K) :
    letI := modLinear Λ φ X
    a • 𝟙 (DerivedCategory.Q.obj M) = DerivedCategory.Q.map
      ((HomologicalComplex.Hom.mk (fun n ↦ Mod.smulEnd (constRingHom Λ φ X a) (M.X n))
        fun _ _ _ ↦ Mod.hom_ext _ _ (Mod.smulHom_naturality _ _)) : M ⟶ M) := by
  let _ := modLinear Λ φ X
  rw [← DerivedCategory.Q.map_id, ← Functor.map_smul]
  congr 1

variable (ℓ : ℕ) [Fact ℓ.Prime] [IsFinitenessCoefficient ℓ Λ] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (g : Z ⟶ Y)

/-- The derived pushforward `Rg_* : Dᵇc(Z)⟦Λ⟧ ⥤ Dᵇc(Y)⟦Λ⟧` on bounded constructible complexes is
`K`-linear. -/
lemma linear_boundedConstructibleLowerStar :
    letI := modLinear Λ φ Z.left
    letI := modLinear Λ φ Y.left
    (boundedConstructibleLowerStar Λ ℓ g).Linear K :=
  letI := modLinear Λ φ Z.left
  letI := modLinear Λ φ Y.left
  haveI := linear_rightDerivedLowerStar Λ φ g.left
  ObjectProperty.lift_linear K _ _ _

end General

/-! ### Finite subextensions `F ⊆ ℚ̄_ℓ` -/

section Subfield

variable (ℓ : ℕ) [Fact ℓ.Prime] (F : FiniteIntermediateField ℓ)

/-- The constant global sections `F →+* Γ(F_X)` of the coefficient ring `F_X = p_X^* F̲`. -/
noncomputable def padicSubfieldConstRingHom (X : Scheme.{u}) :
    F →+* Γ (padicSubfieldRingObj X ℓ F) :=
  constRingHom _ (Profinite.continuousMapConstRingHom.{u} F) X

/-- The `F`-linear structure on `F_X`-module objects: `b : F` acts by multiplication by the
constant global section `b` of `F_X`. -/
@[instance_reducible]
noncomputable def padicSubfieldModLinear (X : Scheme.{u}) :
    Linear F (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) :=
  modLinear _ (Profinite.continuousMapConstRingHom.{u} F) X

attribute [scoped instance] padicSubfieldModLinear

/-- The action of `b ∈ F` on a morphism of `F_X`-module objects is the composition with the
multiplication by the constant global section `b`. -/
lemma padicSubfield_smul_hom (X : Scheme.{u}) (b : F)
    {M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)} (f : M ⟶ N) :
    (b • f).hom = f.hom ≫ Mod.smulHom (padicSubfieldConstRingHom ℓ F X b) N :=
  Mod.linearOfRingHom_smul_hom _ b f

/-- On the derived category of `F_X`-module objects, the action of `b ∈ F` on (the image of) a
complex `M` is the image of the multiplication by the constant global section `b` in each
degree. -/
lemma padicSubfield_smul_id_Q_obj {X : Scheme.{u}}
    (M : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ F)) ℤ) (b : F) :
    b • 𝟙 (DerivedCategory.Q.obj M) = DerivedCategory.Q.map
      ((HomologicalComplex.Hom.mk
        (fun n ↦ Mod.smulEnd (padicSubfieldConstRingHom ℓ F X b) (M.X n))
        fun _ _ _ ↦ Mod.hom_ext _ _ (Mod.smulHom_naturality _ _)) : M ⟶ M) :=
  smul_id_Q_obj _ (Profinite.continuousMapConstRingHom.{u} F) M b

variable {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (g : Z ⟶ Y)

/-- The pushforward `g_*` of `F_X`-module objects is `F`-linear. -/
instance linear_lowerStar_padicSubfield :
    ((g.left)_*⟦Profinite.continuousMapRingObj F⟧).Linear F :=
  linear_lowerStar _ (Profinite.continuousMapConstRingHom.{u} F) g.left

/-- The derived pushforward `Rg_*` of `F_X`-module objects is `F`-linear. -/
instance linear_rightDerivedLowerStar_padicSubfield :
    (R((g.left)_*⟦Profinite.continuousMapRingObj F⟧)).Linear F :=
  linear_rightDerivedLowerStar _ (Profinite.continuousMapConstRingHom.{u} F) g.left

/-- The derived pushforward `Rg_* : Dᵇc(Z)⟦F⟧ ⥤ Dᵇc(Y)⟦F⟧` on bounded constructible complexes is
`F`-linear. -/
instance linear_boundedConstructibleLowerStar_padicSubfield :
    (boundedConstructibleLowerStar (Profinite.continuousMapRingObj F) ℓ g).Linear F :=
  linear_boundedConstructibleLowerStar _ (Profinite.continuousMapConstRingHom.{u} F) ℓ g

/-- The derived pushforward `Rg_*` on bounded constructible complexes commutes with the
multiplication by a scalar `b ∈ F`. -/
lemma boundedConstructibleLowerStar_map_smul_id (b : F)
    (K : Dᵇc(Z.left)⟦Profinite.continuousMapRingObj F⟧) :
    (boundedConstructibleLowerStar (Profinite.continuousMapRingObj F) ℓ g).map (b • 𝟙 K) =
      b • 𝟙 _ :=
  ((boundedConstructibleLowerStar _ ℓ g).map_smul b (𝟙 K)).trans
    (congrArg (b • ·) ((boundedConstructibleLowerStar _ ℓ g).map_id K))

end Subfield

end AlgebraicGeometry.ProEtale.CondensedRing
