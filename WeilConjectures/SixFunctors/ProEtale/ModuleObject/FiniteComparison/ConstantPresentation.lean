/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularCorepresentable
public import WeilConjectures.CategoryTheory.Preadditive.FinitePowerMatrixMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Constant presentations give constant sheaves

Let `T` be a finite discrete commutative ring, `V` a scheme and `Φ_V` the identification of
module objects over `Λ_V = p_V^* T̲` with sheaves of `T`-modules on `V_proét`
(`finiteCoefficientModEquivalence`).

* `Φ_V Λ_V` is the constant sheaf `T` (`ProEtale.finiteCoefficientModEquivalenceRegularIso`):
  both corepresent the global sections.
* The multiplication by the constant global section `t` on `Λ_V` goes to the multiplication
  by `t` (`ProEtale.finiteCoefficientModEquivalence_map_regularLift_constSection`).
* Hence the cokernel of a morphism `Λ_Vᵐ ⟶ Λ_Vⁿ` whose matrix entries are constant global
  sections `tⱼᵢ ∈ T` goes to the constant sheaf on the cokernel of the matrix `(tⱼᵢ)`, a finite
  `T`-module (`ProEtale.exists_iso_constantSheaf_of_constant_matrix`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] {A : C} [MonObj A]
  [IsCommMonObj A]

/-- For a commutative monoid object `A`, the multiplication by a global section `σ` on the
regular module, `a ↦ a σ`, is the action of `σ`, `a ↦ σ a`. -/
lemma regularLift_hom_eq_globalSmul (σ : 𝟙_ C ⟶ A) :
    (regularLift (regular A) σ).hom = globalSmul σ (regular A) := by
  have h₁ : (regularLift (regular A) σ).hom = (ρ_ A).inv ≫ A ◁ σ ≫ μ[A] := rfl
  have h₂ : globalSmul σ (regular A) = (λ_ A).inv ≫ σ ▷ A ≫ μ[A] := rfl
  rw [h₁, h₂]
  conv_lhs => rw [← IsCommMonObj.mul_comm A]
  rw [BraidedCategory.braiding_naturality_right_assoc, rightUnitor_inv_braiding_assoc]

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (V : Scheme.{u}) {T : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

/-- The multiplication by the constant global section `t` on the regular module `Λ_V` is sent by
`Φ_V` to the multiplication by `t`. -/
lemma finiteCoefficientModEquivalence_map_regularLift_constSection (t : T) :
    (finiteCoefficientModEquivalence V T).functor.map
        (Mod.regularLift (Mod.regular _) (constSection V t).hom) =
      Sheaf.smulEnd (ULift.up t)
        ((finiteCoefficientModEquivalence V T).functor.obj (Mod.regular _)) := by
  ext U y
  rw [Sheaf.smulEnd_hom_app_apply, finiteCoefficientModEquivalence_smul,
    ← Mod.regularLift_hom_eq_globalSmul]
  rfl

instance additive_constantSheaf_moduleCat :
    (constantSheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} T))).Additive := by
  have adj := constantSheafAdj (Scheme.ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} T))
    (ProEt.isTerminalMkId V)
  have : (constantSheaf (Scheme.ProEt.topology V)
      (ModuleCat.{u + 1} (ULift.{u + 1} T))).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint
    (constantSheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} T)))
  have : PreservesColimitsOfSize.{0, 0}
      (constantSheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} T))) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (constantSheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} T)))
  exact Functor.additive_of_preservesBinaryBiproducts _

instance preservesCokernels_constantSheaf_moduleCat :
    PreservesColimitsOfShape WalkingParallelPair
      (constantSheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} T))) :=
  have adj := constantSheafAdj (Scheme.ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} T))
    (ProEt.isTerminalMkId V)
  have : PreservesColimitsOfSize.{0, 0}
      (constantSheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} T))) :=
    adj.leftAdjoint_preservesColimits
  inferInstance

/-- The abelian sheaf underlying the constant sheaf `T` on `V_proét`. -/
noncomputable abbrev constantSheafUnderlying : Sheaf (Scheme.ProEt.topology V) Ab.{u + 1} :=
  (sheafCompose (Scheme.ProEt.topology V)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T)) AddCommGrpCat.{u + 1})).obj
      ((constantSheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj
        (ModuleCat.of (ULift.{u + 1} T) (ULift.{u + 1} T)))

/-- The unit section `𝟙 ⟶ T` of the constant sheaf `T` on `V_proét`. -/
noncomputable def constantSheafUnitHom :
    𝟙_ (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) ⟶ constantSheafUnderlying V (T := T) :=
  (Sheaf.unitHomEvalAddEquiv (ProEt.isTerminalMkId V) (constantSheafUnderlying V (T := T))).symm
    (Sheaf.constantSheafUnitSection (R := ULift.{u + 1} T) _ (ProEt.isTerminalMkId V))

omit [TopologicalSpace T] [IsTopologicalRing T] [DiscreteTopology T] [Finite T] in
/-- The constant sheaf `T` corepresents the global sections of the underlying abelian sheaf. -/
lemma bijective_constantSheafUnitHom_comp_map
    (G : Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} T))) :
    Function.Bijective (fun f : (constantSheaf (Scheme.ProEt.topology V)
        (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj
          (ModuleCat.of (ULift.{u + 1} T) (ULift.{u + 1} T)) ⟶ G ↦
      constantSheafUnitHom V ≫ (sheafCompose (Scheme.ProEt.topology V)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T)) AddCommGrpCat.{u + 1})).map f) := by
  rw [← (Function.Bijective.of_comp_iff' (Sheaf.unitHomEvalAddEquiv (ProEt.isTerminalMkId V)
    ((sheafCompose (Scheme.ProEt.topology V)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T)) AddCommGrpCat.{u + 1})).obj G)).bijective)]
  have h : (Sheaf.unitHomEvalAddEquiv (ProEt.isTerminalMkId V)
      ((sheafCompose (Scheme.ProEt.topology V)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T)) AddCommGrpCat.{u + 1})).obj G) ∘
      fun f : (constantSheaf (Scheme.ProEt.topology V)
        (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj
          (ModuleCat.of (ULift.{u + 1} T) (ULift.{u + 1} T)) ⟶ G ↦
        constantSheafUnitHom V ≫ (sheafCompose (Scheme.ProEt.topology V)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T)) AddCommGrpCat.{u + 1})).map f) =
      fun f ↦ f.hom.app (op (ProEt.mk (𝟙 V)))
        (Sheaf.constantSheafUnitSection (R := ULift.{u + 1} T) _ (ProEt.isTerminalMkId V)) := by
    funext f
    have hu : Sheaf.unitHomEval (F := constantSheafUnderlying V (T := T)) (ProEt.mk (𝟙 V))
        (constantSheafUnitHom V) =
        Sheaf.constantSheafUnitSection (R := ULift.{u + 1} T) _ (ProEt.isTerminalMkId V) :=
      (Sheaf.unitHomEvalAddEquiv (ProEt.isTerminalMkId V)
        (constantSheafUnderlying V (T := T))).apply_symm_apply _
    exact (Sheaf.unitHomEval_comp (F := constantSheafUnderlying V (T := T)) (ProEt.mk (𝟙 V))
      (constantSheafUnitHom V) ((sheafCompose (Scheme.ProEt.topology V)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T)) AddCommGrpCat.{u + 1})).map f)).trans
      (congrArg _ hu)
  rw [h]
  exact Sheaf.bijective_constantSheaf_hom_app (Scheme.ProEt.topology V) (ProEt.isTerminalMkId V) G

/-- The constant sheaf `T` corepresents the global sections of the underlying abelian sheaf. -/
noncomputable def constantSheafCorepresentableBy :
    (sheafCompose (Scheme.ProEt.topology V)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T)) AddCommGrpCat.{u + 1}) ⋙
      coyoneda.obj (op (𝟙_ (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})))).CorepresentableBy
      ((constantSheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj
        (ModuleCat.of (ULift.{u + 1} T) (ULift.{u + 1} T))) :=
  Functor.CorepresentableBy.ofBijective _ (constantSheafUnitHom V)
    (bijective_constantSheafUnitHom_comp_map V)

/-- `Φ_V Λ_V` corepresents the global sections of the underlying abelian sheaf. -/
noncomputable def regularCorepresentableBy :
    (sheafCompose (Scheme.ProEt.topology V)
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T)) AddCommGrpCat.{u + 1}) ⋙
      coyoneda.obj (op (𝟙_ (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})))).CorepresentableBy
      ((finiteCoefficientModEquivalence V T).functor.obj (Mod.regular _)) :=
  Functor.CorepresentableBy.ofBijective _ _
    (Mod.bijective_comp_map_regular (finiteCoefficientModEquivalence V T).functor _
      (eqToIso (finiteCoefficientModEquivalence_functor_comp_sheafCompose V T)))

/-- **`Φ_V Λ_V` is the constant sheaf `T`**: both corepresent the global sections of the
underlying abelian sheaf, through the unit sections. -/
noncomputable def finiteCoefficientModEquivalenceRegularIso :
    (finiteCoefficientModEquivalence V T).functor.obj (Mod.regular _) ≅
      (constantSheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj
        (ModuleCat.of (ULift.{u + 1} T) (ULift.{u + 1} T)) :=
  (regularCorepresentableBy V).uniqueUpToIso (constantSheafCorepresentableBy V)

/-- The cokernel of a morphism between finite powers of a finite module is finite. -/
lemma finite_cokernel_of_finite {R : Type*} [Ring R] (M : ModuleCat.{u + 1} R) [Finite M]
    {m n : ℕ} (f : (⨁ fun _ : Fin m ↦ M) ⟶ ⨁ fun _ : Fin n ↦ M) :
    Finite ((cokernel f : ModuleCat.{u + 1} R) : Type (u + 1)) := by
  have : Finite (((⨁ fun _ : Fin n ↦ M) : ModuleCat.{u + 1} R) : Type (u + 1)) :=
    Finite.of_equiv _ (ModuleCat.biproductIsoPi fun _ : Fin n ↦ M).toLinearEquiv.toEquiv.symm
  exact Finite.of_surjective _ ((ModuleCat.epi_iff_surjective (cokernel.π f)).1 inferInstance)

/-- **A presentation with constant matrix entries gives a constant sheaf.** If the matrix
entries of `φ : Λ_Vᵐ ⟶ Λ_Vⁿ` are the multiplications by constant global sections `tⱼᵢ ∈ T`,
then `Φ_V (coker φ)` is the constant sheaf on a finite `T`-module, the cokernel of the
matrix `(tⱼᵢ)`. -/
theorem exists_iso_constantSheaf_of_constant_matrix {m n : ℕ}
    (φ : Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj T) V) m ⟶
      Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj T) V) n)
    (t : Fin m → Fin n → T)
    (hφ : ∀ j i, biproduct.ι _ j ≫ φ ≫ biproduct.π _ i =
      Mod.regularLift (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj T) V))
        (constSection V (t j i)).hom) :
    ∃ M : ModuleCat.{u + 1} (ULift.{u + 1} T), Finite M ∧
      Nonempty ((finiteCoefficientModEquivalence V T).functor.obj (cokernel φ) ≅
        (constantSheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj M) := by
  have : HasFiniteBiproducts (Sheaf (Scheme.ProEt.topology V)
      (ModuleCat.{u + 1} (ULift.{u + 1} T))) := HasFiniteBiproducts.of_hasFiniteProducts
  let K := ModuleCat.of (ULift.{u + 1} T) (ULift.{u + 1} T)
  let y : Fin m → Fin n → (K ⟶ K) := fun j i ↦ (ULift.up (t j i) : ULift.{u + 1} T) • 𝟙 K
  refine ⟨cokernel (biproduct.matrix y), finite_cokernel_of_finite K _,
    ⟨Functor.cokernelIsoOfComponents _ _ (finiteCoefficientModEquivalenceRegularIso V) φ y
      fun j i ↦ ?_⟩⟩
  rw [hφ, finiteCoefficientModEquivalence_map_regularLift_constSection, ← Sheaf.comp_smulEnd,
    Iso.inv_hom_id_assoc, Sheaf.constantSheaf_map_smul (Scheme.ProEt.topology V)
      (ProEt.isTerminalMkId V) (ULift.up (t j i) : ULift.{u + 1} T) K]

end AlgebraicGeometry.ProEtale
