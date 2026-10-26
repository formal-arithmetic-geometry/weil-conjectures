/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.Sections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ConstantPresentation

/-!
# Finitely presented module objects are Zariski locally constant

Let `T` be a finite discrete commutative ring and `P` a finitely presented module object over
`Λ_Y = p_Y^* T̲`, the cokernel of `φ : Λ_Yᵐ ⟶ Λ_Yⁿ`. The matrix entries of `φ` are global sections
of `Λ_Y`, that is continuous maps `Y → T` (`ProEtale.finiteSectionRingHom_bijective`). As `T` is
finite and discrete, `Y` is covered by the finitely many open subschemes `V_c` on which the matrix
of `φ` is a given constant matrix `c` over `T`. On `V_c` the presentation of `P` pulls back to the
constant matrix `c`, so that the sheaf of `T`-modules corresponding to `P|_{V_c}` is the constant
sheaf on the finite `T`-module `coker c`
(`ProEtale.exists_opens_iso_constantSheaf_of_isFinitelyPresented`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable {T : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- The open subset of `Y` on which the continuous maps `f j i : Y → T` take the values `c j i`. -/
def matrixLevelOpens {Y : Scheme.{u}} {m n : ℕ} (f : Fin m → Fin n → C(Y, T))
    (c : Fin m → Fin n → T) : Y.Opens :=
  ⟨{y | ∀ j i, f j i y = c j i}, by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦ isOpen_iInter_of_finite fun i ↦
      (isOpen_discrete {c j i}).preimage (f j i).continuous⟩

omit [CommRing T] [IsTopologicalRing T] [Finite T] in
/-- On `V_c = matrixLevelOpens f c`, the restriction of `f j i` is the constant map `c j i`. -/
lemma comp_matrixLevelOpens_ι {Y : Scheme.{u}} {m n : ℕ} (f : Fin m → Fin n → C(Y, T))
    (c : Fin m → Fin n → T) (j : Fin m) (i : Fin n) :
    (f j i).comp (matrixLevelOpens f c).ι.base.hom = ContinuousMap.const _ (c j i) :=
  ContinuousMap.ext fun y ↦ y.2 j i

omit [Finite T] in
/-- The pullback along `g : W ⟶ Y` of the multiplication by the global section of `Λ_Y` given by
a continuous map `f : Y → T` is the multiplication by the global section given by `f ∘ g`. -/
lemma restrictEnd_regularEndRingHom_finiteSectionRingHom {W Y : Scheme.{u}} (g : W ⟶ Y)
    (f : C(Y, T)) :
    restrictEnd (Profinite.continuousMapRingObj.{u} T) g
        (Mod.regularEndRingHom (finiteSectionRingHom Y T f)) =
      Mod.regularEndRingHom (finiteSectionRingHom W T (f.comp g.base.hom)) := by
  rw [restrictEnd_regularEndRingHom, Γ_map_condensedPullbackHom_finiteSectionRingHom]

omit [Finite T] in
/-- Let `φ : Λ_Yᵐ ⟶ Λ_Yⁿ` have matrix entries given by continuous maps `f j i : Y → T`. If
`f j i ∘ g` is the constant map `t j i` for `g : W ⟶ Y`, then the pullback of `φ` along `g`,
transported along `g^* Λ_Y ≅ Λ_W`, has the constant matrix entries `t j i`. -/
lemma ι_upperStar_map_π_of_comp_eq_const {W Y : Scheme.{u}} (g : W ⟶ Y) {m n : ℕ}
    (φ : Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj T) Y) m ⟶
      Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj T) Y) n)
    (f : Fin m → Fin n → C(Y, T))
    (hf : ∀ j i, Mod.regularEndRingHom (finiteSectionRingHom Y T (f j i)) =
      biproduct.ι (fun _ : Fin m ↦ Mod.regular (condensedRingObj
          (Profinite.continuousMapRingObj T) Y)) j ≫ φ ≫
        biproduct.π (fun _ : Fin n ↦ Mod.regular (condensedRingObj
          (Profinite.continuousMapRingObj T) Y)) i)
    (t : Fin m → Fin n → T) (ht : ∀ j i, (f j i).comp g.base.hom = ContinuousMap.const W (t j i))
    (j : Fin m) (i : Fin n) :
    biproduct.ι (fun _ : Fin m ↦ Mod.regular (condensedRingObj
        (Profinite.continuousMapRingObj T) W)) j ≫
      ((g)^*⟦Profinite.continuousMapRingObj.{u} T⟧.mapBiproductPowIso
        (upperStarObjRegularIso (Profinite.continuousMapRingObj.{u} T) g) m).inv ≫
      (g)^*⟦Profinite.continuousMapRingObj.{u} T⟧.map φ ≫
      ((g)^*⟦Profinite.continuousMapRingObj.{u} T⟧.mapBiproductPowIso
        (upperStarObjRegularIso (Profinite.continuousMapRingObj.{u} T) g) n).hom ≫
      biproduct.π (fun _ : Fin n ↦ Mod.regular (condensedRingObj
        (Profinite.continuousMapRingObj T) W)) i =
      Mod.regularLift (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj T) W))
        (constSection W (t j i)).hom := by
  rw [Functor.ι_mapBiproductPowIso_inv_map_hom_π, ← hf, ← restrictEnd_apply,
    restrictEnd_regularEndRingHom_finiteSectionRingHom, ht, finiteSectionRingHom_const,
    Mod.regularEndRingHom_apply]

/-- **Finitely presented module objects over `Λ_Y` are Zariski locally constant**: there is a
finite open cover `V_c` of `Y` such that the sheaf of `T`-modules corresponding to the restriction
of `P` to each `V_c` is the constant sheaf on a finite `T`-module. -/
theorem exists_opens_iso_constantSheaf_of_isFinitelyPresented {Y : Scheme.{u}}
    {P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) Y)}
    (hP : Mod.IsFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj T) Y) P) :
    ∃ (κ : Type) (_ : Finite κ) (V : κ → Y.Opens), (∀ y, ∃ c, y ∈ V c) ∧
      ∀ c, ∃ M : ModuleCat.{u + 1} (ULift.{u + 1} T), Finite M ∧
        Nonempty ((finiteCoefficientModEquivalence (V c) T).functor.obj
          (((V c).ι)^*⟦Profinite.continuousMapRingObj.{u} T⟧.obj P) ≅
          (constantSheaf (Scheme.ProEt.topology (V c)) (ModuleCat.{u + 1} (ULift.{u + 1} T))).obj
            M) := by
  obtain ⟨n, m, φ, ⟨e⟩⟩ := hP
  have hsurj (x : End (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj T) Y))) :
      ∃ f : C(Y, T), Mod.regularEndRingHom (finiteSectionRingHom Y T f) = x := by
    obtain ⟨s, rfl⟩ := Mod.regularEndRingHom_bijective.2 x
    obtain ⟨f, rfl⟩ := (finiteSectionRingHom_bijective Y T).2 s
    exact ⟨f, rfl⟩
  choose f hf using fun j i ↦ hsurj
    (biproduct.ι (fun _ : Fin m ↦ Mod.regular (condensedRingObj
        (Profinite.continuousMapRingObj T) Y)) j ≫ φ ≫
      biproduct.π (fun _ : Fin n ↦ Mod.regular (condensedRingObj
        (Profinite.continuousMapRingObj T) Y)) i)
  refine ⟨Fin m → Fin n → T, inferInstance, matrixLevelOpens f, fun y ↦ ⟨fun j i ↦ f j i y,
    fun j i ↦ rfl⟩, fun c ↦ ?_⟩
  obtain ⟨M, hM, ⟨e'⟩⟩ := exists_iso_constantSheaf_of_constant_matrix (matrixLevelOpens f c)
    (φ := (((matrixLevelOpens f c).ι)^*⟦Profinite.continuousMapRingObj.{u} T⟧.mapBiproductPowIso
        (upperStarObjRegularIso (Profinite.continuousMapRingObj.{u} T) _) m).inv ≫
      ((matrixLevelOpens f c).ι)^*⟦Profinite.continuousMapRingObj.{u} T⟧.map φ ≫
      (((matrixLevelOpens f c).ι)^*⟦Profinite.continuousMapRingObj.{u} T⟧.mapBiproductPowIso
        (upperStarObjRegularIso (Profinite.continuousMapRingObj.{u} T) _) n).hom) c
    fun j i ↦ by
      simp only [Category.assoc]
      exact ι_upperStar_map_π_of_comp_eq_const _ φ f hf c (comp_matrixLevelOpens_ι f c) j i
  exact ⟨M, hM, ⟨(finiteCoefficientModEquivalence _ T).functor.mapIso
    (((matrixLevelOpens f c).ι)^*⟦Profinite.continuousMapRingObj.{u} T⟧.mapIso e ≪≫
      PreservesCokernel.iso _ φ ≪≫ cokernel.mapIso _ _
        (((matrixLevelOpens f c).ι)^*⟦Profinite.continuousMapRingObj.{u} T⟧.mapBiproductPowIso
          (upperStarObjRegularIso (Profinite.continuousMapRingObj.{u} T) _) m)
        (((matrixLevelOpens f c).ι)^*⟦Profinite.continuousMapRingObj.{u} T⟧.mapBiproductPowIso
          (upperStarObjRegularIso (Profinite.continuousMapRingObj.{u} T) _) n) (by simp)) ≪≫ e'⟩⟩

end AlgebraicGeometry.ProEtale
