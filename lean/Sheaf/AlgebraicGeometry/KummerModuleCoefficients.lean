/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Module coefficients for the Kummer sheaf

Source: Stacks Project, Tags 03PK and 03EK; blueprint sk-prop-a1-kummer, Coefficients
(blueprint: def-pur-kummer-module-coefficients).

The twist is the sheafification of the sectionwise tensor of the existing roots-of-unity
module presheaf with a constant module presheaf. This is the sheaf tensor product with the
constant sheaf. Insertion of a coefficient is defined on sections before sheafification.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme

/-- The existing root module presheaf with a universe lift of its coefficient ring.
Source: Stacks, Tag 03PK (blueprint: def-pur-kummer-module-coefficients). -/
def kummerRootModulePresheaf (X : Scheme.{u}) (m : ℕ) :
    X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)) :=
  finiteEtaleMuModulePresheaf X m ⋙ ModuleCat.restrictScalars ULift.ringEquiv.toRingHom

/-- The coefficient functor `A ↦ μ_m ⊗ A_C`, by sectionwise tensor and sheafification.
Source: Stacks, Tags 03PK and 03EK (blueprint: def-pur-kummer-module-coefficients). -/
def kummerModuleTwist (X : Scheme.{u}) (m : ℕ) :
    ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) :=
  Functor.const X.Etaleᵒᵖ ⋙ tensorLeft (kummerRootModulePresheaf X m) ⋙
    presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))

/-- The underlying abelian coefficient functor.
Source: Stacks, Tag 03PK (blueprint: def-pur-kummer-module-coefficients). -/
def kummerAbelianTwist (X : Scheme.{u}) (m : ℕ) :
    ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)) ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kummerModuleTwist X m ⋙
    sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) AddCommGrpCat)

/-- Insertion of a coefficient into a local pure tensor, followed by sheafification.
Source: Stacks, Tag 03EK (blueprint: def-pur-kummer-module-coefficients). -/
def kummerCoefficientInsertionApp (X : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) (a : A) (U : X.Etaleᵒᵖ) :
    (X.rootsOfUnitySheaf m).obj.obj U →+
      ((kummerAbelianTwist X m).obj A).obj.obj U :=
  ((toSheafify X.smallEtaleTopology
    (kummerRootModulePresheaf X m ⊗ (Functor.const X.Etaleᵒᵖ).obj A)).app U).hom.toAddMonoidHom.comp
      ((TensorProduct.mk (ULift.{u + 1} (ZMod m))
        ((kummerRootModulePresheaf X m).obj U) A).flip a).toAddMonoidHom

/-- The insertion maps commute with restrictions.
Source: Stacks, Tag 03EK (blueprint: def-pur-kummer-module-coefficients).
Proof: tensor restriction sends `x ⊗ a` to `res(x) ⊗ a`. Naturality of the
sheafification unit then gives the asserted equality of additive maps. -/
theorem kummerCoefficientInsertion_naturality (X : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) (a : A) (U V : X.Etaleᵒᵖ) (f : U ⟶ V) :
    (X.rootsOfUnitySheaf m).obj.map f ≫
        AddCommGrpCat.ofHom (kummerCoefficientInsertionApp X m A a V) =
      AddCommGrpCat.ofHom (kummerCoefficientInsertionApp X m A a U) ≫
        ((kummerAbelianTwist X m).obj A).obj.map f := by
  ext x
  let P := kummerRootModulePresheaf X m ⊗ (Functor.const X.Etaleᵒᵖ).obj A
  have h := congrArg (fun g ↦ g.hom (TensorProduct.tmul _ x a))
    ((toSheafify X.smallEtaleTopology P).naturality f)
  change ((toSheafify X.smallEtaleTopology P).app V).hom
      ((P.map f).hom (TensorProduct.tmul _ x a)) =
    ((sheafify X.smallEtaleTopology P).map f).hom
      (((toSheafify X.smallEtaleTopology P).app U).hom (TensorProduct.tmul _ x a)) at h
  have hp : (P.map f).hom
      (TensorProduct.tmul _ (x : (kummerRootModulePresheaf X m).obj U) a) =
      TensorProduct.tmul _
        ((kummerRootModulePresheaf X m).map f x) a := by
    rfl
  rw [hp] at h
  exact h

/-- The canonical map `i_a : μ_m → μ_m ⊗ A_C`, `x ↦ x ⊗ a`.
Source: Stacks, Tags 03PK and 03EK (blueprint: def-pur-kummer-module-coefficients). -/
def kummerCoefficientInsertion (X : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) (a : A) :
    X.rootsOfUnitySheaf m ⟶ (kummerAbelianTwist X m).obj A :=
  ⟨{ app := fun U => AddCommGrpCat.ofHom (kummerCoefficientInsertionApp X m A a U)
     naturality := kummerCoefficientInsertion_naturality X m A a }⟩

/-- Roots-of-unity cohomology is killed by `m`, hence has its unique `ZMod m` action.
Source: Stacks, Tag 03PK (blueprint: def-pur-kummer-module-coefficients).
Proof: multiplication by m on the roots sheaf is zero by its kernel inclusion into G_m.
The additive cohomology functor sends this equality to multiplication by m equal to zero. -/
theorem kummerRootCohomology_annihilated (X : Scheme.{u}) (m q : ℕ)
    (x : Sheaf.H (X.rootsOfUnitySheaf m) q) : m • x = 0 := by
  have h : m • 𝟙 (X.rootsOfUnitySheaf m) = 0 := by
    change m • 𝟙 (kernel (m • 𝟙 X.gmSheaf)) = 0
    rw [← cancel_mono (kernel.ι (m • 𝟙 X.gmSheaf)), Preadditive.nsmul_comp,
      Category.id_comp, zero_comp, ← Category.comp_id (kernel.ι _),
      ← Preadditive.comp_nsmul, kernel.condition]
  have hx := congrArg (fun f ↦ Sheaf.H.map f q x) h
  rw [Sheaf.H.map_nsmul_apply, Sheaf.H.map_id_apply, Sheaf.H.map_apply,
    Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero] at hx
  exact hx

/-- The unique residue-ring action on roots-of-unity cohomology.
Source: Stacks, Tag 03PK (blueprint: def-pur-kummer-module-coefficients). -/
instance kummerRootCohomologyModule (X : Scheme.{u}) (m q : ℕ) :
    Module (ULift.{u + 1} (ZMod m)) (Sheaf.H (X.rootsOfUnitySheaf m) q) :=
  letI := AddCommGroup.zmodModule (kummerRootCohomology_annihilated X m q)
  Module.compHom _ ULift.ringEquiv.toRingHom

/-- Twisted coefficient cohomology is killed by `m`.
Source: Stacks, Tag 03PK (blueprint: def-pur-kummer-module-coefficients).
Proof: the twist is a sheaf of ZMod m modules. Its underlying abelian sheaf has m times
the identity equal to zero; apply the additive cohomology functor in degree q. -/
theorem kummerModuleCohomology_annihilated (X : Scheme.{u}) (m q : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))
    (x : Sheaf.H ((kummerAbelianTwist X m).obj A) q) : m • x = 0 := by
  let F := (kummerModuleTwist X m).obj A
  have h : m • 𝟙 ((kummerAbelianTwist X m).obj A) = 0 := by
    apply Sheaf.hom_ext
    ext U y
    have hy (z : F.obj.obj U) : m • z = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ULift.{u + 1} (ZMod m)),
        show (m : ULift.{u + 1} (ZMod m)) = 0 by
          apply ULift.ext
          exact ZMod.natCast_self m, zero_smul]
    exact hy y
  have hx := congrArg (fun f ↦ Sheaf.H.map f q x) h
  rw [Sheaf.H.map_nsmul_apply, Sheaf.H.map_id_apply, Sheaf.H.map_apply,
    Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero] at hx
  exact hx

/-- The unique residue-ring action on twisted coefficient cohomology.
Source: Stacks, Tag 03PK (blueprint: def-pur-kummer-module-coefficients). -/
instance kummerModuleCohomologyModule (X : Scheme.{u}) (m q : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m))) :
    Module (ULift.{u + 1} (ZMod m)) (Sheaf.H ((kummerAbelianTwist X m).obj A) q) :=
  letI := AddCommGroup.zmodModule (kummerModuleCohomology_annihilated X m q A)
  Module.compHom _ ULift.ringEquiv.toRingHom

end AlgebraicGeometry.Scheme
