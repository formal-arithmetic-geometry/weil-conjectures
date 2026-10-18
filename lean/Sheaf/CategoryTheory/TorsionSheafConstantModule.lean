/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic

/-! # The canonical constant Z/N module structure of a torsion sheaf

Source: Stacks Project, Lemma 18.11.1, Tag 03CY
(blueprint: lem-pur-torsion-sheaf-constant-module).
-/

@[expose] public section

universe w vC uC

open CategoryTheory

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J RingCat.{w}]

/-- The constant sheaf of rings with value `Z/N`, lifted to the coefficient universe.
Source: Stacks Project, Tag 03CY (blueprint: lem-pur-torsion-sheaf-constant-module). -/
noncomputable abbrev constantZModRingSheaf (N : ℕ) : Sheaf J RingCat.{w} :=
  (constantSheaf J RingCat.{w}).obj (RingCat.of (ULift.{w} (ZMod N)))

/-- A module structure on the fixed underlying groups, normalized on constant sections,
with semilinear restrictions. The normalization uses every integer representative.
Source: Stacks Project, Tag 03CY (blueprint: lem-pur-torsion-sheaf-constant-module). -/
def IsConstantZModSheafModuleStructure (N : ℕ) (F : Sheaf J AddCommGrpCat.{w})
    (M : ∀ U : Cᵒᵖ, Module ((constantZModRingSheaf J N).obj.obj U) (F.obj.obj U)) : Prop :=
  (∀ (U : Cᵒᵖ) (z : ℤ) (x : F.obj.obj U),
    @SMul.smul _ _ (M U).toSMul
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{w} (ZMod N))))).app U
        (ULift.up (z : ZMod N))) x = z • x) ∧
  ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (a : (constantZModRingSheaf J N).obj.obj U)
      (x : F.obj.obj U),
    F.obj.map f (@SMul.smul _ _ (M U).toSMul a x) =
      @SMul.smul _ _ (M V).toSMul ((constantZModRingSheaf J N).obj.map f a) (F.obj.map f x)

/-- A sheaf killed by `N` has exactly one normalized constant `Z/N` module structure.
Source: Stacks Project, Tag 03CY (blueprint: lem-pur-torsion-sheaf-constant-module).
Proof: the annihilation hypothesis makes each group a `ZMod N`-module, with integer
representatives acting by integer multiples. Additive restriction maps are linear over this
constant presheaf. Lemma 03CY uniquely extends this action to the sheafification of that
presheaf of rings; the abelian sheaf is already a sheaf, so its sheafification is itself.
The resulting action commutes with restrictions. The uniqueness part of 03CY proves
uniqueness of the family of module structures. -/
theorem existsUnique_constantZModSheafModuleStructure (N : ℕ) (hN : 0 < N)
    (F : Sheaf J AddCommGrpCat.{w}) (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0) :
    ∃! M : ∀ U : Cᵒᵖ, Module ((constantZModRingSheaf J N).obj.obj U) (F.obj.obj U),
      IsConstantZModSheafModuleStructure J N F M := by
  sorry

/-- The unique normalized scalar action; choice is from an existence-and-uniqueness theorem.
Source: Stacks Project, Tag 03CY (blueprint: lem-pur-torsion-sheaf-constant-module). -/
@[instance_reducible]
noncomputable def torsionSheafModuleStructure (N : ℕ) (hN : 0 < N)
    (F : Sheaf J AddCommGrpCat.{w}) (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0) :
    ∀ U : Cᵒᵖ, Module ((constantZModRingSheaf J N).obj.obj U) (F.obj.obj U) :=
  (existsUnique_constantZModSheafModuleStructure J N hN F hF).exists.choose

/-- The chosen unique action satisfies normalization and semilinearity.
Source: Stacks Project, Tag 03CY (blueprint: lem-pur-torsion-sheaf-constant-module).
Proof: apply the specification of the unique witness in
`existsUnique_constantZModSheafModuleStructure`, which constructs the action by 03CY. -/
theorem torsionSheafModuleStructure_spec (N : ℕ) (hN : 0 < N)
    (F : Sheaf J AddCommGrpCat.{w}) (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0) :
    IsConstantZModSheafModuleStructure J N F (torsionSheafModuleStructure J N hN F hF) := by
  sorry

/-- The corresponding module sheaf has exactly the original underlying abelian presheaf.
Source: Stacks Project, Tag 03CY (blueprint: lem-pur-torsion-sheaf-constant-module). -/
noncomputable def torsionSheafModule (N : ℕ) (hN : 0 < N)
    (F : Sheaf J AddCommGrpCat.{w}) (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0) :
    ringedSiteModules (constantZModRingSheaf J N) :=
  letI := torsionSheafModuleStructure J N hN F hF
  ⟨PresheafOfModules.ofPresheaf F.obj (torsionSheafModuleStructure_spec J N hN F hF).2,
    F.property⟩

/-- Every additive sheaf morphism between `N`-torsion sheaves is linear for their canonical
constant `Z/N` module structures.
Source: Stacks Project, Tag 03CY (blueprint: lem-pur-torsion-sheaf-constant-module).
Proof: an additive map commutes with integer multiples, hence is linear over the constant
presheaf `ZMod N`. The morphism clause of 03CY extends that linearity to the sheafified
ring action. This applies to every normalized action by the uniqueness just established. -/
theorem torsionSheaf_hom_linear (N : ℕ) (hN : 0 < N)
    (F G : Sheaf J AddCommGrpCat.{w})
    (hF : ∀ (U : Cᵒᵖ) (x : F.obj.obj U), N • x = 0)
    (hG : ∀ (U : Cᵒᵖ) (x : G.obj.obj U), N • x = 0) (φ : F ⟶ G)
    (M : ∀ U : Cᵒᵖ, Module ((constantZModRingSheaf J N).obj.obj U) (F.obj.obj U))
    (M' : ∀ U : Cᵒᵖ, Module ((constantZModRingSheaf J N).obj.obj U) (G.obj.obj U))
    (hM : IsConstantZModSheafModuleStructure J N F M)
    (hM' : IsConstantZModSheafModuleStructure J N G M') :
    ∀ (U : Cᵒᵖ) (a : (constantZModRingSheaf J N).obj.obj U) (x : F.obj.obj U),
      φ.hom.app U (@SMul.smul _ _ (M U).toSMul a x) =
        @SMul.smul _ _ (M' U).toSMul a (φ.hom.app U x) := by
  sorry

/-- Conversely, every module sheaf over the constant `Z/N` ring is killed by `N`.
Source: Stacks Project, Tag 03CY (blueprint: lem-pur-torsion-sheaf-constant-module).
Proof: the image of the integer `N` in the constant presheaf `ZMod N` is zero.
The sheafified image is still zero. Its action is multiplication by `N`, so the
module axioms give `N • x = 0` on every section. -/
theorem constantZModModuleSheaf_nsmul (N : ℕ) (hN : 0 < N)
    (F : ringedSiteModules (constantZModRingSheaf J N))
    (U : Cᵒᵖ) (x : F.val.obj U) : N • x = 0 := by
  sorry

end CategoryTheory
