/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap

/-! # Pure-tensor extensionality for internal Hom

Source: Stacks Project, more-algebra.tex, Lemma 0A6A (lemma-base-change-RHom).
(blueprint: lem-pc-ring-extension-internal-hom-ext)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem ringExtension_induction
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (M : RingSiteModules A) (U : (Discrete PUnit.{u + 1})ᵒᵖ)
    (S : (F.obj M).val.obj U → Prop)
    (hzero : S 0) (hadd : ∀ x y, S x → S y → S (x + y))
    (hpure : ∀ b x, S (ringExtensionPure φ F hF M U b x))
    (z : (F.obj M).val.obj U) : S z := by
  let α := (eqToHom (hF M).symm).val.app U
  let η := toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf (ringSiteMap φ) M).presheaf
  have : IsIso η := isIso_toSheafify ⊥ (Presheaf.isSheaf_bot _)
  have : IsIso α := by
    change IsIso ((SheafOfModules.evaluation _ U).map (eqToHom (hF M).symm))
    infer_instance
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso α).2 z
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (η.app U)).2 y
  let : Module A B := Module.compHom B φ
  induction x using TensorProduct.induction_on with
  | zero => simpa using hzero
  | tmul b x => exact hpure b x
  | add x y hx hy => simpa using hadd _ _ hx hy

/-- Maps from an extended module to an internal Hom out of an extended module are
 determined by evaluation on pure tensors in both arguments.

Source: Stacks Project, more-algebra.tex, Lemma 0A6A, tensor-Hom calculation;
algebra.tex, the universal property of tensor product.
(blueprint: lem-pc-ring-extension-internal-hom-ext).

Proof: transport through hF to the specified scalar extensions. On this bottom-topology
site the sheafification unit is invertible, so every section of an extension is a sum
of pure tensors. For each pure tensor in T, the two internal-Hom sections agree on
pure tensors in M by hypothesis, hence on every section of M's extension by additivity.
The slice over each object has only its identity object and identity arrows up to the
unique isomorphism, so equality at the identity slice object implies equality of the
internal-Hom sections, by naturality. Additivity and generation by pure tensors in T
then imply equality on every section of T's extension. Extensionality of module-sheaf
morphisms gives f=g. Zero rings and zero modules cause no exception. -/
theorem ringExtension_internalHom_ext
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (T M : RingSiteModules A) (N : RingSiteModules B)
    (f g : F.obj T ⟶ SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf B)
      (F.obj M) N)
    (h : ∀ (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
      (x : T.val.obj U) (y : M.val.obj U),
      ((f.val.app U (ringExtensionPure φ F hF T U b x)).app
        (op (Over.mk (𝟙 U.unop)))) (ringExtensionPure φ F hF M U c y) =
      ((g.val.app U (ringExtensionPure φ F hF T U b x)).app
        (op (Over.mk (𝟙 U.unop)))) (ringExtensionPure φ F hF M U c y)) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using ringExtension_induction φ F hF T U with
  | hzero => simp
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hpure b x =>
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have hw : W = op (Over.mk (𝟙 U.unop)) := by
      apply Opposite.unop_injective
      rcases U with ⟨⟨⟨⟩⟩⟩
      rcases W with ⟨⟨⟨⟨⟩⟩, ⟨⟨⟩⟩, f⟩⟩
      rfl
    subst W
    induction z using ringExtension_induction φ F hF M U with
    | hzero => exact (map_zero _).trans (map_zero _).symm
    | hadd y z hy hz => simp only [map_add, hy, hz]
    | hpure c y => exact h U b c x y

end CategoryTheory
