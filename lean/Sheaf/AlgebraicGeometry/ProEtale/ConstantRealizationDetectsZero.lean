/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Nonempty constant sheaf detects a zero module
Source: Stacks Project, sites.tex, Tags 00WB and 00WK, applied via sites-modules.tex Tag 03CY
(blueprint: lem-sfb-constant-realization-detects-zero).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The unit map from a module to its constant-module realization on a pro-etale object.
Source: Stacks Project, sites.tex, Tags 00WB and 00WK, and sites-modules.tex Tag 03CY
(blueprint: lem-sfb-constant-realization-detects-zero). -/
def constantRealizationUnit (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R]
    (T : ModuleCat.{u + 1} R) (U : X.ProEt) :
    T → ((siteConstantModuleFunctorGeneral (Scheme.ProEt.topology X) R).obj T).val.obj
      (Opposite.op U) :=
  fun t ↦
    ((((PresheafOfModules.sheafificationAdjunction
      (CategoryTheory.toSheafify (Scheme.ProEt.topology X)
        ((Functor.const (X.ProEt)ᵒᵖ).obj (RingCat.of R)))).unit.app
      ((siteConstantModulePresheafGeneral (C := X.ProEt) R).obj T)).app
        (Opposite.op U)).hom t)

/-- On a nonempty pro-etale object, the constant-module realization unit is injective;
therefore a zero realization forces the original module to be zero, including when the
realization is zero after restriction to the localized site.
Source: Stacks Project, sites.tex, Tags 00WB and 00WK, applied to constant modules via
sites-modules.tex Tag 03CY (blueprint: lem-sfb-constant-realization-detects-zero).
Proof: If two module elements have equal images under the sheafification unit at `U`,
local injectivity of sheafification (lem-sf-constant-module-unit-locally-bijective,
the plus construction in Tag 00WB) gives a covering
on which they are equal in the constant presheaf. All its restriction maps are identities.
A covering of a nonempty pro-etale object is jointly surjective, so it has a member with
nonempty underlying scheme; the equality there is equality of the original elements.
This proves injectivity. If the section module is zero, all images coincide, and hence
all elements of `T` coincide, which is equivalent to `IsZero T`. Finally, if the localized
sheaf is zero, its sections at the terminal object `U → U` are zero. By the definition
of localization (def-pur-localized-ringed-site), these are exactly the original sections
at `U`, so the preceding implication applies.
-/
theorem constantRealization_detects_zero (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R]
    (T : ModuleCat.{u + 1} R) (U : X.ProEt) [Nonempty U.left] :
    Function.Injective (constantRealizationUnit X R T U) ∧
      (IsZero (((siteConstantModuleFunctorGeneral (Scheme.ProEt.topology X) R).obj T).val.obj
        (Opposite.op U)) → IsZero T) ∧
      (IsZero (((siteConstantModuleFunctorGeneral (Scheme.ProEt.topology X) R).obj T).over U) →
        IsZero T) := by
  classical
  let J := Scheme.ProEt.topology X
  let P := ((siteConstantModulePresheafGeneral (C := X.ProEt) R).obj T).presheaf
  have hbot : (⊥ : Sieve U) ∉ J U := by
    intro h
    obtain ⟨Q, hQ, hQS⟩ := Scheme.ProEt.mem_topology_iff.mp h
    obtain ⟨ι, V, f, rfl⟩ := Q.exists_eq_ofArrows
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hQ
    obtain ⟨i, y, hy⟩ :=
      ((Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).1 hQ.2).1
        (Classical.arbitrary U.left)
    have hf := hQS _ _ (Presieve.ofArrows.mk i)
    simp at hf
  have hinj : Function.Injective (constantRealizationUnit X R T U) := by
    intro a b hab
    have hS := Presheaf.equalizerSieve_mem J (toSheafify J P) a b hab
    by_contra hab'
    apply hbot
    convert hS using 1
    ext V g
    simp only [Sieve.bot_apply, Presheaf.equalizerSieve_apply, false_iff]
    change ¬ a = b
    exact hab'
  have hzero : IsZero (((siteConstantModuleFunctorGeneral J R).obj T).val.obj
      (Opposite.op U)) → IsZero T := by
    intro h
    have := ModuleCat.subsingleton_of_isZero h
    have : Subsingleton T := ⟨fun a b ↦ hinj (Subsingleton.elim _ _)⟩
    exact ModuleCat.isZero_of_subsingleton T
  refine ⟨hinj, hzero, ?_⟩
  intro h
  apply hzero
  exact (SheafOfModules.evaluation _ (Opposite.op (Over.mk (𝟙 U)))).map_isZero h

end AlgebraicGeometry.ProEtale
