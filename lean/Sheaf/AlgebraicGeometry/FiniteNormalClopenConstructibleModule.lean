/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q115
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Pi.Basic
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Constructibility of a finite clopen componentwise constant module sheaf

Source: literature/stacks-project/etale-cohomology.tex, Tags 03RU and 03RW,
and the blueprint proof of lem-fin-normal-open-lisse-image
(blueprint: lem-fin-normal-clopen-constructible-module).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The componentwise product of the direct images of finite constant module sheaves.
Source: Stacks Project, Etale Cohomology, Tags 03RU and 03RW; this is the displayed
formula in lem-fin-normal-clopen-constructible-module
(blueprint: lem-fin-normal-clopen-constructible-module). -/
noncomputable def finiteNormalClopenConstantModuleSheaf
    {Λ : Type (u + 1)} [CommRing Λ]
    {Y : Scheme.{u}} {r : ℕ} (C : Fin r → Scheme.{u})
    (ι : ∀ a : Fin r, C a ⟶ Y) (M : Fin r → ModuleCat.{u + 1} Λ) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (Pi.functor (Fin r)).obj
    ((Functor.pi (fun a ↦ Etale.lowerStar (ModuleCat.{u + 1} Λ) (ι a))).obj
      (fun a ↦
        (constantSheaf (C a).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M a)))

/-- A finite disjoint clopen coproduct of schemes carrying finite constant module values
is constructible in both the module-sheaf and general constructibility formulations.
The component restrictions are identified with the specified constant sheaves.

Proof. The coproduct legs are clopen and form a finite covering. On the a-th leg,
the upper-star restriction of the componentwise product has only the a-th nonzero
factor, hence is the constant sheaf with value M a; the empty product gives the zero
sheaf when the index is empty. These identifications provide the finite locally constant
models on the clopen stratification. The same stratification satisfies both
constructibility predicates, and the component projections give the displayed
isomorphisms. This uses def-weil-pbc-etale-site,
def-weil-sheaf-of-modules-category, lem-weil-pbc-open-immersion-etale,
lem-weil-pbc-etale-inverse-image-restriction,
lem-weil-pbc-module-abelian-inverse-image-comparison,
lem-weil-pbc-finite-locally-constant-module-values,
def-constructible-stratification, def-weil-constructible-subset,
def-weil-pbc-etale-constructible-sheaf, and def-constructible-constructible.
Source: literature/stacks-project/etale-cohomology.tex, Tags 03RU and 03RW, and the
blueprint proof of lem-fin-normal-open-lisse-image
(blueprint: lem-fin-normal-clopen-constructible-module). -/
theorem finite_normal_clopen_constructible_module
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (Y : Scheme.{u}) (r : ℕ) (C : Fin r → Scheme.{u})
    (ι : ∀ a : Fin r, C a ⟶ Y) (hc : IsColimit (Cofan.mk Y ι))
    (M : Fin r → ModuleCat.{u + 1} Λ)
    (hM : ∀ a : Fin r, Finite (M a))
    (hopen : ∀ a : Fin r, IsOpenImmersion (ι a))
    (hclosed : ∀ a : Fin r, IsClosedImmersion (ι a)) :
    IsConstructibleEtaleModuleSheaf
        (finiteNormalClopenConstantModuleSheaf C ι M) ∧
      IsConstructibleSheaf (finiteNormalClopenConstantModuleSheaf C ι M) ∧
      ∀ a : Fin r, Nonempty
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (ι a)).obj
          (finiteNormalClopenConstantModuleSheaf C ι M) ≅
          (constantSheaf (C a).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M a)) := by
  sorry

end AlgebraicGeometry.Scheme
