/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Topology.Sheaves.CechComparison

/-! # Refinement of module Cech complexes along a scheme morphism

Source: Stacks Project, Cohomology, Tag 01FD
(blueprint: def-sc-cech-refinement-cochain-map).
The component formula fixes the map to pullback of sections followed by restriction;
it is not an unconstrained map assumed to commute with cohomology comparisons.
-/

universe uR
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The inclusion of a refined intersection in the inverse image of its original
intersection. Covers and index sets need not be finite.
Source: Stacks, Tag 01FD (blueprint: def-sc-cech-refinement-cochain-map). -/
def cechRefinementIntersection {X X' : Scheme.{uR}} (f : X' ⟶ X)
    {ι ι' : Type uR} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (n : ℕ) (y : Fin (n + 1) → ι') :
    (⨅ j, U' (y j)) ⟶ f ⁻¹ᵁ (⨅ j, U (refine (y j))) :=
  homOfLE (by
    intro x hx
    change f.base x ∈ ⨅ j, U (refine (y j))
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    intro j
    exact hrefine (y j) ((iInf_le (fun j ↦ U' (y j)) j) hx))

/-- The prescribed refinement map on cochains, written on every tuple of indices.
The canonical tensor-pullback adjunction unit gives pullback of sections.
Source: Stacks, Tag 01FD (blueprint: def-sc-cech-refinement-cochain-map). -/
def IsCechRefinementMap {X X' : Scheme.{uR}} (f : X' ⟶ X)
    {ι ι' : Type uR} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i)) (F : X.Modules)
    (gamma : ((forget₂ (ModuleCat.{uR} Γ(X, ⊤)) AddCommGrpCat.{uR}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{uR} Γ(X', ⊤)) AddCommGrpCat.{uR}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat)) : Prop :=
  ∀ (n : ℕ) (a : ((cechComplexFunctor U).obj F.presheafModuleCat).X n)
    (y : Fin (n + 1) → ι'),
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U'
        ((tensorPullback f).obj F).presheafModuleCat n (gamma.f n a) y =
      ((tensorPullback f).obj F).presheaf.map
        (cechRefinementIntersection f U U' refine hrefine n y).op
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F).val.app
          (op (⨅ j, U (refine (y j))))
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a
            (refine ∘ y)))

/-- Pullback and restriction define a unique refinement cochain map.
Source: Stacks, Tag 01FD (blueprint: def-sc-cech-refinement-cochain-map).
Proof: use the specified tuple components and the product universal property to define
its degree maps. Pullback of sections and restrictions are additive. Each omitted-vertex
restriction commutes with these maps, so the alternating sums commute with the
 differential. Uniqueness follows by the product projections in every degree.
No covering hypothesis is needed for the cochain construction. -/
theorem exists_unique_cechRefinementMap {X X' : Scheme.{uR}} (f : X' ⟶ X)
    {ι ι' : Type uR} (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i)) (F : X.Modules) :
    ∃! gamma : ((forget₂ (ModuleCat.{uR} Γ(X, ⊤)) AddCommGrpCat.{uR}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{uR} Γ(X', ⊤)) AddCommGrpCat.{uR}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat),
      IsCechRefinementMap f U U' refine hrefine F gamma := by
  sorry

/-- The refinement map on cohomology, transported through the canonical homology
comparison for forgetting scalars on each scheme.
Source: Stacks, Tag 01FD (blueprint: def-sc-cech-refinement-cochain-map). -/
def cechRefinementHomology {X X' : Scheme.{uR}} {f : X' ⟶ X}
    {ι ι' : Type uR} {U : ι → X.Opens} {U' : ι' → X'.Opens} {F : X.Modules}
    (gamma : ((forget₂ (ModuleCat.{uR} Γ(X, ⊤)) AddCommGrpCat.{uR}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{uR} Γ(X', ⊤)) AddCommGrpCat.{uR}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat))
    (p : ℕ) :
    (forget₂ _ AddCommGrpCat).obj
        (((cechComplexFunctor U).obj F.presheafModuleCat).homology p) ⟶
      (forget₂ _ AddCommGrpCat).obj
        (((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat).homology p) :=
  ((((cechComplexFunctor U).obj F.presheafModuleCat).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat)).inv ≫
    HomologicalComplex.homologyMap gamma p ≫
    ((((cechComplexFunctor U').obj
      ((tensorPullback f).obj F).presheafModuleCat).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat)).hom

end
end AlgebraicGeometry.Scheme.Modules
