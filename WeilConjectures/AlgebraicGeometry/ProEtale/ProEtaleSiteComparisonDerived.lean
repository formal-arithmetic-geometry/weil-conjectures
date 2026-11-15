/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementCoefficientRealization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic

set_option autoImplicit false

/-!
# Bounded below finite-coefficient site comparison

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
node theorem-bounded-below-cohomology-comparison (blueprint:
theorem-bounded-below-cohomology-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Direct image in the specified coefficient encoding: undo canonical coefficient
realization and restrict along the inclusion of the etale site.
Source: blueprint, theorem-bounded-below-cohomology-comparison, module adjunction
(blueprint: theorem-bounded-below-cohomology-comparison). -/
noncomputable def finiteCoefficientDirectImage :
    FiniteCoefficientModules T Λ ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (finiteCoefficientRealization T Λ).inv ⋙ comparisonLowerStar (ModuleCat.{u + 1} Λ) T

/-- The module adjunction transported through canonical coefficient realization.
Source: blueprint, theorem-bounded-below-cohomology-comparison, module adjunction
(blueprint: theorem-bounded-below-cohomology-comparison). -/
noncomputable def finiteCoefficientComparisonAdjunction :
    finiteCoefficientComparison T Λ ⊣ finiteCoefficientDirectImage T Λ :=
  (T.proEtaleSiteComparisonModules Λ).comp
    (finiteCoefficientRealization T Λ).asEquivalence.toAdjunction

/-- Transport enough injectives along the canonical coefficient equivalence.
Source: blueprint, theorem-bounded-below-cohomology-comparison, injective-resolution paragraph
(blueprint: theorem-bounded-below-cohomology-comparison). -/
noncomputable instance finiteCoefficientModulesEnoughInjectives :
    EnoughInjectives (FiniteCoefficientModules T Λ) :=
  EnoughInjectives.of_equivalence (finiteCoefficientRealization T Λ).inv

/-- Additivity of direct image, inherited from the specified module adjunction.
Source: blueprint, theorem-bounded-below-cohomology-comparison, module adjunction
(blueprint: theorem-bounded-below-cohomology-comparison). -/
noncomputable instance finiteCoefficientDirectImageAdditive :
    (finiteCoefficientDirectImage T Λ).Additive :=
  (finiteCoefficientComparisonAdjunction T Λ).right_adjoint_additive

/-- The canonical adjunction on bounded below derived categories. Its left adjoint is
termwise exact inverse image; its right adjoint is the right derived direct image.
Source: blueprint, theorem-bounded-below-cohomology-comparison, derived-adjunction paragraph
(blueprint: theorem-bounded-below-cohomology-comparison). -/
noncomputable def finiteCoefficientDerivedComparisonAdjunction :
    (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus ⊣
      (finiteCoefficientDirectImage T Λ).rightDerivedFunctorPlus :=
  (finiteCoefficientComparisonAdjunction T Λ).derivedPlus

/-- Finite-coefficient comparison is fully faithful on all bounded below complexes,
and its canonical derived unit is a natural isomorphism.
Source: blueprint, theorem-bounded-below-cohomology-comparison, statement and all proof paragraphs;
Stacks Project, Tag 099V, final paragraph (blueprint: theorem-bounded-below-cohomology-comparison).

Proof:
1. The module categories are abelian. The comparison inverse image is additive and
exact by the finite-level comparison proposition. Termwise application therefore
preserves quasi-isomorphisms and cohomological lower bounds, giving the displayed
functor on the full bounded below derived categories.
2. Good truncation replaces a cohomologically bounded below complex by a termwise
bounded below one. Resolve this by a bounded below termwise injective complex I.
Enough injectives also gives the right derived direct image, with its canonical
comparison, which is invertible on bounded below complexes of injectives.
3. Resolve the inverse image of a bounded below complex by J. The right adjoint of
an exact functor preserves K-injective complexes. The Hom-localization bijections
and termwise homotopy adjunction give the derived adjunction. On a representative
M its unit is the ordinary unit followed by the right-derived comparison; for a
resolution j of its inverse image this is represented by R(j) composed with eta_M.
4. The finite-level proposition makes every term of the inverse image of I acyclic
for direct image. The injective resolution terms are acyclic too. The acyclic
quasi-isomorphism lemma makes R(j) a quasi-isomorphism. Thus the right-derived
comparison is invertible on the inverse image of I.
5. The finite-level unit is invertible termwise on I. Naturality makes its inverse
components a chain map. The derived unit at Q(I) is consequently invertible, by
step 4, and hence so is the unit at any isomorphic derived object. Naturality of
the unit assembles these pointwise inverses into a natural isomorphism.
6. Under the derived adjunction the map on Hom sets induced by inverse image is
composition with this invertible unit, by its naturality. Both maps are bijective,
which proves full faithfulness. No constructibility, finite generation of module
sheaves, upper cohomological bound, or commutativity of the coefficient ring enters. -/
theorem siteComparison_boundedBelow (T : Scheme.{u}) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    Nonempty (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.FullyFaithful ∧
      IsIso (finiteCoefficientDerivedComparisonAdjunction T Λ).unit := by
  let L := comparisonUpperStar (ModuleCat.{u + 1} Λ) T
  let E := finiteCoefficientRealization T Λ
  let adj := comparisonAdjunction (ModuleCat.{u + 1} Λ) T
  obtain ⟨_, _, hunit, hacyclic⟩ := siteComparison_finiteLevel T Λ
  have hu : IsIso adj.derivedPlus.unit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact adj.isIso_derivedPlus_unit_app_of_rightAcyclic
      (fun I _ ↦ hunit I)
      (fun I _ n ↦ hacyclic I inferInstance (n + 1) (Nat.succ_pos n)) K
  let fL := adj.derivedPlus.fullyFaithfulLOfIsIsoUnit
  let fE := (Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.Plus.ι ⋙ E.mapDerivedCategory)).ofIso
      E.mapDerivedCategoryPlusCompatibility.symm
  let e := Functor.mapDerivedCategoryPlusCompIso L E
  let ff := fL.comp (Functor.FullyFaithful.ofCompFaithful fE)
  let f := ff.ofIso e.symm
  have : (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.Full := f.full
  have : (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.Faithful := f.faithful
  exact ⟨⟨f⟩, inferInstance⟩

end AlgebraicGeometry.ProEtale

/- Stage-2 comparison interface rebuild for the compatible uniform category. -/
