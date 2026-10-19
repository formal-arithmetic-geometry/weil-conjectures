/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.Paper.IntrinsicCompletion
public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.CategoryTheory.RingedCechKoszulDualLimit
import Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.ExtendedCechCompletionModel
import Sheaf.Paper.RingedLocalizationRHomCalculus

/-!
# The Koszul reflector at the actual small pro-etale universes

Source: Stacks Project, Tags 0999, 099B and 0A0E
(blueprint: lem-weil-pbc-ringed-koszul-completion-reflector).
The completed coefficient ring, signed fiber and (u,0) unit are the published ones.

## Main definitions

- `wfCompletionObj`, `wfCompletionUnit`: the published Koszul fiber and its unit.
- `WfCompleteCategory`: the full subcategory with invertible completion unit.
- `wfCompletion`: the functor determined by the reflector's Hom bijection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)

/-- A genuine complex representative supplied by essential surjectivity of localization.
Source: Stacks 0A0E (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
abbrev wfCompletionRepresentative (M : PbcCompletedDerived X d) :=
  DerivedCategory.Q.objPreimage M

/-- The specified Koszul fiber, localized after choosing a representative of this very M.
Source: Stacks 0A0E (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
def wfCompletionObj (M : PbcCompletedDerived X d) : PbcCompletedDerived X d :=
  intrinsicCompletion X d r a ha M (wfCompletionRepresentative X d M)
    (DerivedCategory.Q.objObjPreimageIso M)

/-- Its actual (u,0) unit, including the realization of the chosen representative.
Source: Stacks 0A0E (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
def wfCompletionUnit (M : PbcCompletedDerived X d) : M ⟶ wfCompletionObj X d r a ha M :=
  intrinsicCompletionUnit X d r a ha M (wfCompletionRepresentative X d M)
    (DerivedCategory.Q.objObjPreimageIso M)

/-- Intrinsic completeness, using exactly the published completion predicate.
Source: Stacks 0999 (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
def WfIsComplete (M : PbcCompletedDerived X d) : Prop :=
  IsDerivedCompleteIntrinsic X d r a ha M (wfCompletionRepresentative X d M)
    (DerivedCategory.Q.objObjPreimageIso M)

/-- The complete full subcategory has no chosen completion witnesses in its objects.
Source: Stacks 0999 (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
abbrev WfCompleteCategory := ObjectProperty.FullSubcategory (WfIsComplete X d r a ha)

/-- The published Koszul fiber is the reflector, also with distinct site object/Hom sizes.
Source: Stacks 099B and 0A0E
(blueprint: lem-weil-pbc-ringed-koszul-completion-reflector).
Proof: pass to a small model of the site in the coefficient universe. The site equivalence
preserves module tensor, strict towers and their derived inverse limits. Apply the ringed
Koszul reflector there. Exact countable products on the small pro-etale site identify its
strict derived limit with the published product/mapping-fiber complex. The comparison
preserves the degree-zero augmentation, hence precisely the (u,0) unit. Transport back.
The reflector's complete-output and Hom-bijection assertions give the two clauses. -/
theorem wfCompletionReflector :
    (∀ M : PbcCompletedDerived X d,
      WfIsComplete X d r a ha (wfCompletionObj X d r a ha M)) ∧
    ∀ (M L : PbcCompletedDerived X d), WfIsComplete X d r a ha L →
      Function.Bijective (fun f : wfCompletionObj X d r a ha M ⟶ L ↦
        wfCompletionUnit X d r a ha M ≫ f) := by
  sorry

/-- The complete object defined by the explicit Koszul fiber.
Source: Stacks 0A0E (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
def wfCompleteObj (M : PbcCompletedDerived X d) : WfCompleteCategory X d r a ha :=
  ⟨wfCompletionObj X d r a ha M, (wfCompletionReflector X d r a ha).1 M⟩

/-- Unique extension across the actual completion unit, rather than a chosen arbitrary map.
Source: Stacks 099B (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
def wfCompletionExtend (M : PbcCompletedDerived X d)
    (L : WfCompleteCategory X d r a ha) (f : M ⟶ L.obj) :
    wfCompletionObj X d r a ha M ⟶ L.obj :=
  Equiv.ofBijective _ ((wfCompletionReflector X d r a ha).2 M L.obj L.property) |>.symm f

set_option backward.isDefEq.respectTransparency false in
/-- The unique extended maps preserve identities and composition.
Source: Stacks 099B (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector).
Proof: compose with the completion unit. Both identity candidates become the same unit;
both composition candidates become f followed by g followed by the final unit. The Hom
bijection's injectivity gives both equations. -/
theorem wfCompletionMap_laws :
    (∀ M : PbcCompletedDerived X d,
      wfCompletionExtend X d r a ha M (wfCompleteObj X d r a ha M)
        (𝟙 M ≫ wfCompletionUnit X d r a ha M) = 𝟙 _) ∧
    ∀ (M N P : PbcCompletedDerived X d) (f : M ⟶ N) (g : N ⟶ P),
      wfCompletionExtend X d r a ha M (wfCompleteObj X d r a ha P)
          ((f ≫ g) ≫ wfCompletionUnit X d r a ha P) =
        wfCompletionExtend X d r a ha M (wfCompleteObj X d r a ha N)
            (f ≫ wfCompletionUnit X d r a ha N) ≫
          wfCompletionExtend X d r a ha N (wfCompleteObj X d r a ha P)
            (g ≫ wfCompletionUnit X d r a ha P) := by
  have hext (M : PbcCompletedDerived X d) (L : WfCompleteCategory X d r a ha)
      (f : M ⟶ L.obj) :
      wfCompletionUnit X d r a ha M ≫ wfCompletionExtend X d r a ha M L f = f := by
    exact (Equiv.ofBijective _
      ((wfCompletionReflector X d r a ha).2 M L.obj L.property)).apply_symm_apply f
  constructor
  · intro M
    apply ((wfCompletionReflector X d r a ha).2 M
      (wfCompletionObj X d r a ha M) ((wfCompletionReflector X d r a ha).1 M)).1
    simp only [hext, Category.id_comp, Category.comp_id]
  · intro M N P f g
    apply ((wfCompletionReflector X d r a ha).2 M
      (wfCompletionObj X d r a ha P) ((wfCompletionReflector X d r a ha).1 P)).1
    dsimp only
    rw [hext, ← Category.assoc, hext, Category.assoc]
    rw [Category.assoc, hext]

/-- Completion with its canonical morphism action determined by reflection.
Source: Stacks 099B (blueprint: lem-weil-pbc-ringed-koszul-completion-reflector). -/
def wfCompletion : PbcCompletedDerived X d ⥤ WfCompleteCategory X d r a ha where
  obj := wfCompleteObj X d r a ha
  map {M N} f := ObjectProperty.homMk
    (wfCompletionExtend X d r a ha M (wfCompleteObj X d r a ha N)
      (f ≫ wfCompletionUnit X d r a ha N))
  map_id M := ObjectProperty.hom_ext _ ((wfCompletionMap_laws X d r a ha).1 M)
  map_comp f g := ObjectProperty.hom_ext _
    ((wfCompletionMap_laws X d r a ha).2 _ _ _ f g)

end AlgebraicGeometry.Scheme
