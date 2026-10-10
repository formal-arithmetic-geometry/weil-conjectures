/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.UpperStarExact

/-!
# Extension by zero of Weil sheaves: exactness and weights

The extension by zero `j₀!` of Weil sheaves along a quasi-compact open immersion `j : U ⟶ X` is
exact, and it preserves punctual purity and upper weight bounds: its geometric stalk at a closed
point of `U` is the stalk of the sheaf, with the same local Frobenius and the same residue field,
and its stalks at the closed points outside `U` vanish.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

/-- The extension by zero of Weil sheaves is the extension by zero of pro-étale Weil sheaves. -/
noncomputable def extensionByZeroCompιIso :
    extensionByZero (l := l) j ⋙ (WeilSheaf.objectProperty k₀ l X).ι ≅
      (WeilSheaf.objectProperty k₀ l U).ι ⋙ ProEtaleWeilSheaf.extensionByZero k₀ l j := by
  unfold extensionByZero
  exact ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _

/-- A Weil sheaf with an epimorphism from a sheaf with weights at most `w` has weights at most
`w`: its stalks are Frobenius-equivariant quotients. -/
theorem HasWeightsAtMost.of_epi [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    {ι : PadicAlgCl l →+* ℂ} {w : ℝ} {F G : WeilSheaf k₀ l X} (f : F ⟶ G) [Epi f]
    (h : F.HasWeightsAtMost ι w) : G.HasWeightsAtMost ι w := fun x α hα ↦
  h x α (FrobeniusModule.hasEigenvalue_of_surjective _ (stalkAtMap_frobenius _ _ _ f)
    (surjective_stalkAtMap _ _ _ f) hα)

variable [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

instance : PreservesFiniteLimits (extensionByZero (k₀ := k₀) (l := l) j) := by
  have : PreservesFiniteLimits (extensionByZero (k₀ := k₀) (l := l) j ⋙
      (WeilSheaf.objectProperty k₀ l X).ι) :=
    preservesFiniteLimits_of_natIso (WeilSheaf.extensionByZeroCompιIso j).symm
  have : ReflectsFiniteLimits (WeilSheaf.objectProperty k₀ l X).ι := ⟨fun _ _ _ ↦ inferInstance⟩
  exact preservesFiniteLimits_of_reflects_of_preserves _ (WeilSheaf.objectProperty k₀ l X).ι

instance : PreservesFiniteColimits (extensionByZero (k₀ := k₀) (l := l) j) := by
  have : PreservesFiniteColimits (extensionByZero (k₀ := k₀) (l := l) j ⋙
      (WeilSheaf.objectProperty k₀ l X).ι) :=
    preservesFiniteColimits_of_natIso (WeilSheaf.extensionByZeroCompιIso j).symm
  have : ReflectsFiniteColimits (WeilSheaf.objectProperty k₀ l X).ι := {}
  exact preservesFiniteColimits_of_reflects_of_preserves _ (WeilSheaf.objectProperty k₀ l X).ι

variable {ι : PadicAlgCl l →+* ℂ} {w : ℝ} {F : WeilSheaf k₀ l U}

/-- Extension by zero along a quasi-compact open immersion preserves punctual purity: at a
closed point of `U` the geometric stalk of `j₀!F` is that of `F`, with the same local Frobenius
and the same residue field, and at a closed point outside `U` it vanishes. -/
theorem IsPunctuallyPureOfWeight.extensionByZero (hF : F.IsPunctuallyPureOfWeight ι w) :
    ((WeilSheaf.extensionByZero j).obj F).IsPunctuallyPureOfWeight ι w :=
  sorry

/-- Extension by zero along a quasi-compact open immersion preserves upper weight bounds: at a
closed point of `U` the geometric stalk of `j₀!F` is that of `F`, with the same local Frobenius
and the same residue field, and at a closed point outside `U` it vanishes. -/
theorem HasWeightsAtMost.extensionByZero (hF : F.HasWeightsAtMost ι w) :
    ((WeilSheaf.extensionByZero j).obj F).HasWeightsAtMost ι w :=
  sorry

end WeilSheaf

end AlgebraicGeometry
