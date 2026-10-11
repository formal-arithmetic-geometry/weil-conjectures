/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# The kernel of a degreewise epimorphism and its shifted mapping cone

Source: Stacks Project, Derived Categories, Tags 070M and 014Q; the chain-level
comparison implicit in the proof of Tag 070M
(blueprint: lem-weil-degreewise-epi-kernel-cocone-qis).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

/-- Source: Stacks Project, Derived Categories, Tags 070M and 014Q
(blueprint: lem-weil-degreewise-epi-kernel-cocone-qis).
The termwise kernel of a degreewise epimorphism maps quasi-isomorphically to the cone
shifted by `-1`. Mathlib orders the cone summands as `P^(r+1) ⊞ Q^r`, so the two
projection identities below specify the map written `(0, ι)` with the source's ordering.

Proof: (1) The kernel inclusion commutes with differentials, since `f` does. The cone
and shift differentials then show that `(0, ι)` is a chain map, using `ι ≫ f = 0`
[def-sp-abelian, def-weil-abstract-derived-category].
(2) Map the shifted cone to the shifted cone of `𝟙 Q` by `(y, x) ↦ (y, f x)`.
Degreewise this is the direct sum of the identity of `Q^(p-1)` and the kernel exact
sequence of `f^p`, giving a short exact sequence with kernel the displayed comparison.
The shifted identity cone is contractible by `h(y, q) = (0, -y)`, hence has zero
cohomology [def-sp-abelian, def-weil-abstract-derived-category].
(3) The short exact sequence gives a distinguished triangle
[lem-weil-pbc-complex-ses-triangle]. Compare it to the identity triangle on the kernel
[def-weil-triangulated-category]; the first and third components are isomorphisms, so
[lem-sf-triangle-morphism-iso] makes the localized comparison an isomorphism.
Cohomology factors through the localization [def-weil-abstract-derived-category], so
the comparison is a quasi-isomorphism and identifies these objects in the derived category. -/
theorem exists_kernel_to_shifted_mappingCone_of_degreewise_epi
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) (hf : ∀ p : ℤ, Epi (f.f p)) :
    ∃ κ : kernel f ⟶ (mappingCone f)⟦(-1 : ℤ)⟧,
      (∀ p : ℤ,
        κ.f p ≫ ((mappingCone f).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
          homotopyCofiber.sndX f (p - 1) = 0 ∧
        κ.f p ≫ ((mappingCone f).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
          homotopyCofiber.fstX f (p - 1) p (by change p - 1 + 1 = p; omega) =
            (kernel.ι f).f p) ∧
      QuasiIso κ ∧
      Nonempty ((DerivedCategory.Q.obj (kernel f)) ≅
        DerivedCategory.Q.obj ((mappingCone f)⟦(-1 : ℤ)⟧)) := by
  sorry

end CochainComplex
