/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CanonicalMapsSupport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompCoherenceStatement

/-!

# Composition of the canonical maps of `Rf^!`, given a coherent composition law

The composition law `Rh_! ≅ Rf_! ⋙ Rg_!` for `h = f ≫ g`, compatible with the projection maps
(`sk-prop-sf-pf-coherence`) and with compact-support base change (`sk-thm-sf-package` (2)), is
taken as a hypothesis `AlgebraicGeometry.Etale.RightDerivedLowerShriekCompCoherence` (stated in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompCoherenceStatement`). From it the
canonical maps of `R^!` — the base change map and the tensor map `θ` — compose:

- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff_of_coherence`:
  the base change map of `R(f ≫ g)^!` is, up to the composition isomorphisms, the composite of
  those of `Rf^!` and `Rg^!`;
- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_comp_iff`: `θ_{f ≫ g, K}` is an
  isomorphism if and only if `Rf^! θ_{g, K}` is one, as soon as the tensor map of `f` at
  `(ω_g, Lg^* K)` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- Search the braiding through the symmetric structure, as in the definition of the derived
-- tensor product (see
-- `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence`).
attribute [local instance high] SymmetricCategory.toBraidedCategory

variable {Λ}

section BaseChange

variable {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} {f' : X' ⟶ Y'}
  {g' : Y' ⟶ Z'} {h' : X' ⟶ Z'} {a : X' ⟶ X} {b : Y' ⟶ Y} {c : Z' ⟶ Z}
  (sqf : IsPullback a f' f b) (sqg : IsPullback b g' g c) (sqh : IsPullback a h' h c)
  (w : f ≫ g = h) (w' : f' ≫ g' = h') [HasCompactification f] [HasCompactification g]
  [HasCompactification h] [HasCompactification f'] [HasCompactification g']
  [HasCompactification h'] [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact h']

include sqf sqg sqh w w' in
/-- **Base change maps of a composite**, given a coherent composition law. For stacked cartesian
squares, `β_h` is an isomorphism at `K` if and only if `Rf'^! β_g` is one at `K`, as soon as
`β_f` is one at `Rg^! K`. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_comp_iff_of_coherence
    (hE : RightDerivedLowerShriekCompCoherence Λ)
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hf : IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sqf).app
      ((R(g)^![ModuleCat.{u + 1} Λ]).obj K))) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sqh).app K) ↔
      IsIso ((R(f')^![ModuleCat.{u + 1} Λ]).map
        ((rightDerivedUpperShriekBaseChangeMap Λ sqg).app K)) := by
  obtain ⟨E, -, hEx⟩ := hE
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sqf
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sqg
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sqh
  have key := Adjunction.mateEquiv_inv_comp_rightAdjointUniq
    (rightDerivedUpperShriekAdjunction _ f) (rightDerivedUpperShriekAdjunction _ g)
    (rightDerivedUpperShriekAdjunction _ h) (rightDerivedUpperShriekAdjunction _ f')
    (rightDerivedUpperShriekAdjunction _ g') (rightDerivedUpperShriekAdjunction _ h')
    (rightDerivedLowerShriekBaseChangeMap Λ sqf) (rightDerivedLowerShriekBaseChangeMap Λ sqg)
    (rightDerivedLowerShriekBaseChangeMap Λ sqh) (E f g h w) (E f' g' h' w')
    (hEx sqf sqg sqh w w') K
  change IsIso ((mateEquiv _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sqh))).natTrans.app K) ↔
    IsIso ((R(f')^![ModuleCat.{u + 1} Λ]).map
      ((mateEquiv _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sqg))).natTrans.app K))
  change IsIso ((mateEquiv _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sqf))).natTrans.app
    ((R(g)^![ModuleCat.{u + 1} Λ]).obj K)) at hf
  rw [← isIso_comp_right_iff _ ((Adjunction.rightAdjointUniq
      ((rightDerivedUpperShriekAdjunction _ h').ofNatIsoLeft (E f' g' h' w'))
      ((rightDerivedUpperShriekAdjunction _ f').comp
        (rightDerivedUpperShriekAdjunction _ g'))).hom.app _), ← key,
    isIso_comp_left_iff, isIso_comp_left_iff]

end BaseChange

section Tensor

/-- **The tensor map `θ` of a composite**, given a coherent composition law. For `h = f ≫ g`, if
the tensor map of `f` at `(ω_g, Lg^* K)` is an isomorphism, then `θ_{h, K}` is an isomorphism if
and only if `Rf^! θ_{g, K}` is one: through the composition isomorphism `Rh^! ≅ Rf^! ∘ Rg^!`, the
tensor map of `h` at `(Λ, K)` is the tensor map of `f` at `(ω_g, Lg^* K)` followed by `Rf^!` of
the tensor map of `g` at `(Λ, K)` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap_comp`).
-/
theorem isIso_dualizingComplexTensorMap_comp_iff (hE : RightDerivedLowerShriekCompCoherence Λ)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : f ≫ g = h)
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hf : IsIso (rightDerivedUpperShriekTensorMap f ((R(g)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))
      ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K))) :
    IsIso (dualizingComplexTensorMap Λ h K) ↔
      IsIso ((R(f)^![ModuleCat.{u + 1} Λ]).map (dualizingComplexTensorMap Λ g K)) := by
  obtain ⟨E, hEp, -⟩ := hE
  have hc := rightDerivedUpperShriekTensorMap_comp f g h w (E f g h w) (hEp f g h w) (𝟙_ _) K
  change IsIso (dualizingComplexTensorMapOfIsIso h K) ↔
    IsIso ((R(f)^![ModuleCat.{u + 1} Λ]).map (dualizingComplexTensorMapOfIsIso g K))
  rw [isIso_dualizingComplexTensorMapOfIsIso_iff, dualizingComplexTensorMapOfIsIso_eq,
    Functor.map_comp, isIso_comp_right_iff, ← isIso_comp_right_iff _ ((Adjunction.rightAdjointUniq
      ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) h).ofNatIsoLeft (E f g h w))
      ((rightDerivedUpperShriekAdjunction _ f).comp
        (rightDerivedUpperShriekAdjunction _ g))).hom.app (𝟙_ _ ⊗ K)), hc,
    isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_left_iff]

end Tensor

end Etale

end AlgebraicGeometry
