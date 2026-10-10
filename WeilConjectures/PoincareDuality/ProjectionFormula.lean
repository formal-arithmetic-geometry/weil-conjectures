/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.PoincareDuality.Abstract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.Monoidal

/-!

# The derived exceptional projection morphism for `ℚ̄_ℓ`-coefficients

Let `ℓ` be a prime and `f : X ⟶ Y` a morphism of schemes with a compactification
`c = (X ⟶[i] Z ⟶[g] Y)`, so that `Rf_! = Rg_* ∘ Di_!` and `Lf^* ≅ Li^* ∘ Lg^*` on the derived
categories of module objects over `ℚ̄_ℓ`. This file constructs the *derived exceptional
projection morphism*
```
PF^!_{f,K,B} : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B),
```
the canonical morphism whose invertibility is the derived projection formula for `Rf_!`. Its
direction is chosen so that the Verdier exchange morphism can be defined from it directly
(`WeilConjectures.PoincareDuality.Abstract`). It is the composite of three canonical maps:

1. the projection morphism `PF^*_g : Rg_* A ⊗ᴸ B ⟶ Rg_* (A ⊗ᴸ Lg^* B)` of the adjunction
   `Lg^* ⊣ Rg_*`, the mate of `Lg^* (Rg_* A ⊗ᴸ B) ≅ Lg^* Rg_* A ⊗ᴸ Lg^* B ⟶ A ⊗ᴸ Lg^* B`
   (`CategoryTheory.Adjunction.projectionMorphism`, using the monoidal structure of `Lg^*` of
   `WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.Monoidal`), at
   `A = Di_! K`;
2. the *inverse* of the projection comparison
   `q_{i,M,N} : Di_! (M ⊗ᴸ Li^* N) ⟶ Di_! M ⊗ᴸ N` of the adjunction `Di_! ⊣ Li^*` along the open
   immersion `i` (`CategoryTheory.Adjunction.projectionComparison`), which is *assumed* to be an
   isomorphism (`ProEtale.PadicAlgClRing.isIso_openImmersionProjectionComparison`): this is the
   derived projection formula for the extension by zero;
3. the identification `Li^* Lg^* B ≅ Lf^* B`.

## Main definitions

- `ProEtale.PadicAlgClRing.properProjectionMorphism`: `PF^*_g` for any morphism `g` (the name
  records that it is only expected to be an isomorphism for `g` proper).
- `ProEtale.PadicAlgClRing.openImmersionProjectionComparison`: `q_j` for an open immersion `j`.
- `ProEtale.PadicAlgClRing.exceptionalProjectionMorphismOfCompactification` and
  `ProEtale.PadicAlgClRing.exceptionalProjectionMorphism`: `PF^!_f` with respect to a
  compactification, and for the chosen one.

## Main results

- `ProEtale.PadicAlgClRing.exceptionalProjectionMorphism_natural_right`: `PF^!_{f,K,B}` is
  natural in `B`. This is the only property of `PF^!` used downstream besides its invertibility.
  Its proof (sorried for now) is the naturality of the three constituent maps:
  `Adjunction.projectionMorphism_natural_right`,
  `Adjunction.inv_projectionComparison_natural_right` and that of
  `leftDerivedUpperStarCompactificationIso`.

## Sorried input

- `ProEtale.PadicAlgClRing.isIso_openImmersionProjectionComparison`: `q_j` is an isomorphism.
  On module objects `j_!` is exact and `j^*` is restriction, so `j_!(M ⊗ j^* N) ≅ j_! M ⊗ N`
  holds already on the underived tensor products (`Adjunction.HasProjectionFormula` for
  `j_! ⊣ j^*`), and both sides preserve K-flat resolutions.
- `ProEtale.PadicAlgClRing.isIso_exceptionalProjectionMorphism`: the derived projection formula
  for `Rf_!`, for `K` bounded constructible and arbitrary `B` (Input 2.1 of the instruction
  file). It is deduced from the proper case `g` and from base change; neither is available in
  derived form.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### The projection morphism of `Lg^* ⊣ Rg_*` -/

section Proper

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The projection morphism `PF^*_g : Rg_* A ⊗ᴸ B ⟶ Rg_* (A ⊗ᴸ Lg^* B)` of the derived
adjunction `Lg^* ⊣ Rg_*`: the mate of `Lg^* (Rg_* A ⊗ᴸ B) ≅ Lg^* Rg_* A ⊗ᴸ Lg^* B ⟶ A ⊗ᴸ Lg^* B`.
It is the derived projection formula for `Rg_*` when it is an isomorphism, which is expected
for `g` proper. -/
noncomputable def properProjectionMorphism
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (padicAlgClSheaf Z ℓ)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicAlgClSheaf Y ℓ))) :
    (R((g)_*⟦ℚ̄_ℓ⟧)).obj A ⊗ B ⟶ (R((g)_*⟦ℚ̄_ℓ⟧)).obj (A ⊗ (L((g)^*⟦ℚ̄_ℓ⟧)).obj B) :=
  (derivedUpperStarLowerStarAdjunction ℓ g).projectionMorphism A B

@[reassoc]
lemma properProjectionMorphism_natural_right
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (padicAlgClSheaf Z ℓ)))
    {B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicAlgClSheaf Y ℓ))} (h : B ⟶ B') :
    (R((g)_*⟦ℚ̄_ℓ⟧)).obj A ◁ h ≫ properProjectionMorphism ℓ g A B' =
      properProjectionMorphism ℓ g A B ≫
        (R((g)_*⟦ℚ̄_ℓ⟧)).map (A ◁ (L((g)^*⟦ℚ̄_ℓ⟧)).map h) :=
  (derivedUpperStarLowerStarAdjunction ℓ g).projectionMorphism_natural_right A h

end Proper

/-! ### The projection comparison of `Dj_! ⊣ Lj^*` -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The derived adjunction `Dj_! ⊣ Lj^*` along an open immersion `j`, with the derived pullback
`L((j)^*⟦ℚ̄_ℓ⟧)` (rather than the levelwise `D((j)^*⟦ℚ̄_ℓ⟧)`) as right adjoint. -/
noncomputable def derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction :
    D((j)_!open⟦ℚ̄_ℓ⟧) ⊣ L((j)^*⟦ℚ̄_ℓ⟧) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction ℓ j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion ℓ j).symm

/-- The projection comparison `q_{j,M,N} : Dj_! (M ⊗ᴸ Lj^* N) ⟶ Dj_! M ⊗ᴸ N` of the adjunction
`Dj_! ⊣ Lj^*` along an open immersion `j`: the adjoint of
`M ⊗ᴸ Lj^* N ⟶ Lj^* Dj_! M ⊗ᴸ Lj^* N ⟶ Lj^* (Dj_! M ⊗ᴸ N)`. -/
noncomputable def openImmersionProjectionComparison
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (padicAlgClSheaf U ℓ)))
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ))) :
    (D((j)_!open⟦ℚ̄_ℓ⟧)).obj (M ⊗ (L((j)^*⟦ℚ̄_ℓ⟧)).obj N) ⟶ (D((j)_!open⟦ℚ̄_ℓ⟧)).obj M ⊗ N :=
  (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction ℓ j).projectionComparison M N

/-- **The derived projection formula for the extension by zero**: the projection comparison
`q_j` along an open immersion is an isomorphism. See the module docstring. -/
instance isIso_openImmersionProjectionComparison
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (padicAlgClSheaf U ℓ)))
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ))) :
    IsIso (openImmersionProjectionComparison ℓ j M N) :=
  sorry

@[reassoc]
lemma openImmersionProjectionComparison_natural_right
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (padicAlgClSheaf U ℓ)))
    {N N' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ))} (h : N ⟶ N') :
    (D((j)_!open⟦ℚ̄_ℓ⟧)).map (M ◁ (L((j)^*⟦ℚ̄_ℓ⟧)).map h) ≫
        openImmersionProjectionComparison ℓ j M N' =
      openImmersionProjectionComparison ℓ j M N ≫ (D((j)_!open⟦ℚ̄_ℓ⟧)).obj M ◁ h :=
  Adjunction.projectionComparison_natural_right
    (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction ℓ j) M h

@[reassoc]
lemma inv_openImmersionProjectionComparison_natural_right
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (padicAlgClSheaf U ℓ)))
    {N N' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ))} (h : N ⟶ N') :
    (D((j)_!open⟦ℚ̄_ℓ⟧)).obj M ◁ h ≫ inv (openImmersionProjectionComparison ℓ j M N') =
      inv (openImmersionProjectionComparison ℓ j M N) ≫
        (D((j)_!open⟦ℚ̄_ℓ⟧)).map (M ◁ (L((j)^*⟦ℚ̄_ℓ⟧)).map h) := by
  rw [IsIso.eq_inv_comp, ← openImmersionProjectionComparison_natural_right_assoc,
    IsIso.hom_inv_id, Category.comp_id]

end OpenImmersion

/-! ### The exceptional projection morphism -/

section OfCompactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The identification `Lf^* ≅ Lg^* ⋙ Li^*` of the derived pullback along `f` with the
composite of the derived pullbacks along the two halves of a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`. -/
noncomputable def leftDerivedUpperStarCompactificationIso :
    L((f)^*⟦ℚ̄_ℓ⟧) ≅ L((c.g)^*⟦ℚ̄_ℓ⟧) ⋙ L((c.i)^*⟦ℚ̄_ℓ⟧) :=
  eqToIso (congrArg (fun h : X ⟶ Y ↦ L((h)^*⟦ℚ̄_ℓ⟧)) c.comm) ≪≫ leftDerivedUpperStarComp ℓ c.i c.g

/-- The derived exceptional projection morphism
`PF^!_{f,K,B} : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)` with respect to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` of `f`: the projection morphism `PF^*_g` at `Di_! K`, the inverse of the
projection comparison `q_i`, and the identification `Li^* Lg^* B ≅ Lf^* B`. -/
noncomputable def exceptionalProjectionMorphismOfCompactification
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicAlgClSheaf Y ℓ))) :
    (Rf_!(c)⟦ℚ̄_ℓ⟧).obj K ⊗ B ⟶ (Rf_!(c)⟦ℚ̄_ℓ⟧).obj (K ⊗ (L((f)^*⟦ℚ̄_ℓ⟧)).obj B) :=
  properProjectionMorphism ℓ c.g ((D((c.i)_!open⟦ℚ̄_ℓ⟧)).obj K) B ≫
    (R((c.g)_*⟦ℚ̄_ℓ⟧)).map
      (inv (openImmersionProjectionComparison ℓ c.i K ((L((c.g)^*⟦ℚ̄_ℓ⟧)).obj B)) ≫
        (D((c.i)_!open⟦ℚ̄_ℓ⟧)).map
          (K ◁ (leftDerivedUpperStarCompactificationIso ℓ c).inv.app B))

/-- The exceptional projection morphism is natural in its second variable. -/
@[reassoc]
lemma exceptionalProjectionMorphismOfCompactification_natural_right
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ)))
    {B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicAlgClSheaf Y ℓ))} (h : B ⟶ B') :
    (Rf_!(c)⟦ℚ̄_ℓ⟧).obj K ◁ h ≫ exceptionalProjectionMorphismOfCompactification ℓ c K B' =
      exceptionalProjectionMorphismOfCompactification ℓ c K B ≫
        (Rf_!(c)⟦ℚ̄_ℓ⟧).map (K ◁ (L((f)^*⟦ℚ̄_ℓ⟧)).map h) :=
  sorry

end OfCompactification

section Chosen

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The **derived exceptional projection morphism**
`PF^!_{f,K,B} : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)` for the chosen compactification of `f`. -/
noncomputable def exceptionalProjectionMorphism
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicAlgClSheaf Y ℓ))) :
    (R(f)_!⟦ℚ̄_ℓ⟧).obj K ⊗ B ⟶ (R(f)_!⟦ℚ̄_ℓ⟧).obj (K ⊗ (L((f)^*⟦ℚ̄_ℓ⟧)).obj B) :=
  exceptionalProjectionMorphismOfCompactification ℓ (HasCompactification.compactification f) K B

/-- The exceptional projection morphism is natural in its second variable. -/
@[reassoc]
lemma exceptionalProjectionMorphism_natural_right
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ)))
    {B B' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicAlgClSheaf Y ℓ))} (h : B ⟶ B') :
    (R(f)_!⟦ℚ̄_ℓ⟧).obj K ◁ h ≫ exceptionalProjectionMorphism ℓ f K B' =
      exceptionalProjectionMorphism ℓ f K B ≫ (R(f)_!⟦ℚ̄_ℓ⟧).map (K ◁ (L((f)^*⟦ℚ̄_ℓ⟧)).map h) :=
  exceptionalProjectionMorphismOfCompactification_natural_right ℓ _ K h

/-- **The derived projection formula for `Rf_!`**: the exceptional projection morphism
`PF^!_{f,K,B}` is an isomorphism for `K` bounded constructible and `B` arbitrary. See the module
docstring. -/
lemma isIso_exceptionalProjectionMorphism
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ)))
    (hK : boundedConstructible (padicAlgClSheaf X ℓ) K)
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (padicAlgClSheaf Y ℓ))) :
    IsIso (exceptionalProjectionMorphism ℓ f K B) :=
  sorry

end Chosen

end AlgebraicGeometry.ProEtale.PadicAlgClRing
