/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Rigid.BraidedTrace
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension

/-!
# Finite-level coefficient change and the compactly supported direct image

Let `S` be a finite free algebra over a commutative ring `R`, for instance a finite extension of
finite coefficient rings `A_{E,n} → A_{E',n}` with `E'/E` unramified. Derived scalar extension
`N = - ⊗ᴸ_R S = L(S ⊗_R -) : D(X_proét, R) ⥤ D(X_proét, S)` commutes with the operations:

- with the derived pullbacks `Lf^*`
  (`AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsCompUpperStarIso`);
- with extension by zero along open immersions
  (`AlgebraicGeometry.ProEtale.mapDerivedCategoryOpenLowerShriekExtendScalarsIso`);
- with the derived direct images `Rg_*`
  (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarExtendScalarsIso`);
- hence with the compactly supported direct images `Rf_!`
  (`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationExtendScalarsIso`,
  `AlgebraicGeometry.ProEtale.nonempty_rightDerivedLowerShriek_comp_iso`).

These are the natural isomorphisms of blueprint `thm-trf-finite-coefficient-map` and of the
sketch `sk-p-trace-coeff`. Being natural, they intertwine the images of every endomorphism, in
particular of the Frobenius maps; by the scalar-extension law of the categorical trace
(`CategoryTheory.Functor.trace_eq_unitEndRingHom_trace`, blueprint
`prop-trf-trace-formal-laws`, item (3)), the trace of the scalar extension of an endomorphism
of a compactly supported direct image is the image of its trace
(`AlgebraicGeometry.ProEtale.trace_rightDerivedLowerShriekOfCompactification_map_extendScalars`).

## Gaps with respect to the blueprint

- The coefficient map `ρ : A → B` is assumed finite free, so that `S ⊗_R -` is exact and its
  derived functor is computed levelwise. For a general `ρ` (such as `ℤ/ℓ² → ℤ/ℓ`) the derived
  scalar extension of pro-étale sheaves of modules is not available with its commutation
  isomorphisms.
- The derived scalar extension is not given a braided monoidal structure on the derived
  categories, and the derived categories `D(X_proét)` carry no chosen braiding; the trace law is
  therefore stated for a braided monoidal structure on `N` taken as an argument.
- The stability of `Dctf` under `N`, and the Frobenius operators of strict Weil complexes on the
  pro-étale site, are not formalised here.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Blueprint `thm-trf-finite-coefficient-map`: derived scalar extension commutes with extension
by zero along an open immersion `j`, `L(S ⊗_R -) ∘ Dj_! ≅ Dj_! ∘ L(S ⊗_R -)`, both functors
being exact. -/
noncomputable def mapDerivedCategoryOpenLowerShriekExtendScalarsIso :
    D((j)_!open[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) X) ≅
      L(sheafExtendScalars (algebraMap R S) U) ⋙ D((j)_!open[ModuleCat.{u + 1} S]) :=
  Functor.isoWhiskerLeft _
      (sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekCompSheafExtendScalarsIso j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (sheafExtendScalars (algebraMap R S) U).leftDerivedFunctorIsoMapDerivedCategory.symm _

end OpenImmersion

variable [Module.Finite R S] [Module.Free R S] [Nontrivial R]

/-- Blueprint `thm-trf-finite-coefficient-map`: derived scalar extension along a finite free
algebra commutes with the derived direct image, `L(S ⊗_R -) ∘ Rg_* ≅ Rg_* ∘ L(S ⊗_R -)`; it is
the base change map, the mate of the commutation with `Lg^*`, which is invertible by
`AlgebraicGeometry.ProEtale.isIso_mateEquiv_leftDerivedSheafExtendScalarsCompUpperStarIso_app`. -/
noncomputable def rightDerivedLowerStarExtendScalarsIso {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    R((g)_*[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) Y) ≅
      L(sheafExtendScalars (algebraMap R S) Z) ⋙ R((g)_*[ModuleCat.{u + 1} S]) :=
  have (M : _) := isIso_mateEquiv_leftDerivedSheafExtendScalarsCompUpperStarIso_app
    (R := R) (S := S) g M
  have : IsIso (mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
      (derivedUpperStarLowerStarAdjunction _ g)
      (leftDerivedSheafExtendScalarsCompUpperStarIso (R := R) (S := S) g).hom) :=
    NatIso.isIso_of_isIso_app _
  asIso (mateEquiv (derivedUpperStarLowerStarAdjunction _ g)
    (derivedUpperStarLowerStarAdjunction _ g)
    (leftDerivedSheafExtendScalarsCompUpperStarIso (R := R) (S := S) g).hom)

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Blueprint `thm-trf-finite-coefficient-map`: derived scalar extension along a finite free
algebra commutes with the compactly supported direct image attached to a compactification
`c = (X ⟶[i] Z ⟶[g] Y)`, `(Rf_! K) ⊗ᴸ_R S ≅ Rf_!(K ⊗ᴸ_R S)`: it commutes with `Di_!` and with
`Rg_*`. -/
noncomputable def rightDerivedLowerShriekOfCompactificationExtendScalarsIso
    (c : Compactification f) :
    Rf_!(c)[ModuleCat.{u + 1} R] ⋙ L(sheafExtendScalars (algebraMap R S) Y) ≅
      L(sheafExtendScalars (algebraMap R S) X) ⋙ Rf_!(c)[ModuleCat.{u + 1} S] :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedLowerStarExtendScalarsIso c.g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mapDerivedCategoryOpenLowerShriekExtendScalarsIso c.i) _ ≪≫
    Functor.associator _ _ _

variable (f) in
/-- **Finite-level coefficient change commutes with `Rf_!`** (sketch `sk-p-trace-coeff`,
blueprint `thm-trf-finite-coefficient-map`): for a finite free algebra `S` over `R` and a
compactifiable morphism `f`, there is a natural isomorphism
`(Rf_! K) ⊗ᴸ_R S ≅ Rf_!(K ⊗ᴸ_R S)`. -/
theorem nonempty_rightDerivedLowerShriek_comp_iso [HasCompactification f] :
    Nonempty (R(f)_![ModuleCat.{u + 1} R] ⋙ L(sheafExtendScalars (algebraMap R S) Y) ≅
      L(sheafExtendScalars (algebraMap R S) X) ⋙ R(f)_![ModuleCat.{u + 1} S]) :=
  ⟨rightDerivedLowerShriekOfCompactificationExtendScalarsIso _⟩

end AlgebraicGeometry.ProEtale
