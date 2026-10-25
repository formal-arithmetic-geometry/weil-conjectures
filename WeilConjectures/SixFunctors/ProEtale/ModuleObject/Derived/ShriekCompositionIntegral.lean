/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition

/-!

# Composition of the derived lower shriek on bounded constructible `𝒪_E`-complexes

For a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` with ring of integers `𝒪_E` and composable morphisms
`f : X ⟶ Y`, `g : Y ⟶ S` of separated `k`-schemes of finite type, this file gives the
composition isomorphism
```
R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!
```
on bounded constructible `𝒪_E`-complexes
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicIntegers`). The construction is
that of `ProEtale.CondensedRing.boundedConstructibleLowerShriekComp` for the coefficients `E̲`,
with the integral inputs of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral`
(independence of the compactification and the exchange of proper direct image with extension by
zero, which rest on proper base change for `𝒪_E`-sheaves).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]
  (f : X ⟶ Y) (g : Y ⟶ S)

/-- For bounded constructible `𝒪_E`-sheaves, the exchange morphism
`Rp_* ⋙ j_! ⟶ i'_! ⋙ Rp'_*` of a cartesian square with `p'` proper is an isomorphism. -/
theorem isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicIntegers
    {X Z X' Z' : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
    {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
    [IsOpenImmersion j.left] [IsOpenImmersion i'.left] [IsProper p'.left]
    (sq : IsPullback p i' j p') :
    IsIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
      (Profinite.padicIntegersRingObj.{u} ℓ E) ℓ sq) := by
  rw [boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_eq]
  exact isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange'_padicIntegers ℓ E sq

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` for the derived lower shriek on
bounded constructible `𝒪_E`-sheaves, constructed as `boundedConstructibleLowerShriekComp`: for
the chosen compactifications `c` of `f` and `c'` of `g` and a compactification `d` of `p ≫ j`
with cartesian square, it chains the independence of the compactification, the composition
isomorphisms of extension by zero and of `Rf_*`, and the inverse of the exchange isomorphism
`Rp_* ⋙ j_! ≅ i'_! ⋙ Rp'_*`. -/
@[no_expose]
noncomputable def boundedConstructibleLowerShriekComp_padicIntegers :
    boundedConstructibleLowerShriek (Profinite.padicIntegersRingObj.{u} ℓ E) ℓ (f ≫ g) ≅
      boundedConstructibleLowerShriek (Profinite.padicIntegersRingObj.{u} ℓ E) ℓ f ⋙
        boundedConstructibleLowerShriek (Profinite.padicIntegersRingObj.{u} ℓ E) ℓ g :=
  let c := compactificationOverField f
  let c' := compactificationOverField g
  have hd := Compactification.exists_isPullback_overG_overI c c'
  let d := hd.choose
  let e := Compactification.overCompObjIso c c' d
  have : IsOpenImmersion (c.overI ≫ d.overI).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper e.hom.left := by
    simp only [e, Compactification.overCompObjIso, Over.isoMk_hom_left, Iso.refl_hom]
    infer_instance
  have sqe : IsPullback (𝟙 X) (c.overComp c' d).overI (c.overI ≫ d.overI) e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp [e]⟩
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicIntegers ℓ E
    sqe
  have := isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicIntegers ℓ E
    hd.choose_spec
  boundedConstructibleLowerShriekOfCompactificationIso_padicIntegers ℓ E _ (c.overComp c' d) ≪≫
    (boundedConstructibleLowerShriekRefinementIso _ ℓ sqe
      (Compactification.overCompObjIso_hom_overG c c' d)).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekComp _ ℓ c.overI d.overI) _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarComp _ ℓ d.overG c'.overG).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (boundedConstructibleLowerStarOpenImmersionLowerShriekExchange
        _ ℓ hd.choose_spec)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

end AlgebraicGeometry.ProEtale.CondensedRing
