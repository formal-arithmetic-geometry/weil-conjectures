/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import Submission.WeilConjectures.SixFunctors.OpenClosed.Derived

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Base change for the exceptional inverse image against an open immersion

For a cartesian square of schemes
```
  X' --g'--> X
  |          |
  f'         f
  v          v
  Y' --g---> Y
```
with `f`, `f'` admitting compactifications, and torsion coefficients `Λ`, the compact-support
base change `Ex_! : Lg^* Rf_! ⟶ Rf'_! Lg'^*` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`), and the exceptional
inverse images `Rf^!`, `Rf'^!` are right adjoints of `Rf_!`, `Rf'_!`. The *base-change
comparison* of the exceptional inverse image is the mate of `Ex_!⁻¹`,
```
  β : Lg'^* Rf^! ⟶ Rf'^! Lg^*,
```
whose transpose under `Rf'_! ⊣ Rf'^!` is `Rf'_! Lg'^* Rf^! ≅ Lg^* Rf_! Rf^! ⟶ Lg^*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`). It is not an isomorphism for
an arbitrary `g`; it is one when `g` is an open immersion
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion`,
blueprint `prop-exc-base-change-proper` and `cor-exc-base-change-open-immersion-general`).

## The argument

For an open immersion `g` the pullbacks `Lg^*`, `Lg'^*` are themselves right adjoints, of the
extensions by zero `g_!`, `g'_!`. The iterated mate of a square of left adjoints is its
conjugate (`CategoryTheory.iterated_mateEquiv_conjugateEquiv`), so `β` is the conjugate of the
transformation
```
  γ : g_! Rf'_! ⟶ Rf_! g'_!
```
between the left adjoints of `Rf'^! Lg^*` and `Lg'^* Rf^!`, and `β` is invertible if and only if
`γ` is. Invertibility of `γ` is tested on the open `Y'` and on its closed complement `Z`
(`AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_closedComplement_map`):

* over `Y'`, `Lg^* γ` is a composite of the invertible units `𝟭 ≅ Lg^* g_!`, `𝟭 ≅ Lg'^* g'_!`
  and of `Ex_!⁻¹`;
* over `Z`, both sides vanish: `Li^* g_! = 0`, and `Li^* Rf_! g'_! ≅ Rf_{Z,!} Li'^* g'_! = 0` by
  compact-support base change along `i` and since the ranges of `i'` and `g'` are disjoint.

This is a different route from the blueprint proof of `prop-exc-base-change-proper` (closed
support triangle and dual base change), and it does not need `f` to be proper.

## Main definitions and statements

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`: `β : Lg'^* Rf^! ⟶ Rf'^! Lg^*`.
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ L₁' : C ⥤ D} {R₁ R₁' : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ R₂' : F ⥤ E}

/-- Whether the mate of a 2-square is invertible does not depend on the choice of the left
adjoints up to isomorphism, nor on the choice of their right adjoints: transporting the square
along isomorphisms `L₁ ≅ L₁'` and `L₂ ≅ L₂'` changes its mate by whiskering with the invertible
conjugates (`CategoryTheory.conjugateEquiv_mateEquiv_vcomp`,
`CategoryTheory.mateEquiv_conjugateEquiv_vcomp`). -/
lemma isIso_mateEquiv_whiskerLeft_whiskerRight (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁')
    (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂' ⊣ R₂') (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂')
    (α : TwoSquare G L₁ L₂ H) [IsIso (mateEquiv adj₁ adj₂ α).natTrans] :
    IsIso (mateEquiv adj₁' adj₂' ((α.whiskerLeft e₁.hom).whiskerRight e₂.inv)).natTrans := by
  rw [mateEquiv_conjugateEquiv_vcomp adj₁' adj₂ adj₂', conjugateEquiv_mateEquiv_vcomp adj₁' adj₁]
  dsimp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.natTrans]
  infer_instance

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- For an open immersion `g`, the derived extension by zero `D(g_!)` is left adjoint to the
derived pullback `Lg^*`: the adjunction `D(g_!) ⊣ D(g^*)` transported along `Lg^* ≅ D(g^*)`. -/
noncomputable def derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction {V T : Scheme.{u}}
    (j : V ⟶ T) [IsOpenImmersion j] :
    D((j)_!open[ModuleCat.{u + 1} Λ]) ⊣ L((j)^*[ModuleCat.{u + 1} Λ]) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction _ j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory _ j).symm

instance isIso_derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction_unit
    {V T : Scheme.{u}} (j : V ⟶ T) [IsOpenImmersion j] :
    IsIso (derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ j).unit := by
  simp only [derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction]
  rw [Adjunction.ofNatIsoRight_unit]
  infer_instance

/-- Blueprint `prop-exc-base-change-proper`: Base change for a proper morphism, against an open
immersion.

Blueprint `cor-exc-base-change-open-immersion-general`: Base change for an arbitrary morphism,
against an open immersion.

For a cartesian square `g' ≫ f = f' ≫ g` with `g` an open immersion, `f`, `f'` admitting
compactifications and torsion coefficients `Λ`, the base-change comparison
`β : Lg'^* Rf^! ⟶ Rf'^! Lg^*` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`)
is an isomorphism. The ambient right adjoints `Rf^!`, `Rf'^!` of the blueprint's datum are the
exceptional inverse images, which exist for torsion coefficients
(`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek`, blueprint
`thm-amb-etale-exceptional-adjoint`). In particular this applies to the passage from an affine
open of the base to the base.

`f` need not be proper: `β` is the conjugate of `γ : g_! Rf'_! ⟶ Rf_! g'_!`, which is checked to
be invertible on the open `Y'` and on its closed complement; see the module docstring. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion [HasCompactification f]
    [HasCompactification f'] [QuasiCompact f] [QuasiCompact f'] [IsOpenImmersion g]
    (sq : IsPullback g' f' f g) :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  have : IsOpenImmersion g' := MorphismProperty.of_isPullback sq.flip inferInstance
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  set adjG' := derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ g'
  set adjG := derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ g
  set adjf := rightDerivedUpperShriekAdjunction Λ f
  set adjf' := rightDerivedUpperShriekAdjunction Λ f'
  set Ex := rightDerivedLowerShriekBaseChangeMap Λ sq
  let γ := (mateEquiv adjG' adjG).symm (TwoSquare.mk _ _ _ _ (inv Ex))
  have hβ : rightDerivedUpperShriekBaseChangeMap Λ sq =
      conjugateEquiv (adjG'.comp adjf) (adjf'.comp adjG) γ := by
    rw [← iterated_mateEquiv_conjugateEquiv]
    simp only [γ, Equiv.apply_symm_apply]
    rfl
  rw [hβ]
  suffices IsIso γ by infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hγ : γ.app M = D((g)_!open[ModuleCat.{u + 1} Λ]).map
      ((R(f')_![ModuleCat.{u + 1} Λ]).map (adjG'.unit.app M)) ≫
      D((g)_!open[ModuleCat.{u + 1} Λ]).map ((inv Ex).app _) ≫ adjG.counit.app _ := by
    simp [γ]
  refine isIso_of_isIso_leftDerivedUpperStar_closedComplement_map _ g _ ?_ ?_
  · -- over the open `Y'`
    rw [hγ, Functor.map_comp, Functor.map_comp]
    have : IsIso (L((g)^*[ModuleCat.{u + 1} Λ]).map (adjG.counit.app
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj (D((g')_!open[ModuleCat.{u + 1} Λ]).obj M)))) := by
      have h := adjG.right_triangle_components
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj (D((g')_!open[ModuleCat.{u + 1} Λ]).obj M))
      have : IsIso (adjG.unit.app (L((g)^*[ModuleCat.{u + 1} Λ]).obj
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj (D((g')_!open[ModuleCat.{u + 1} Λ]).obj M)))) :=
        inferInstance
      have : IsIso (adjG.unit.app (L((g)^*[ModuleCat.{u + 1} Λ]).obj
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj (D((g')_!open[ModuleCat.{u + 1} Λ]).obj M))) ≫
          L((g)^*[ModuleCat.{u + 1} Λ]).map (adjG.counit.app
            ((R(f)_![ModuleCat.{u + 1} Λ]).obj (D((g')_!open[ModuleCat.{u + 1} Λ]).obj M)))) := by
        rw [h]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_left (adjG.unit.app _) _
    infer_instance
  · -- over the closed complement `Z` both sides vanish
    have hsrc : IsZero ((L((g.closedComplement)^*[ModuleCat.{u + 1} Λ])).obj
        ((D((g)_!open[ModuleCat.{u + 1} Λ])).obj ((R(f')_![ModuleCat.{u + 1} Λ]).obj M))) :=
      isZero_leftDerivedUpperStar_closedComplement_obj_openImmersionLowerShriek _ g _
    have sqi := IsPullback.of_hasPullback f g.closedComplement
    have : HasCompactification (pullback.snd f g.closedComplement) :=
      ((HasCompactification.compactification f).ofIsPullback sqi).hasCompactification
    have : QuasiCompact (pullback.snd f g.closedComplement) :=
      MorphismProperty.of_isPullback sqi ‹QuasiCompact f›
    have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sqi
    have hdisj : Disjoint (Set.range (pullback.fst f g.closedComplement).base)
        (Set.range g'.base) := by
      rw [Set.disjoint_left]
      rintro _ ⟨z, rfl⟩ ⟨x', hx'⟩
      have h1 : f.base (g'.base x') = g.base (f'.base x') := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, sq.w]
      have h2 : f.base ((pullback.fst f g.closedComplement).base z) =
          g.closedComplement.base ((pullback.snd f g.closedComplement).base z) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      have h3 : g.closedComplement.base ((pullback.snd f g.closedComplement).base z) ∈
          Set.range g.closedComplement.base := ⟨_, rfl⟩
      rw [g.range_closedComplement, ← h2, ← hx', h1] at h3
      exact h3 ⟨_, rfl⟩
    have hz :=
      isZero_leftDerivedUpperStar_obj_mapDerivedCategory_openImmersionLowerShriek_of_disjoint_range
        (ModuleCat.{u + 1} Λ) g' (pullback.fst f g.closedComplement) hdisj M
    have htgt : IsZero ((L((g.closedComplement)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(f)_![ModuleCat.{u + 1} Λ]).obj ((D((g')_!open[ModuleCat.{u + 1} Λ])).obj M))) :=
      (Functor.map_isZero (R(pullback.snd f g.closedComplement)_![ModuleCat.{u + 1} Λ]) hz).of_iso
        ((asIso (rightDerivedLowerShriekBaseChangeMap Λ sqi)).app _)
    exact ⟨⟨0, hsrc.eq_of_src _ _, htgt.eq_of_src _ _⟩⟩

section ReductionToProper

variable [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
  (sq : IsPullback g' f' f g)

end ReductionToProper

end Etale

end AlgebraicGeometry
