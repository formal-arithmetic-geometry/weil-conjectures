/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Finite locally constant sheaves of sets on the small étale site

Let `Y` be a scheme. A sheaf of sets `F` on the small étale site of `Y` is *locally constant*
if there is an étale cover of `Y` over each member of which `F` is constant, and *finite
locally constant* if moreover its stalks at all geometric points are finite. These sheaves
form the category `FLC(Y)` which, together with the category `FÉt(Y)` of finite étale
`Y`-schemes (`AlgebraicGeometry.Scheme.FiniteEtale`), is the setting of the Galois theory
of finite étale covers.

## Main definitions

- `AlgebraicGeometry.Scheme.IsLocallyConstantSheafOfTypes`: locally constant sheaves of sets.
- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheafOfTypes`: finite locally constant
  sheaves of sets.
- `AlgebraicGeometry.Scheme.FiniteLocallyConstant`: the category `FLC(Y)`.
- `AlgebraicGeometry.Scheme.FiniteLocallyConstant.fiber`: the stalk functor
  `FLC(Y) ⥤ FintypeCat` at a geometric point.

## Implementation notes

The predicates `AlgebraicGeometry.Scheme.IsLocallyConstantSheaf` and
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf` of
`WeilConjectures.ConstructibleSheaf.Defs` are stated for Grothendieck abelian coefficient
categories; the definitions here are their analogues for sheaves of sets. As there, the values
live in `Type (u + 1)`, one universe above the base schemes, and the restriction of a sheaf to
a member of an étale cover is taken on the localized site.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}}

/-- A sheaf of sets `F` on the small étale site of `Y` is *locally constant* if there is an
étale cover of `Y` — a cover in `Scheme.etalePrecoverage` — such that the restriction of `F` to
the site localized at each member of the cover is constant in the sense of
`CategoryTheory.Sheaf.IsConstant`. -/
class IsLocallyConstantSheafOfTypes (F : Sheaf Y.smallEtaleTopology (Type (u + 1))) : Prop where
  exists_cover : ∃ 𝒰 : Cover.{u} etalePrecoverage Y, ∀ i : 𝒰.I₀,
    (F.over (𝒰.etalePrecoverageToEtale i)).IsConstant
      (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))

/-- Blueprint `def-galois-categories`: a sheaf of sets `F` on the small étale site of `Y` is
*finite locally constant* if it is locally constant and its stalk at every geometric point of
`Y` is finite. -/
class IsFiniteLocallyConstantSheafOfTypes (F : Sheaf Y.smallEtaleTopology (Type (u + 1))) :
    Prop extends IsLocallyConstantSheafOfTypes F, IsFiniteSheaf F

variable (Y) in
/-- Blueprint `def-galois-categories`: Finite etale covers and finite locally constant sheaves.

The category `FLC(Y)` of finite locally constant sheaves of sets on the small étale site of
`Y`, with morphisms of sheaves; the category `FÉt(Y)` of finite étale `Y`-schemes is
`AlgebraicGeometry.Scheme.FiniteEtale`. -/
protected abbrev FiniteLocallyConstant : Type (u + 2) :=
  ObjectProperty.FullSubcategory fun F : Sheaf Y.smallEtaleTopology (Type (u + 1)) ↦
    IsFiniteLocallyConstantSheafOfTypes F

namespace FiniteLocallyConstant

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

/-- Blueprint `def-galois-categories`: the stalk `F_s` of a finite locally constant sheaf at
a geometric point `s : Spec Ω ⟶ Y`, as a functor `FLC(Y) ⥤ FintypeCat`; the corresponding
fibre `|P_s|` of a finite étale `P` is `AlgebraicGeometry.Scheme.FiniteEtale.fiber`. -/
noncomputable def fiber : Y.FiniteLocallyConstant ⥤ FintypeCat.{u + 1} :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ (pointSmallEtale s).sheafFiber)
    fun F ↦ F.property.toIsFiniteSheaf.finite_sheafFiber Ω s

@[simp]
lemma fiber_obj_obj (F : Y.FiniteLocallyConstant) :
    ((fiber s).obj F).obj = (pointSmallEtale s).sheafFiber.obj F.obj := rfl

end FiniteLocallyConstant

end AlgebraicGeometry.Scheme
