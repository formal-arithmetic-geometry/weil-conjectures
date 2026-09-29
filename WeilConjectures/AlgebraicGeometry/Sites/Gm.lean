/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Adjunctions
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# The multiplicative group on the small étale site

The étale sheaf `𝔾ₘ` on a scheme `X` sends an étale `X`-scheme `U` to the group of units of
`Γ(U, 𝒪_U)`, written additively so that it is a sheaf of abelian groups. Its étale cohomology
in degrees `1` and `2` is the Picard group and the Brauer group of `X`.

The sheaf condition is reduced to étale descent for the structure sheaf: the presheaf `𝔾ₘ` is
the composite

```
  X.Etaleᵒᵖ ──etaleStructurePresheaf──▶ CommRingCat ──units──▶ AddCommGrpCat ──uliftFunctor──▶
    AddCommGrpCat
```

and the last two functors preserve limits, so it suffices that `U ↦ Γ(U, 𝒪_U)` is an étale
sheaf (`AlgebraicGeometry.Scheme.isSheaf_etaleStructurePresheaf`, the one `sorry` of this
part of the file). That reusable form is what `𝔾ₐ`, `μₙ` and sheaves of `𝒪`-modules need too.

## Main definitions

- `AlgebraicGeometry.Scheme.etaleStructurePresheaf`: `U ↦ Γ(U, 𝒪_U)` on the small étale site.
- `AlgebraicGeometry.Scheme.gmSheaf`: the sheaf `𝔾ₘ` of units on the small étale site.
- `AlgebraicGeometry.Scheme.CohomologicalPicardGroup`: `H¹(X_ét, 𝔾ₘ)`.
- `AlgebraicGeometry.Scheme.CohomologicalBrauerGroup`: `H²(X_ét, 𝔾ₘ)`.
- `AlgebraicGeometry.Scheme.gmSheafToLowerStar`: the map `𝔾ₘ ⟶ g_* 𝔾ₘ` on units.
- `AlgebraicGeometry.Scheme.gmSheafComparison`: its adjoint `g^* 𝔾ₘ ⟶ 𝔾ₘ`.
- `AlgebraicGeometry.Scheme.upperStarGmSheafIso`: `g^* 𝔾ₘ ≅ 𝔾ₘ`, whose invertibility
  (`AlgebraicGeometry.Scheme.isIso_gmSheafComparison`) is `sorry`.

## Main statements

- `AlgebraicGeometry.Scheme.isSheaf_etaleStructurePresheaf`: the structure presheaf is a sheaf
  for the small étale topology. Its proof, étale descent, is `sorry`.
- `AlgebraicGeometry.Scheme.subsingleton_cohomologicalPicardGroup_of_field`: Hilbert 90 for a
  field, `H¹(Spec K_ét, 𝔾ₘ) = 0`.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository; `sk-...` names a subsection there and the other names a statement inside
one.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The structure presheaf on the small étale site of `X`: an étale `X`-scheme `U` is sent to
the ring `Γ(U, 𝒪_U)` of its global sections,

```
  X.Etaleᵒᵖ ──(Etale.forget ⋙ Over.forget)ᵒᵖ──▶ Schemeᵒᵖ ──Γ──▶ CommRingCat
```
-/
noncomputable def etaleStructurePresheaf : X.Etaleᵒᵖ ⥤ CommRingCat.{u} :=
  (Scheme.Etale.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ

/-- **Étale descent for the structure sheaf**: the presheaf `U ↦ Γ(U, 𝒪_U)` is a sheaf for the
small étale topology. The proof is `sorry`; it is the special case for `𝒪` itself of fppf
descent for quasi-coherent modules, the small étale topology being coarser than the fppf
topology. -/
theorem isSheaf_etaleStructurePresheaf :
    Presheaf.IsSheaf X.smallEtaleTopology X.etaleStructurePresheaf :=
  sorry

/-- The presheaf `𝔾ₘ` on the small étale site of `X`: an étale `X`-scheme `U` is sent to the
group of units of `Γ(U, 𝒪_U)`, written additively and lifted to the next universe,

```
  X.Etaleᵒᵖ ──etaleStructurePresheaf──▶ CommRingCat ──unitsAddCommGrp──▶ AddCommGrpCat
    ──uliftFunctor──▶ AddCommGrpCat
```
-/
noncomputable def gmPresheaf : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  X.etaleStructurePresheaf ⋙
    (CommRingCat.unitsAddCommGrp ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})

/-- The presheaf `𝔾ₘ` is a sheaf for the small étale topology: the group of units and the
universe lift are right adjoints, hence preserve limits, so the sheaf condition follows from
étale descent for the structure sheaf. -/
theorem isSheaf_gmPresheaf : Presheaf.IsSheaf X.smallEtaleTopology X.gmPresheaf :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ _ X.isSheaf_etaleStructurePresheaf

/-- The sheaf `𝔾ₘ` on the small étale site of `X`: the sheaf of units of the structure sheaf,
written additively.

The blueprint node cited is about `𝔾ₘ`-torsors and introduces `𝔾ₘ` itself only in passing;
the block has no node of its own for the sheaf.
(blueprint: `def-sc-gm-torsor`) -/
noncomputable def gmSheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ⟨X.gmPresheaf, X.isSheaf_gmPresheaf⟩

/-- The *cohomological Picard group* `H¹(X_ét, 𝔾ₘ)` of a scheme.

It is called cohomological because the Picard group proper, the group of invertible
`𝒪_X`-modules up to isomorphism, is a different definition; that the two agree is a theorem
(blueprint: `lem-sc-h1-gm-pic`), and the invertible-module definition together with the degree
homomorphism and `Pic⁰` belong to the blueprint block `sk-def-av-pic`. Its vanishing for the
spectrum of a field is
`AlgebraicGeometry.Scheme.subsingleton_cohomologicalPicardGroup_of_field`. -/
noncomputable abbrev CohomologicalPicardGroup : Type (u + 1) := Sheaf.H X.gmSheaf 1

/-- The *cohomological Brauer group* `H²(X_ét, 𝔾ₘ)` of a scheme.

It is called cohomological because the Brauer group proper, the group of Azumaya algebras up
to Morita equivalence — Mathlib's `BrauerGroup K` for a field `K` — is a different definition;
the two agree for a quasi-compact separated scheme with an ample family of line bundles
(Gabber), which is not stated here.
(blueprint: `def-br`) -/
noncomputable abbrev CohomologicalBrauerGroup : Type (u + 1) := Sheaf.H X.gmSheaf 2

/-- **Hilbert 90** for a field: the cohomological Picard group `H¹(Spec K_ét, 𝔾ₘ)` of the
spectrum of a field vanishes.

A field has no nontrivial invertible modules, and by Hilbert 90 the étale and the Zariski
computation of `H¹` of the units agree. The three-way comparison

`{invertible 𝒪_X-modules}/≅ ≃ H¹(X_Zar, 𝒪_Xˣ) ≃ H¹(X_ét, 𝔾ₘ)`

that precedes it in the blueprint is not stated here: invertible modules belong to another
blueprint block, so they are not redefined in this one. The proof is `sorry`.
(blueprint: `cor-sc-hilbert-90-field`) -/
instance subsingleton_cohomologicalPicardGroup_of_field (K : Type u) [Field K] :
    Subsingleton (Spec (.of K)).CohomologicalPicardGroup :=
  sorry

variable {X} {Y : Scheme.{u}}

/-- The map of structure presheaves `Γ(V, 𝒪_V) ⟶ Γ(V ×_Y X, 𝒪)` on the small étale site of
`Y`, given on an étale `Y`-scheme `V` by the pullback of functions along the first projection
`V ×_Y X ⟶ V` of the base change of `V` along `g`. -/
noncomputable def etaleStructurePresheafToBaseChange (g : X ⟶ Y) :
    Y.etaleStructurePresheaf ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ g).op ⋙ X.etaleStructurePresheaf where
  app V := Scheme.Γ.map (Limits.pullback.fst V.unop.hom g).op
  naturality V W f := by
    change Scheme.Γ.map f.unop.left.op ≫ Scheme.Γ.map (Limits.pullback.fst W.unop.hom g).op =
      Scheme.Γ.map (Limits.pullback.fst V.unop.hom g).op ≫ Scheme.Γ.map _
    simp only [← Functor.map_comp, ← op_comp]
    congr 2
    exact (Limits.pullback.lift_fst _ _ _).symm

/-- The map `𝔾ₘ ⟶ g_* 𝔾ₘ` of sheaves on the small étale site of `Y`: on an étale `Y`-scheme
`V` it is the map on units `Γ(V, 𝒪_V)ˣ ⟶ Γ(V ×_Y X, 𝒪)ˣ` induced by the first projection
`V ×_Y X ⟶ V`. -/
noncomputable def gmSheafToLowerStar (g : X ⟶ Y) :
    Y.gmSheaf ⟶ (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj X.gmSheaf :=
  ⟨Functor.whiskerRight (etaleStructurePresheafToBaseChange g)
    (CommRingCat.unitsAddCommGrp ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})⟩

/-- The comparison map `g^* 𝔾ₘ ⟶ 𝔾ₘ` on the small étale site of `X`: the transpose under the
adjunction `g^* ⊣ g_*` of `AlgebraicGeometry.Scheme.gmSheafToLowerStar`. -/
noncomputable def gmSheafComparison (g : X ⟶ Y) :
    (Etale.upperStar AddCommGrpCat.{u + 1} g).obj Y.gmSheaf ⟶ X.gmSheaf :=
  ((Etale.upperStarLowerStarAdjunction _ g).homEquiv _ _).symm (gmSheafToLowerStar g)

/-- The comparison map `g^* 𝔾ₘ ⟶ 𝔾ₘ` is an isomorphism: the sheaf `𝔾ₘ` is represented by the
group scheme `𝔾_{m,X}`, whose formation commutes with base change. The proof is deferred and
is `sorry`. -/
instance isIso_gmSheafComparison (g : X ⟶ Y) : IsIso (gmSheafComparison g) :=
  sorry

/-- The pullback of `𝔾ₘ` along an arbitrary morphism of schemes is `𝔾ₘ`, via the comparison
map `AlgebraicGeometry.Scheme.gmSheafComparison`. This is the analogue for `𝔾ₘ` of
`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`, and is what identifies the target of a
pullback map on the cohomology of `𝔾ₘ`. The blueprint block uses it silently and has no node
for it. -/
noncomputable def upperStarGmSheafIso (g : X ⟶ Y) :
    (Etale.upperStar AddCommGrpCat.{u + 1} g).obj Y.gmSheaf ≅ X.gmSheaf :=
  asIso (gmSheafComparison g)

end AlgebraicGeometry.Scheme
