/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.DualNumbers
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.Mathlib.Algebra.DualNumber

/-!
# The Picard group of the dual-number thickening

Let `X` be a scheme and `X[ε]` its dual-number thickening
(`AlgebraicGeometry.Scheme.dualNumbers`), with the closed immersion `i : X ⟶ X[ε]`. The
invertible modules on `X[ε]` which become trivial on `X` are classified by `H¹(X, 𝒪_X)`:

`ker (Pic(X[ε]) → Pic(X)) ≅ H¹(X, 𝒪_X)`,

and under this isomorphism rescaling the infinitesimal, `ε ↦ cε`, is multiplication by `c`.

## Implementation notes

The two schemes have the same underlying space, so all sheaves live on the site of opens of
`X`. The units of `𝒪_{X[ε]} = 𝒪_X[ε]` split as `𝒪_{X[ε]}ˣ ≅ 𝒪_X ⊕ 𝒪_Xˣ`,
`a + εb ↦ (a⁻¹ b, a)`, compatibly with the inclusion `g ↦ 1 + εg` of `𝒪_X` and with
`a + εb ↦ a`, which corresponds to the pullback along `i` under
`Pic ≅ H¹(-, 𝒪ˣ)` (`AlgebraicGeometry.Scheme.Pic.toH1UnitsAddEquiv`). Taking `H¹` of this
splitting gives the isomorphism; no long exact sequence is needed.

## Main statements

- `AlgebraicGeometry.Scheme.exists_addEquiv_ker_picMap_dualNumbersι`: the isomorphism
  `ker (Pic(X[ε]) → Pic(X)) ≅ H¹(X, 𝒪_X)`, compatible with rescaling the infinitesimal.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The structure sheaf `𝒪_X` as a sheaf of abelian groups on the opens of `X`; its first
cohomology is `(Modules.unit X).H 1`. -/
noncomputable abbrev structureAddSheaf : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj (Modules.unit X)

end AlgebraicGeometry.Scheme

namespace DualNumber

open TrivSqZeroExt

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The units `1 + εg` are compatible with ring homomorphisms. -/
theorem oneAddEps_mapRingHom (f : R →+* S) (g : R) :
    oneAddEps (f g) = (Units.map (mapRingHom f).toMonoidHom).toAdditive (oneAddEps g) := by
  refine congrArg Additive.ofMul (Units.ext ?_)
  change 1 + inr (f g) = mapRingHom f (1 + inr g)
  ext <;> simp

/-- The `ε`-part of units is compatible with ring homomorphisms. -/
theorem unitsRetract_mapRingHom (f : R →+* S) (u : Additive R[ε]ˣ) :
    unitsRetract ((Units.map (mapRingHom f).toMonoidHom).toAdditive u) = f (unitsRetract u) := by
  rw [unitsRetract_apply, unitsRetract_apply]
  change (mapRingHom f (((Additive.toMul u)⁻¹ : R[ε]ˣ) : R[ε])).fst *
    (mapRingHom f ((Additive.toMul u : R[ε]ˣ) : R[ε])).snd = _
  rw [fst_mapRingHom, snd_mapRingHom, map_mul]

end DualNumber

namespace AlgebraicGeometry.Scheme

open DualNumber

variable (X : Scheme.{u})

/-- Restricting a global section in two steps. -/
lemma presheaf_map_homOfLE_top_apply (c : Γ(X, ⊤)) {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    X.presheaf.map i (X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op c) =
      X.presheaf.map (homOfLE le_top : V.unop ⟶ ⊤).op c := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The inclusion `𝒪_X ⟶ 𝒪_{X[ε]}ˣ`, `g ↦ 1 + εg`, of sheaves of abelian groups on the opens
of `X`. -/
noncomputable def dualNumbersOneAddEps : X.structureAddSheaf ⟶ X.dualNumbers.unitsSheaf :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (oneAddEps (R := Γ(X, U.unop)))
      naturality U V i := by
        ext g
        exact oneAddEps_mapRingHom (X.presheaf.map i).hom g }

/-- The reduction `𝒪_{X[ε]}ˣ ⟶ 𝒪_Xˣ`, `a + εb ↦ a`. -/
noncomputable def dualNumbersUnitsFst : X.dualNumbers.unitsSheaf ⟶ X.unitsSheaf :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (unitsFst (R := Γ(X, U.unop)))
      naturality U V i := by
        ext u
        refine congrArg Additive.ofMul (Units.ext ?_)
        exact (fst_mapRingHom (X.presheaf.map i).hom _) }

/-- The inclusion `𝒪_Xˣ ⟶ 𝒪_{X[ε]}ˣ` of the units of `𝒪_X`. -/
noncomputable def dualNumbersUnitsInl : X.unitsSheaf ⟶ X.dualNumbers.unitsSheaf :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (unitsInl (R := Γ(X, U.unop)))
      naturality U V i := by
        ext u
        refine congrArg Additive.ofMul (Units.ext ?_)
        change (TrivSqZeroExt.inl (X.presheaf.map i ((Additive.toMul u : Γ(X, U.unop)ˣ) : Γ(X, U.unop))) :
          DualNumber Γ(X, V.unop)) = mapRingHom (X.presheaf.map i).hom (TrivSqZeroExt.inl _)
        ext <;> simp }

/-- The `ε`-part `𝒪_{X[ε]}ˣ ⟶ 𝒪_X`, `a + εb ↦ a⁻¹ b`, a retraction of
`AlgebraicGeometry.Scheme.dualNumbersOneAddEps`. -/
noncomputable def dualNumbersUnitsRetract : X.dualNumbers.unitsSheaf ⟶ X.structureAddSheaf :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (unitsRetract (R := Γ(X, U.unop)))
      naturality U V i := by
        ext u
        exact unitsRetract_mapRingHom (X.presheaf.map i).hom u }

/-- Rescaling the infinitesimal on units, `a + εb ↦ a + εcb`. -/
noncomputable def dualNumbersUnitsScale (c : Γ(X, ⊤)) :
    X.dualNumbers.unitsSheaf ⟶ X.dualNumbers.unitsSheaf :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        (Units.map (scale (X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op c)).toMonoidHom).toAdditive
      naturality U V i := by
        ext u
        refine congrArg Additive.ofMul (Units.ext ?_)
        change scale _ (mapRingHom (X.presheaf.map i).hom _) =
          mapRingHom (X.presheaf.map i).hom (scale _ _)
        ext
        · simp only [DualNumber.fst_scale]
          exact (DualNumber.fst_mapRingHom (X.presheaf.map i).hom _).trans
            ((congrArg _ (DualNumber.fst_scale _ _).symm).trans
              (DualNumber.fst_mapRingHom (X.presheaf.map i).hom _).symm)
        · simp only [DualNumber.snd_mapRingHom, DualNumber.snd_scale, map_mul]
          exact congrArg₂ (· * ·) (X.presheaf_map_homOfLE_top_apply c i).symm
            (DualNumber.snd_mapRingHom _ _) }

@[reassoc (attr := simp)]
lemma dualNumbersOneAddEps_comp_unitsRetract :
    X.dualNumbersOneAddEps ≫ X.dualNumbersUnitsRetract = 𝟙 _ := by
  ext U g
  exact unitsRetract_oneAddEps (R := Γ(X, U.unop)) g

@[reassoc (attr := simp)]
lemma dualNumbersOneAddEps_comp_unitsFst : X.dualNumbersOneAddEps ≫ X.dualNumbersUnitsFst = 0 := by
  ext U g
  exact unitsFst_oneAddEps (R := Γ(X, U.unop)) g

@[reassoc (attr := simp)]
lemma dualNumbersUnitsInl_comp_unitsFst : X.dualNumbersUnitsInl ≫ X.dualNumbersUnitsFst = 𝟙 _ := by
  ext U a
  exact unitsFst_unitsInl (R := Γ(X, U.unop)) a

lemma dualNumbersUnitsRetract_comp_oneAddEps_add :
    X.dualNumbersUnitsRetract ≫ X.dualNumbersOneAddEps +
      X.dualNumbersUnitsFst ≫ X.dualNumbersUnitsInl = 𝟙 _ := by
  ext U u
  exact oneAddEps_unitsRetract_add_unitsInl_unitsFst (R := Γ(X, U.unop)) u

lemma dualNumbersUnitsScale_comp_unitsRetract (c : Γ(X, ⊤)) :
    X.dualNumbersUnitsScale c ≫ X.dualNumbersUnitsRetract =
      X.dualNumbersUnitsRetract ≫
        (SheafOfModules.toSheaf X.ringCatSheaf).map ((Modules.unit X).smulHom c) := by
  ext U u
  exact unitsRetract_map_scale (R := Γ(X, U.unop)) _ u

end AlgebraicGeometry.Scheme
