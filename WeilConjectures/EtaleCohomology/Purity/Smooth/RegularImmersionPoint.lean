/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# The fundamental class of a section

Let `p : X ⟶ Y` be proper and `s : Y ⟶ X` a section of `p` which is a closed immersion, such as
a `k`-point of a proper `k`-scheme. Part (c) of `sk-thm-regular` identifies the fundamental
class of `s` with the isomorphism `Φ_s` assembled from the orientations of `p` and of
`p ∘ s = 𝟙` through the composition law `Rs^! Rp^! ≅ R(p ∘ s)^! = 𝟙`. This file constructs that
isomorphism and states the identification.

The composition law is read through the adjunctions: the composite `Rp_! Rs_!` is left adjoint
to `Rs^! Rp^!`, and `Λ_Y ≅ Rp_! Rs_! Λ_Y` by the units of the pullback–pushforward adjunctions
(`AlgebraicGeometry.Etale.sectionUnitClass`, an isomorphism since `s ≫ p = 𝟙`). The map
`Φ_s : Λ_Y ⟶ Rs^! Rp^! Λ_Y` (`AlgebraicGeometry.Etale.sectionPurityMap`) is the transpose of
its inverse; the orientation of the identity is the identity.

## Main definitions

- `AlgebraicGeometry.Etale.supportedUnitClass`: the class `1 ∈ H^0_Z(X, Ri_! Λ_Z)` of a closed
  immersion `i : Z ⟶ X`, through which every class with supports factors
  (`AlgebraicGeometry.Etale.eq_supportedUnitClass_comp_supportedClassMap`).
- `AlgebraicGeometry.Etale.sectionUnitClass`: `Λ_Y ⟶ Rp_! Rs_! Λ_Y` for a section `s` of `p`.
- `AlgebraicGeometry.Etale.sectionPurityMap`: the isomorphism `Φ_s : Λ_Y ⟶ Rs^! Rp^! Λ_Y`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_sectionUnitClass`: `Λ_Y ⟶ Rp_! Rs_! Λ_Y` is an isomorphism.
- `AlgebraicGeometry.Etale.exists_fundamentalClassMap_comp_eq_sectionPurityMap`
  (`sk-thm-regular` (c) for `k`-points): for the orientation `γ` of a smooth proper
  `a : X ⟶ Spec k` given by smooth purity, `Rx^!(γ) ∘ cl_x = Φ_x` for every `k`-point `x`.
- `AlgebraicGeometry.Etale.unit_comp_map_comp_counit_eq_sectionUnitClass_comp`: the trace of
  the image in `H^0(Y, Rp_* L)` of a class with supports on `s` is computed by its adjoint.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section SupportedUnitClass

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The class `1 ∈ H^0_Z(X, Ri_! Λ_Z)` of a closed immersion `i : Z ⟶ X`, a morphism
`Λ_X ⟶ Ri_! Λ_Z`: for the chosen compactification `(j, g)` of `i`, the unit of
`Lg^* ⋙ Lj^* ⊣ Rj_* ⋙ Rg_*` read through `Lj^* Lg^* Λ_X ≅ Λ_Z` and the forget-supports
isomorphism `Ri_! ≅ Rj_* ⋙ Rg_*`. -/
noncomputable def supportedUnitClass :
    constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Z) :=
  ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) _).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) _)).homEquiv _ _
      (compactificationConstantComplexIso Λ i).hom ≫
    inv ((rightDerivedLowerShriekToLowerStarComp (ModuleCat.{u + 1} Λ) i).app _)

/-- The adjoint of the class `1 ⬝ Ri_!(c)` is `c`. -/
lemma supportedClassMap_supportedUnitClass_comp
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (c : constantComplex Λ Z ⟶ (R(i)^![ModuleCat.{u + 1} Λ]).obj L) :
    supportedClassMap Λ i (supportedUnitClass Λ i ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map c) = c := by
  simp only [supportedClassMap, rightDerivedLowerShriekTranspose, supportedUnitClass,
    Category.assoc, NatTrans.naturality, IsIso.inv_hom_id_assoc]
  rw [Adjunction.homEquiv_naturality_right_symm, Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]

/-- Every class with supports `γ : Λ_X ⟶ Ri_! Ri^! L` is the class `1` followed by `Ri_!` of its
adjoint `Λ_Z ⟶ Ri^! L` (`AlgebraicGeometry.Etale.supportedClassMap`). -/
lemma eq_supportedUnitClass_comp_supportedClassMap
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![ModuleCat.{u + 1} Λ]).obj L)) :
    γ = supportedUnitClass Λ i ≫
      (R(i)_![ModuleCat.{u + 1} Λ]).map (supportedClassMap Λ i γ) :=
  (supportedClassMap_bijective Λ i L).injective
    (supportedClassMap_supportedUnitClass_comp Λ i _).symm

end SupportedUnitClass

section Section

variable {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] (s : Y ⟶ X) [IsClosedImmersion s]

/-- For a proper `p : X ⟶ Y` and a closed immersion `s : Y ⟶ X`, the morphism
`Λ_Y ⟶ Rp_! Rs_! Λ_Y`: the unit `Λ_Y ⟶ Rp_* Lp^* Λ_Y = Rp_* Λ_X`, followed by `Rp_*` of the
class `1 ∈ H^0_Y(X, Rs_! Λ_Y)` (`AlgebraicGeometry.Etale.supportedUnitClass`) and
`Rp_* ≅ Rp_!`. For a section `s` of `p` it is an isomorphism
(`AlgebraicGeometry.Etale.isIso_sectionUnitClass`). -/
noncomputable def sectionUnitClass :
    𝟙_ (DerivedCategoryModule Λ Y) ⟶
      (R(p)_![ModuleCat.{u + 1} Λ]).obj ((R(s)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ Y)) :=
  (derivedUpperStarLowerStarAdjunction _ p).unit.app (constantComplex Λ Y) ≫
    (R((p)_*[ModuleCat.{u + 1} Λ])).map
      ((leftDerivedUpperStarConstantComplexIso Λ p).hom ≫ supportedUnitClass Λ s) ≫
    (rightDerivedLowerShriekIsoRightDerivedLowerStar _ p).inv.app _

/-- For a section `s` of the proper `p`, the morphism `Λ_Y ⟶ Rp_! Rs_! Λ_Y` is an isomorphism:
up to isomorphisms it is the unit of the composite adjunction
`Lp^* ⋙ Lg^* ⋙ Lj^* ⊣ Rj_* ⋙ Rg_* ⋙ Rp_*` (for the compactification `(j, g)` of `s`), whose
left adjoint is isomorphic to `L(j ≫ g ≫ p)^* = L(𝟙)^* ≅ 𝟭`, hence fully faithful. -/
theorem isIso_sectionUnitClass (h : s ≫ p = 𝟙 Y) : IsIso (sectionUnitClass Λ p s) := by
  set c := HasCompactification.compactification s
  let adjgi := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.g).comp
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.i)
  let adj := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).comp adjgi
  let e : L((p)^*[ModuleCat.{u + 1} Λ]) ⋙ (L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙
      L((c.i)^*[ModuleCat.{u + 1} Λ])) ≅ 𝟭 _ :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (leftDerivedUpperStarComp _ c.g p).symm _ ≪≫
      (leftDerivedUpperStarComp _ c.i (c.g ≫ p) (𝟙 Y)
        (by rw [← Category.assoc, ← c.comm, h])).symm ≪≫
      leftDerivedUpperStarId _ Y
  have : (L((p)^*[ModuleCat.{u + 1} Λ]) ⋙ (L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙
      L((c.i)^*[ModuleCat.{u + 1} Λ]))).Full := Functor.Full.of_iso e.symm
  have : (L((p)^*[ModuleCat.{u + 1} Λ]) ⋙ (L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙
      L((c.i)^*[ModuleCat.{u + 1} Λ]))).Faithful := Functor.Faithful.of_iso e.symm
  have hu : sectionUnitClass Λ p s = adj.unit.app _ ≫
      (R((p)_*[ModuleCat.{u + 1} Λ])).map ((R((c.i)_*[ModuleCat.{u + 1} Λ]) ⋙
          R((c.g)_*[ModuleCat.{u + 1} Λ])).map
          ((L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙ L((c.i)^*[ModuleCat.{u + 1} Λ])).map
            (leftDerivedUpperStarConstantComplexIso Λ p).hom ≫
            (compactificationConstantComplexIso Λ s).hom) ≫
        inv ((rightDerivedLowerShriekToLowerStarComp (ModuleCat.{u + 1} Λ) s).app _)) ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar _ p).inv.app _ := by
    have nat := adjgi.unit.naturality (leftDerivedUpperStarConstantComplexIso Λ p).hom
    simp only [Functor.id_map] at nat
    simp only [sectionUnitClass, supportedUnitClass, adj, Adjunction.comp_unit_app,
      Adjunction.homEquiv_unit, Category.assoc]
    rw [reassoc_of% nat]
    simp only [Functor.map_comp, Category.assoc, Functor.comp_map, adjgi,
      Adjunction.comp_unit_app]
  rw [hu]
  infer_instance

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

The isomorphism `Φ_s : Λ_Y ⟶ Rs^! Rp^! Λ_Y` of a section `s` of a proper `p` (`s ≫ p = 𝟙`),
assembled through the composition law `Rs^! Rp^! ≅ R(s ≫ p)^! = 𝟙` with the identity
orientation of `𝟙`: the transpose, under the composite adjunction `Rp_! Rs_! ⊣ Rs^! Rp^!`, of
the inverse of `Λ_Y ≅ Rp_! Rs_! Λ_Y` (`AlgebraicGeometry.Etale.sectionUnitClass`). For `a_X`
smooth and `x` a `k`-point it is the isomorphism `Λ ≅ Rx^! Ra_X^! Λ` of Steps 1–2 of
`sk-thm-regular`, before transport along the orientation of `a_X`. -/
noncomputable def sectionPurityMap (h : s ≫ p = 𝟙 Y) :
    constantComplex Λ Y ⟶ (R(s)^![ModuleCat.{u + 1} Λ]).obj
      ((R(p)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ (DerivedCategoryModule Λ Y))) :=
  haveI := isIso_sectionUnitClass Λ p s h
  ((rightDerivedUpperShriekAdjunction _ s).comp (rightDerivedUpperShriekAdjunction _ p)).homEquiv
    _ _ (inv (sectionUnitClass Λ p s))

/-- The transpose of `Φ_s` is the inverse of `Λ_Y ≅ Rp_! Rs_! Λ_Y`. -/
lemma sectionUnitClass_comp_homEquiv_symm_sectionPurityMap (h : s ≫ p = 𝟙 Y) :
    sectionUnitClass Λ p s ≫
      (((rightDerivedUpperShriekAdjunction _ s).comp
        (rightDerivedUpperShriekAdjunction _ p)).homEquiv _ _).symm
        (sectionPurityMap Λ p s h) = 𝟙 _ := by
  haveI := isIso_sectionUnitClass Λ p s h
  simp [sectionPurityMap]

/-- The trace of the image of a class with supports on a closed immersion `s` is computed by its
adjoint: for `γ : Λ_X ⟶ Rs_! Rs^! L` and `f : L ⟶ Rp^! Λ_Y`, the composite
```
Λ_Y ──unit──▶ Rp_* Λ_X ──Rp_*(ε_s ∘ γ)──▶ Rp_* L ≅ Rp_! L ──Rp_!(f)──▶ Rp_! Rp^! Λ_Y ──ε_p──▶ Λ_Y
```
is `Λ_Y ⟶ Rp_! Rs_! Λ_Y` (`AlgebraicGeometry.Etale.sectionUnitClass`) followed by the transpose,
under `Rp_! Rs_! ⊣ Rs^! Rp^!`, of `Rs^!(f) ∘ cl`, where `cl : Λ_Y ⟶ Rs^! L` is the adjoint of
`γ` (`AlgebraicGeometry.Etale.supportedClassMap`). -/
set_option maxHeartbeats 1000000 in
lemma unit_comp_map_comp_counit_eq_sectionUnitClass_comp
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶
      (R(s)_![ModuleCat.{u + 1} Λ]).obj ((R(s)^![ModuleCat.{u + 1} Λ]).obj L))
    (f : L ⟶ (R(p)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ (DerivedCategoryModule Λ Y))) :
    (derivedUpperStarLowerStarAdjunction _ p).unit.app (constantComplex Λ Y) ≫
      (R((p)_*[ModuleCat.{u + 1} Λ])).map ((leftDerivedUpperStarConstantComplexIso Λ p).hom ≫
        γ ≫ (rightDerivedUpperShriekAdjunction _ s).counit.app L) ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar _ p).inv.app L ≫
      (R(p)_![ModuleCat.{u + 1} Λ]).map f ≫
      (rightDerivedUpperShriekAdjunction _ p).counit.app _ =
    sectionUnitClass Λ p s ≫
      (((rightDerivedUpperShriekAdjunction _ s).comp
        (rightDerivedUpperShriekAdjunction _ p)).homEquiv _ _).symm
        (supportedClassMap Λ s γ ≫ (R(s)^![ModuleCat.{u + 1} Λ]).map f) := by
  obtain ⟨c, rfl⟩ : ∃ c, γ = supportedUnitClass Λ s ≫ (R(s)_![ModuleCat.{u + 1} Λ]).map c :=
    ⟨_, eq_supportedUnitClass_comp_supportedClassMap Λ s γ⟩
  rw [supportedClassMap_supportedUnitClass_comp, Adjunction.homEquiv_counit,
    Adjunction.comp_counit_app]
  let g := (R(s)_![ModuleCat.{u + 1} Λ]).map c ≫
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) s).counit.app L
  have h₁ : (R(s)_![ModuleCat.{u + 1} Λ]).map (c ≫ (R(s)^![ModuleCat.{u + 1} Λ]).map f) ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) s).counit.app _ = g ≫ f := by
    rw [Functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg _ ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) s).counit_naturality f)
  have h₂ : (R((p)_*[ModuleCat.{u + 1} Λ])).map g ≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) p).inv.app L =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) p).inv.app _ ≫
        (R(p)_![ModuleCat.{u + 1} Λ]).map g :=
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) p).inv.naturality g
  have h₃ : sectionUnitClass Λ p s ≫ (R(p)_![ModuleCat.{u + 1} Λ]).map g =
      (derivedUpperStarLowerStarAdjunction _ p).unit.app (constantComplex Λ Y) ≫
        (R((p)_*[ModuleCat.{u + 1} Λ])).map ((leftDerivedUpperStarConstantComplexIso Λ p).hom ≫
          supportedUnitClass Λ s ≫ g) ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) p).inv.app L := by
    rw [sectionUnitClass, Category.assoc, Category.assoc, ← h₂]
    simp only [g, Functor.map_comp, Category.assoc]
  have h₄ : (R(p)_![ModuleCat.{u + 1} Λ]).map ((R(s)_![ModuleCat.{u + 1} Λ]).map
      (c ≫ (R(s)^![ModuleCat.{u + 1} Λ]).map f)) ≫
      (R(p)_![ModuleCat.{u + 1} Λ]).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) s).counit.app _) ≫
      (rightDerivedUpperShriekAdjunction _ p).counit.app (𝟙_ (DerivedCategoryModule Λ Y)) =
      (R(p)_![ModuleCat.{u + 1} Λ]).map g ≫ (R(p)_![ModuleCat.{u + 1} Λ]).map f ≫
      (rightDerivedUpperShriekAdjunction _ p).counit.app (𝟙_ (DerivedCategoryModule Λ Y)) := by
    rw [← Functor.map_comp_assoc, h₁, Functor.map_comp_assoc]
  simp only [Functor.comp_map]
  rw [h₄, reassoc_of% h₃]
  simp only [g, Functor.map_comp, Category.assoc]
end Section

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] {k : Type u} [Field k]
  [PerfectField k] [HasInvertibleExponent Λ (Spec (.of k))] {X : Scheme.{u}}
  [HasInvertibleExponent Λ X] {d : ℕ} (a : X ⟶ Spec (.of k)) [IsProper a]
  [SmoothOfRelativeDimension d a]

/-- Blueprint `sk-thm-regular`: Purity for regular closed immersions

**(c) for rational points.** Let `a : X ⟶ Spec k` be smooth and proper of pure relative
dimension `d`, with the orientation `γ : Λ_X(d)[2d] ≅ Ra^! Λ` of `sk-thm-smooth-purity`. For
every `k`-point `x : Spec k ⟶ X` (a regular closed immersion of codimension `d` with
`x ≫ a = 𝟙`), the map `cl_x : Λ ⟶ Rx^! Λ_X(d)[2d]`, `1 ↦ [x ⊂ X]`
(`AlgebraicGeometry.Etale.fundamentalClassMap`), is the isomorphism assembled from the
orientations of `a` and of `a ∘ x = 𝟙` through `Rx^! Ra^! ≅ R(a ∘ x)^!`: transported along `γ`
it is `Φ_x : Λ ≅ Rx^! Ra^! Λ` (`AlgebraicGeometry.Etale.sectionPurityMap`).

The orientation of `sk-thm-smooth-purity` is only known to exist in the repository
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`), so the statement is
existential in it. -/
theorem exists_fundamentalClassMap_comp_eq_sectionPurityMap :
    haveI := SmoothOfRelativeDimension.smooth d a
    ∃ γ : (tateObject Λ X d)⟦(2 * d : ℤ)⟧ ≅ dualizingComplex (ModuleCat.{u + 1} Λ) a,
      ∀ (x : Spec (.of k) ⟶ X) [IsRegularImmersion d x] (hx : x ≫ a = 𝟙 _),
        fundamentalClassMap Λ d x a IsRegular.isRegularLocalRing_stalk ≫
            (R(x)^![ModuleCat.{u + 1} Λ]).map γ.hom =
          sectionPurityMap Λ a x hx :=
  -- TODO: needs the canonical orientations of `sk-thm-smooth-purity` (of `a` and of `𝟙`) and
  -- Steps 1–2 of the proof of `sk-thm-regular`, comparing `Φ_x` with the frame classes.
  sorry

end Etale

end AlgebraicGeometry

