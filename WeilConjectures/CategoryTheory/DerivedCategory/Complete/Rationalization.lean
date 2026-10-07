/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Localization.Linear
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Shift.Linear
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.RingTheory.Localization.Defs

/-!

# Rationalization of an `R`-linear triangulated category

Let `C` be a triangulated category which is linear over a commutative ring `R`, with
`R`-linear shift functors, and let `M` be a submonoid of `R`. An object `X` of `C` is
*`M`-torsion* if `m • 𝟙 X = 0` for some `m ∈ M`. The `M`-torsion objects form a
triangulated subcategory `Rationalization.torsion M C`, and the *rationalization*

```
  Rationalization M C  :=  C / (M-torsion objects)
```

is the Verdier quotient by it: the localization of `C` at the class
`Rationalization.W M C` of morphisms whose mapping cone is annihilated by an element of
`M`. It is again a triangulated category, and the localization functor
`Rationalization.Q M C : C ⥤ Rationalization M C` is a triangulated functor.

For `m ∈ M` the mapping cone of `m • 𝟙 X` is annihilated by `m²`
(`Rationalization.smul_id_cone_eq_zero`), so the morphisms `m • 𝟙 X` are inverted in the
rationalization. Consequently every `m ∈ M` acts invertibly on the `Hom` groups of
`Rationalization M C`, and the rationalization is linear over any localization `A` of `R`
at `M` (`Rationalization.linear`), compatibly with its `R`-linear structure
(`Rationalization.algebraMap_smul`). Inverting a single element `π` of `R` is the case
`M = Submonoid.powers π`; the case of interest downstream is that of the ring of integers
`R = 𝒪_E` of an `ℓ`-adic field `E`, with `M` its nonzero elements and `A = E`.

## Main definitions

- `CategoryTheory.Rationalization.torsion` : the `M`-torsion objects of `C`.
- `CategoryTheory.Rationalization.W` : the morphisms with `M`-torsion mapping cone.
- `CategoryTheory.Rationalization` : the Verdier quotient of `C` by the `M`-torsion
  objects, a triangulated category.
- `CategoryTheory.Rationalization.Q` : the localization functor `C ⥤ Rationalization M C`.
- `CategoryTheory.Rationalization.linear` : the `A`-linear structure, for `A` a
  localization of `R` at `M`.
- `CategoryTheory.Rationalization.map` : the triangulated, `A`-linear functor
  `Rationalization M C ⥤ Rationalization M C'` induced by an `R`-linear triangulated functor
  `F : C ⥤ C'`, with `Rationalization.mapQIso : Q ⋙ map F ≅ F ⋙ Q` and the isomorphisms
  `Rationalization.mapId`, `Rationalization.mapComp` and `Rationalization.mapIso`.

## Main results

- `CategoryTheory.Rationalization.instIsTriangulatedTorsion` : the `M`-torsion objects form
  a triangulated subcategory.
- `CategoryTheory.Rationalization.W_smul_id` : `m • 𝟙 X` lies in `W M C` for `m ∈ M`.
- `CategoryTheory.Rationalization.isIso_smul_id` : `m • 𝟙 Y` is an isomorphism of the
  rationalization for `m ∈ M`.
- `CategoryTheory.Rationalization.W_map` : an `R`-linear triangulated functor sends morphisms
  with `M`-torsion mapping cone to morphisms with `M`-torsion mapping cone.

-/

@[expose] public section

universe w' w v v' v'' u u' u''

open CategoryTheory Category Limits Pretriangulated ZeroObject

namespace CategoryTheory

variable {R : Type w} [CommRing R] (M : Submonoid R) (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear R C]

namespace Rationalization

/-- An object `X` is *`M`-torsion* if `m • 𝟙 X = 0` for some `m ∈ M`. -/
def torsion : ObjectProperty C :=
  fun X ↦ ∃ m ∈ M, m • 𝟙 X = 0

variable {M C}

lemma torsion_iff (X : C) : torsion M C X ↔ ∃ m ∈ M, m • 𝟙 X = 0 := Iff.rfl

/-- Multiplication by `m` on an object, conjugated by an isomorphism. -/
lemma smul_id_eq_conj {X Y : C} (e : X ≅ Y) (m : R) :
    m • 𝟙 Y = e.inv ≫ (m • 𝟙 X) ≫ e.hom := by
  simp

instance : (torsion M C).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨m, hm, h⟩
    exact ⟨m, hm, by rw [smul_id_eq_conj e, h, zero_comp, comp_zero]⟩

section Pretriangulated

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C]

instance : (torsion M C).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, 1, M.one_mem, (isZero_zero C).eq_of_src _ _⟩

instance : (torsion M C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ ⟨m, hm, h⟩ ↦ ⟨m, hm, by
    rw [← Functor.map_id, ← Functor.map_smul, h, Functor.map_zero]⟩⟩

omit [∀ n : ℤ, (shiftFunctor C n).Linear R] in
/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`, if `m₁` kills `X₁` and `m₃` kills
`X₃`, then `m₁ m₃` kills `X₂`. -/
lemma smul_id_obj₂_eq_zero {T : Triangle C} (hT : T ∈ distTriang C) {m₁ m₃ : R}
    (h₁ : m₁ • 𝟙 T.obj₁ = 0) (h₃ : m₃ • 𝟙 T.obj₃ = 0) : (m₁ * m₃) • 𝟙 T.obj₂ = 0 := by
  obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ T hT (m₃ • 𝟙 T.obj₂) (by
    simpa using congrArg (T.mor₂ ≫ ·) h₃)
  have h : m₁ • T.mor₁ = 0 := by simpa using congrArg (· ≫ T.mor₁) h₁
  rw [mul_smul, hb, ← Linear.comp_smul, h, comp_zero]

instance instIsTriangulatedTorsion : (torsion M C).IsTriangulated where
  toIsTriangulatedClosed₂ := .mk' fun _ hT ⟨m₁, hm₁, h₁⟩ ⟨m₃, hm₃, h₃⟩ ↦
    ⟨m₁ * m₃, M.mul_mem hm₁ hm₃, smul_id_obj₂_eq_zero hT h₁ h₃⟩

/-- The mapping cone of `m • 𝟙 X` is killed by `m²`. -/
lemma smul_id_cone_eq_zero {X Z : C} (m : R) (g : X ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (m • 𝟙 X) g h ∈ distTriang C) : (m * m) • 𝟙 Z = 0 := by
  obtain ⟨u, hu⟩ := Triangle.yoneda_exact₃ _ hT (X := Z) (m • 𝟙 Z) (by
    have := comp_distTriang_mor_zero₁₂ _ hT
    simp only [Triangle.mk_mor₁, Triangle.mk_mor₂, Linear.smul_comp] at this
    erw [id_comp] at this
    change g ≫ (m • 𝟙 Z) = 0
    simpa using this)
  have h₀ : m • h = 0 := by
    have := comp_distTriang_mor_zero₃₁ _ hT
    simp only [Triangle.mk_mor₃, Triangle.mk_mor₁, Functor.map_smul, Linear.comp_smul] at this
    erw [Functor.map_id, comp_id] at this
    exact this
  change m • 𝟙 Z = h ≫ u at hu
  rw [mul_smul, hu, ← Linear.smul_comp, h₀, zero_comp]

variable (M C)

/-- The morphisms whose mapping cone is `M`-torsion. These are the morphisms inverted in
the rationalization. -/
@[reducible]
def W : MorphismProperty C := (torsion M C).trW

variable {M C}

/-- For `m ∈ M`, multiplication by `m` has `M`-torsion mapping cone. -/
lemma W_smul_id {m : R} (hm : m ∈ M) (X : C) : W M C (m • 𝟙 X) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (m • 𝟙 X)
  exact ObjectProperty.trW.mk _ hT ⟨m * m, M.mul_mem hm hm, smul_id_cone_eq_zero m g h hT⟩

end Pretriangulated

end Rationalization

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C] [IsTriangulated C]

/-- The *rationalization* of an `R`-linear triangulated category `C` at a submonoid `M` of
`R`: the Verdier quotient of `C` by the triangulated subcategory of `M`-torsion objects,
i.e. the localization of `C` at the morphisms whose mapping cone is annihilated by some
element of `M`. -/
@[reducible]
def Rationalization : Type _ := (Rationalization.W M C).Localization

namespace Rationalization

/-- The localization functor from `C` to its rationalization. -/
@[reducible]
noncomputable def Q : C ⥤ Rationalization M C := (W M C).Q

instance : (Q M C).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor (Q M C) (W M C)

variable {M C}

/-- For `m ∈ M`, multiplication by `m` is an isomorphism of every object of the
rationalization. -/
lemma isIso_smul_id {m : R} (hm : m ∈ M) (Y : Rationalization M C) : IsIso (m • 𝟙 Y) := by
  have e := (Q M C).objObjPreimageIso Y
  have : IsIso (m • 𝟙 ((Q M C).obj ((Q M C).objPreimage Y))) := by
    rw [← (Q M C).map_id, ← Functor.map_smul]
    exact Localization.inverts (Q M C) (W M C) _ (W_smul_id hm _)
  rw [smul_id_eq_conj e]
  infer_instance

open scoped IsMulCommutative

/-- The image of `m ∈ M` in the center of the rationalization is a unit. -/
lemma isUnit_toCatCenter {m : R} (hm : m ∈ M) :
    IsUnit (Linear.toCatCenter R (Rationalization M C) m) := by
  rw [isUnit_iff_isIso]
  have (Y : Rationalization M C) : IsIso ((Linear.toCatCenter R _ m).app Y) :=
    isIso_smul_id hm Y
  exact NatIso.isIso_of_isIso_app _

variable (M C) (A : Type w') [CommRing A] [Algebra R A] [IsLocalization M A]

/-- The action of a localization `A` of `R` at `M` on the rationalization, as a ring
morphism to its center. -/
noncomputable def toCatCenter : A →+* CatCenter (Rationalization M C) :=
  IsLocalization.lift (M := M) (g := Linear.toCatCenter R (Rationalization M C))
    fun m ↦ isUnit_toCatCenter m.2

/-- The rationalization of `C` at `M` is linear over any localization `A` of `R` at `M`,
for instance over the fraction field of `R` when `M` is the set of nonzero divisors. -/
noncomputable instance linear : Linear A (Rationalization M C) :=
  Linear.ofRingMorphism (toCatCenter M C A)

variable {M C}

/-- The `A`-linear structure of the rationalization extends its `R`-linear structure. -/
lemma algebraMap_smul (r : R) {X Y : Rationalization M C} (f : X ⟶ Y) :
    algebraMap R A r • f = r • f := by
  change (toCatCenter M C A (algebraMap R A r)).app X ≫ f = r • f
  rw [toCatCenter, IsLocalization.lift_eq]
  change (r • 𝟙 X) ≫ f = r • f
  rw [Linear.smul_comp, id_comp]

end Rationalization

namespace Rationalization

/-! ### Functoriality

An `R`-linear triangulated functor `F : C ⥤ C'` sends `M`-torsion objects to `M`-torsion
objects and distinguished triangles to distinguished triangles, so it sends `W M C` into
`W M C'` and induces a functor `Rationalization.map M F` between the rationalizations. -/

variable {M C} {C' : Type u'} [Category.{v'} C'] [Preadditive C'] [Linear R C']

omit [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C n).Linear R] [Pretriangulated C] [IsTriangulated C] in
/-- An `R`-linear functor sends `M`-torsion objects to `M`-torsion objects. -/
lemma torsion_map (F : C ⥤ C') [F.Linear R] {X : C} (hX : torsion M C X) :
    torsion M C' (F.obj X) := by
  obtain ⟨m, hm, h⟩ := hX
  exact ⟨m, hm, by rw [← F.map_id, ← F.map_smul, h, ← zero_smul R (𝟙 X), F.map_smul, zero_smul]⟩

variable [HasZeroObject C'] [HasShift C' ℤ] [∀ n : ℤ, (shiftFunctor C' n).Additive]
  [∀ n : ℤ, (shiftFunctor C' n).Linear R] [Pretriangulated C'] [IsTriangulated C']
  {C'' : Type u''} [Category.{v''} C''] [Preadditive C''] [Linear R C'']
  [HasZeroObject C''] [HasShift C'' ℤ] [∀ n : ℤ, (shiftFunctor C'' n).Additive]
  [∀ n : ℤ, (shiftFunctor C'' n).Linear R] [Pretriangulated C''] [IsTriangulated C'']

omit [∀ n : ℤ, (shiftFunctor C n).Linear R] [IsTriangulated C]
  [∀ n : ℤ, (shiftFunctor C' n).Linear R] [IsTriangulated C'] in
/-- An `R`-linear triangulated functor sends morphisms with `M`-torsion mapping cone to
morphisms with `M`-torsion mapping cone: the mapping cone of `F f` is `F` of the mapping
cone of `f`. -/
lemma W_map (F : C ⥤ C') [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R] {X Y : C}
    {f : X ⟶ Y} (hf : W M C f) : W M C' (F.map f) := by
  obtain ⟨Z, g, h, hT, hZ⟩ := hf
  exact ObjectProperty.trW.mk _ (F.map_distinguished _ hT) (torsion_map F hZ)

variable (M)

/-- The functor `Rationalization M C ⥤ Rationalization M C'` induced by an `R`-linear
triangulated functor `F : C ⥤ C'`: the functor out of the localization induced by
`F ⋙ Q M C'`, which inverts `W M C` by `Rationalization.W_map`. -/
noncomputable def map (F : C ⥤ C') [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R] :
    Rationalization M C ⥤ Rationalization M C' :=
  Localization.lift (F ⋙ Q M C')
    (fun _ _ _ hf ↦ Localization.inverts (Q M C') (W M C') _ (W_map F hf)) (Q M C)

section

variable (F : C ⥤ C') [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]

noncomputable instance : Localization.Lifting (Q M C) (W M C) (F ⋙ Q M C') (map M F) :=
  inferInstanceAs (Localization.Lifting _ _ _ (Localization.lift _ _ _))

/-- The functor `Rationalization.map M F` is induced by `F`: `Q ⋙ map F ≅ F ⋙ Q`. -/
noncomputable def mapQIso : Q M C ⋙ map M F ≅ F ⋙ Q M C' :=
  Localization.Lifting.iso (Q M C) (W M C) (F ⋙ Q M C') (map M F)

instance [F.Additive] : (map M F).Additive := by
  rw [Localization.functor_additive_iff (Q M C) (W M C)]
  exact Functor.additive_of_iso (mapQIso M F).symm

noncomputable instance : (map M F).CommShift ℤ :=
  Functor.commShiftOfLocalization (Q M C) (W M C) ℤ (F ⋙ Q M C') (map M F)

instance : NatTrans.CommShift (mapQIso M F).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization (Q M C) (W M C) ℤ (F ⋙ Q M C') (map M F)

instance : (map M F).IsTriangulated := by
  have := Localization.essSurj_mapArrow (Q M C) (W M C)
  exact Functor.isTriangulated_of_precomp_iso (mapQIso M F)

instance linear_map_of_ring : (map M F).Linear R :=
  (Localization.functor_linear_iff (Q M C) (W M C) R (F ⋙ Q M C') (map M F)).1 inferInstance

variable (A : Type w') [CommRing A] [Algebra R A] [IsLocalization M A]

/-- `Rationalization.map M F` is linear over any localization `A` of `R` at `M`: an element
`r / m` of `A` acts through `r` and the inverse of the action of `m`, both of which `map M F`
preserves. -/
instance linear_map : (map M F).Linear A := by
  rw [Functor.linear_iff]
  intro X a
  obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective M a
  dsimp only
  have hsmul {Y : Rationalization M C} :
      (m : R) • (IsLocalization.mk' A r m • 𝟙 Y) = r • 𝟙 Y := by
    rw [← algebraMap_smul A, smul_smul, IsLocalization.mk'_spec', algebraMap_smul]
  have hsmul' {Y : Rationalization M C'} :
      (m : R) • (IsLocalization.mk' A r m • 𝟙 Y) = r • 𝟙 Y := by
    rw [← algebraMap_smul A, smul_smul, IsLocalization.mk'_spec', algebraMap_smul]
  have hinj {Y Z : Rationalization M C'} (f g : Y ⟶ Z) (h : (m : R) • f = (m : R) • g) :
      f = g := by
    have := isIso_smul_id m.2 Y
    rw [← cancel_epi ((m : R) • 𝟙 Y)]
    simpa using h
  apply hinj
  rw [← Functor.map_smul, hsmul, Functor.map_smul, Functor.map_id, hsmul']

end

/-- An isomorphism `F ≅ G` of functors induces an isomorphism `map M F ≅ map M G`. -/
noncomputable def mapIso {F G : C ⥤ C'} [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]
    [G.CommShift ℤ] [G.IsTriangulated] [G.Linear R] (e : F ≅ G) : map M F ≅ map M G :=
  Localization.liftNatIso (Q M C) (W M C) (F ⋙ Q M C') (G ⋙ Q M C') _ _
    (Functor.isoWhiskerRight e _)

/-- The functor induced by the identity is the identity. -/
noncomputable def mapId : map M (𝟭 C) ≅ 𝟭 _ :=
  Localization.liftNatIso (Q M C) (W M C) (𝟭 C ⋙ Q M C) (Q M C) _ _ (Functor.leftUnitor _)

/-- The functor induced by a composition is the composition of the induced functors. -/
noncomputable def mapComp (F : C ⥤ C') [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]
    (G : C' ⥤ C'') [G.CommShift ℤ] [G.IsTriangulated] [G.Linear R] :
    map M (F ⋙ G) ≅ map M F ⋙ map M G :=
  letI : Localization.Lifting (Q M C) (W M C) ((F ⋙ G) ⋙ Q M C'') (map M F ⋙ map M G) :=
    ⟨(Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (mapQIso M F) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F (mapQIso M G) ≪≫
      (Functor.associator _ _ _).symm⟩
  Localization.liftNatIso (Q M C) (W M C) ((F ⋙ G) ⋙ Q M C'') ((F ⋙ G) ⋙ Q M C'') _ _
    (Iso.refl _)

end Rationalization

end CategoryTheory
