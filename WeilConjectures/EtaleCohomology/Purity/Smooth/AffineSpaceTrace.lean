/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.SfAffineLineCanonicalDuality
public import WeilConjectures.CategoryTheory.Triangulated.BinaryBiproductCone
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomology
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomologyTriangle
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!
# The affine-space trace

For the projection `p : 𝔸^d_S ⟶ S` of relative affine space, the *affine-space trace*
`t_p : Rp_! Λ(d)[2d] ⟶ Λ_S` is an isomorphism (a step of the model purity for affine space): the
compactly supported cohomology of affine `d`-space is `Λ(-d)` in degree `2d` and vanishes
otherwise.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_twistShift`: `R_!` commutes with
  twist-and-shift, `Rf_!(M(m)[2m]) ≅ (Rf_! M)(m)[2m]`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_tateObject_affineLine`: the case
  of the affine line, `Rp_! Λ(1)[2] ≅ Λ_S`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace`:
  `Rp_! Λ(d)[2d] ≅ Λ_S`.

## Implementation details

As for the other model purity statements
(`WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace`), the trace map itself, the counit
of the affine-space adjunction, is not constructed; only the existence of the isomorphism is
recorded.

For the affine line `p = q ∘ j`, with `j : 𝔸¹_S ⟶ ℙ¹_S` the standard chart and `q : ℙ¹_S ⟶ S`,
`Rp_! Λ(1)[2] = Rq_* j_! j^* Λ(1)[2]` is the first vertex of `Rq_*` of the open–closed triangle
`j_! j^* N ⟶ N ⟶ Ri_* i^* N ⟶` of `N = Λ_{ℙ¹_S}(1)[2]`, `i` the section at infinity. The middle
vertex `Rq_* N` is `Λ_S(1)[2] ⊕ Λ_S` (the cohomology of the projective line), and on the first
summand the second map is the unit of `L(i ≫ q)^* ⊣ R(i ≫ q)_*`, an isomorphism as `i ≫ q` is
one; hence the first vertex is the second summand `Λ_S`. The general case follows by induction
on `d` through `𝔸^{d+1}_S ≅ 𝔸¹_{𝔸^d_S}`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section Twist

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ]

/-- `F(T(M)[a]) ≅ T'(F M)[a]` for `F` commuting with shifts and `F ⋙ T' ≅ T ⋙ F`. -/
private lemma nonempty_iso_obj_comp_shiftFunctor {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ] (TX TX' : C ⥤ C) (TY : D ⥤ D)
    (pf : F ⋙ TY ≅ TX' ⋙ F) (e : TX' ≅ TX) (a : ℤ) (M : C) :
    Nonempty (F.obj ((TX ⋙ shiftFunctor C a).obj M) ≅ (TY ⋙ shiftFunctor D a).obj (F.obj M)) :=
  ⟨(F.commShiftIso a).app _ ≪≫
    (shiftFunctor D a).mapIso (F.mapIso (e.symm.app M) ≪≫ (pf.app M).symm)⟩

/-- The projection formula for a Tate twist: `Rf_!(-) (m) ≅ Rf_!(- ⊗ᴸ Lf^* Λ_Y(m))`. -/
private lemma nonempty_iso_rightDerivedLowerShriek_comp_tateTwist [Finite Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (m : ℤ) :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ tateTwist Λ Y m ≅
      derivedTensorRight _ X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y m)) ⋙
        R(f)_![ModuleCat.{u + 1} Λ]) :=
  nonempty_iso_rightDerivedLowerShriek_comp_derivedTensorRight _ f
    (tateObject Λ Y m) (fun K ↦ hasProjectionFormula_of_finite Λ _ K _)

/-- Tensoring with `Lf^* Λ_Y(m)` is the Tate twist `(m)` on `X`. -/
private lemma nonempty_iso_derivedTensorRight_leftDerivedUpperStar_tateObject
    {X Y : Scheme.{u}} [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) (m : ℤ) :
    Nonempty (derivedTensorRight _ X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y m)) ≅
      tateTwist Λ X m) :=
  ⟨(derivedTensor _ X).flip.mapIso (leftDerivedUpperStarTateObjectIso f m)⟩

/-- `Rf_!(M(m)[2m]) ≅ (Rf_! M)(m)[2m]`, with the twist-and-shift written as a composite. -/
private lemma nonempty_iso_rightDerivedLowerShriek_tateTwist_comp_shiftFunctor [Finite Λ]
    {X Y : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]
    (f : X ⟶ Y) [HasCompactification f] (m : ℤ)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(f)_![ModuleCat.{u + 1} Λ]).obj
        ((tateTwist Λ X m ⋙ shiftFunctor _ (2 * m)).obj M) ≅
      (tateTwist Λ Y m ⋙ shiftFunctor _ (2 * m)).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj M)) := by
  obtain ⟨pf⟩ := nonempty_iso_rightDerivedLowerShriek_comp_tateTwist Λ f m
  obtain ⟨e⟩ := nonempty_iso_derivedTensorRight_leftDerivedUpperStar_tateObject Λ f m
  exact nonempty_iso_obj_comp_shiftFunctor (R(f)_![ModuleCat.{u + 1} Λ]) (tateTwist Λ X m) _
    (tateTwist Λ Y m) pf e (2 * m) M

/-- Compactly supported direct image commutes with twist-and-shift,
`Rf_!(M(m)[2m]) ≅ (Rf_! M)(m)[2m]`. -/
lemma nonempty_iso_rightDerivedLowerShriek_twistShift [Finite Λ] {X Y : Scheme.{u}}
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f]
    (m : ℤ)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(f)_![ModuleCat.{u + 1} Λ]).obj ((twistShift Λ X m).obj M) ≅
      (twistShift Λ Y m).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj M)) :=
  nonempty_iso_rightDerivedLowerShriek_tateTwist_comp_shiftFunctor Λ f m M

end Twist

section Composition

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Along a factorization `h = f ≫ g`, `Rh_! K ≅ Rg_! Rf_! K`. -/
lemma nonempty_iso_rightDerivedLowerShriek_obj_of_comp_eq [Finite Λ] {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (w : f ≫ g = h) [HasCompactification f]
    [HasCompactification g] [HasCompactification h]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(h)_![ModuleCat.{u + 1} Λ]).obj K ≅
      (R(g)_![ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)) := by
  subst w
  obtain ⟨α⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ f g
  exact ⟨α.app K⟩

/-- Along an isomorphism `φ : X ⟶ Y`, `Rφ_! Λ_X(m)[2m] ≅ Λ_Y(m)[2m]`. -/
lemma nonempty_iso_rightDerivedLowerShriek_twistShift_constantComplex_of_isIso
    [HasTateTwist Λ] {X Y : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]
    (φ : X ⟶ Y) [IsIso φ] (m : ℤ) :
    Nonempty ((R(φ)_![ModuleCat.{u + 1} Λ]).obj ((twistShift Λ X m).obj (constantComplex Λ X)) ≅
      (twistShift Λ Y m).obj (constantComplex Λ Y)) := by
  let A := ModuleCat.{u + 1} Λ
  have : (L((φ)^*[A])).IsEquivalence := inferInstance
  have := (derivedUpperStarLowerStarAdjunction A φ).unit_isIso_of_L_fully_faithful
  exact ⟨(rightDerivedLowerShriekIsoRightDerivedLowerStar A φ).app _ ≪≫
    (R((φ)_*[A])).mapIso ((twistShift Λ X m).mapIso
        (leftDerivedUpperStarConstantComplexIso Λ φ).symm ≪≫
      (leftDerivedUpperStarTwistShiftIso Λ φ m _).symm) ≪≫
    (asIso ((derivedUpperStarLowerStarAdjunction A φ).unit.app _)).symm⟩

end Composition

section AffineLine

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (S : Scheme.{u}) [HasInvertibleExponent Λ S]

/-- For the projective line `q : ℙ¹_S ⟶ S` with section at infinity `i`, the first summand
`Λ_S(1)[2] ⟶ Rq_*(Λ_{ℙ¹_S}(1)[2])` of the decomposition map followed by the restriction
`Rq_*(Λ_{ℙ¹_S}(1)[2]) ⟶ Rq_* Ri_* i^*(Λ_{ℙ¹_S}(1)[2])` to the section at infinity is an
isomorphism. -/
lemma isIso_inl_comp_projectiveLineDecompositionMapAux_comp_unit [HasKummerClass Λ] :
    IsIso (biprod.inl ≫ projectiveLineDecompositionMapAux Λ S ≫
      (R(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_*[ModuleCat.{u + 1} Λ])).map
        ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (ProjectiveSpace.lineInfinityι S)).unit.app
            ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧))) := by
  let A := ModuleCat.{u + 1} Λ
  let q := ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S
  let i := ProjectiveSpace.lineInfinityι S
  have : HasInvertibleExponent Λ ℙ(Option (ULift.{u} (Fin 1)); S) := .of_hom q
  have : (L((i ≫ q)^*[A])).IsEquivalence := inferInstance
  have := (derivedUpperStarLowerStarAdjunction A (i ≫ q)).unit_isIso_of_L_fully_faithful
  have hu := Adjunction.isIso_unit_app_comp_map_unit_app_of_iso
    (derivedUpperStarLowerStarAdjunction A q) (mapDerivedUpperStarLowerStarAdjunction A i)
    (derivedUpperStarLowerStarAdjunction A (i ≫ q))
    (leftDerivedUpperStarComp A i q ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory A i))
    ((tateObject Λ S 1)⟦(2 : ℤ)⟧)
  let κ := (leftDerivedUpperStarTateTwoIso Λ q).hom
  have hκ := (mapDerivedUpperStarLowerStarAdjunction A i).unit.naturality κ
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hκ
  have e : biprod.inl ≫ projectiveLineDecompositionMapAux Λ S ≫
      (R((q)_*[A])).map ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app
        ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧)) =
      ((derivedUpperStarLowerStarAdjunction A q).unit.app ((tateObject Λ S 1)⟦(2 : ℤ)⟧) ≫
        (R((q)_*[A])).map ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app
          ((L((q)^*[A])).obj ((tateObject Λ S 1)⟦(2 : ℤ)⟧)))) ≫
        (R((q)_*[A])).map ((R((i)_*[A])).map ((D((i)^*[A])).map κ)) := by
    rw [projectiveLineDecompositionMapAux, biprod.inl_desc_assoc, Category.assoc,
      Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ← hκ]
    rfl
  rw [e]
  infer_instance

variable [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]

/-- The affine-line trace is an isomorphism: for the projection `p : 𝔸¹_S ⟶ S` over a scheme `S`
on which the exponent of `Λ` is invertible, `Rp_! Λ(1)[2] ≅ Λ_S`. -/
theorem nonempty_iso_rightDerivedLowerShriek_tateObject_affineLine :
    Nonempty ((R(𝔸(ULift.{u} (Fin 1); S) ↘ S)_![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ 𝔸(ULift.{u} (Fin 1); S) 1)⟦(2 : ℤ)⟧) ≅ constantComplex Λ S) := by
  obtain ⟨K, hK, hN⟩ := HasTateTwist.IsNormalized.exists_hasKummerClass (Λ := Λ)
  subst hK
  let A := ModuleCat.{u + 1} Λ
  let q := ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S
  let i := ProjectiveSpace.lineInfinityι S
  let j := AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S
  have : HasInvertibleExponent Λ ℙ(Option (ULift.{u} (Fin 1)); S) := .of_hom q
  let N := (tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed A j i
    (ProjectiveSpace.range_lineInfinityι_eq_compl_range_toRelativeProjectiveSpace S) N
  have := isIso_projectiveLineDecompositionMapAux Λ S
  obtain ⟨e⟩ := nonempty_iso_obj₁_of_isIso_inl_comp ((R((q)_*[A])).map_distinguished _ hw)
    (projectiveLineDecompositionMapAux Λ S)
    (isIso_inl_comp_projectiveLineDecompositionMapAux_comp_unit Λ S)
  exact ⟨(rightDerivedLowerShriekIso Λ (sfAffineLineCompactification S)).symm.app _ ≪≫
    (Rf_!(sfAffineLineCompactification S)[A]).mapIso
      ((leftDerivedUpperStarTateTwoIso Λ j).symm ≪≫
        (leftDerivedUpperStarIsoMapDerivedCategory A j).app N) ≪≫ e.symm⟩

end AffineLine

section AffineSpace

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]

/-- The affine-space trace is an isomorphism, in the coordinates `Fin d`: for the projection
`p : 𝔸^d_S ⟶ S`, `Rp_! Λ(d)[2d] ≅ Λ_S`. -/
theorem nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace_fin (d : ℕ)
    (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    Nonempty ((R(𝔸(ULift.{u} (Fin d); S) ↘ S)_![ModuleCat.{u + 1} Λ]).obj
        ((twistShift Λ 𝔸(ULift.{u} (Fin d); S) d).obj
          (constantComplex Λ 𝔸(ULift.{u} (Fin d); S))) ≅ constantComplex Λ S) := by
  induction d with
  | zero =>
    have : IsIso (𝔸(ULift.{u} (Fin 0); S) ↘ S) := inferInstance
    obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_constantComplex_of_isIso Λ
      (𝔸(ULift.{u} (Fin 0); S) ↘ S) ((0 : ℕ) : ℤ)
    exact ⟨e ≪≫ twistShiftZeroIso Λ S (by simp) _⟩
  | succ d ih =>
    obtain ⟨ih⟩ := ih
    let B := 𝔸(ULift.{u} (Fin d); S)
    let φ := (affineSpaceSuccIso d S).hom
    let q := 𝔸(ULift.{u} (Fin 1); B) ↘ B
    let p := B ↘ S
    have : HasCompactification (φ ≫ q) := HasCompactification.comp_of_isOpenImmersion q φ
    have : HasInvertibleExponent Λ B := .of_hom p
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); B) := .of_hom q
    have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin (d + 1)); S) := .of_hom (_ ↘ S)
    obtain ⟨c₁⟩ := nonempty_iso_rightDerivedLowerShriek_obj_of_comp_eq Λ (f := φ ≫ q) (g := p)
      (h := 𝔸(ULift.{u} (Fin (d + 1)); S) ↘ S)
      (by rw [Category.assoc]; exact affineSpaceSuccIso_hom_over_over d S)
      ((twistShift Λ 𝔸(ULift.{u} (Fin (d + 1)); S) ((d + 1 : ℕ) : ℤ)).obj
        (constantComplex Λ 𝔸(ULift.{u} (Fin (d + 1)); S)))
    obtain ⟨c₂⟩ := nonempty_iso_rightDerivedLowerShriek_obj_of_comp_eq Λ (f := φ) (g := q) rfl
      ((twistShift Λ 𝔸(ULift.{u} (Fin (d + 1)); S) ((d + 1 : ℕ) : ℤ)).obj
        (constantComplex Λ 𝔸(ULift.{u} (Fin (d + 1)); S)))
    obtain ⟨c₃⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_constantComplex_of_isIso Λ φ
      ((d + 1 : ℕ) : ℤ)
    obtain ⟨t⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift Λ q d
      ((twistShift Λ 𝔸(ULift.{u} (Fin 1); B) 1).obj (constantComplex Λ 𝔸(ULift.{u} (Fin 1); B)))
    obtain ⟨l⟩ := nonempty_iso_rightDerivedLowerShriek_tateObject_affineLine Λ B
    let a : (twistShift Λ 𝔸(ULift.{u} (Fin 1); B) ((d + 1 : ℕ) : ℤ)).obj
          (constantComplex Λ 𝔸(ULift.{u} (Fin 1); B)) ≅
        (twistShift Λ 𝔸(ULift.{u} (Fin 1); B) d).obj
          ((twistShift Λ 𝔸(ULift.{u} (Fin 1); B) 1).obj
            (constantComplex Λ 𝔸(ULift.{u} (Fin 1); B))) :=
      eqToIso (by rw [Nat.cast_succ, add_comm]) ≪≫
        (twistShiftTwistShiftIso Λ _ 1 d _).symm
    let b : (twistShift Λ 𝔸(ULift.{u} (Fin 1); B) 1).obj
          (constantComplex Λ 𝔸(ULift.{u} (Fin 1); B)) ≅
        (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)⟦(2 : ℤ)⟧ :=
      twistShiftConstantComplexIso Λ _ 1 ≪≫ eqToIso (by rw [mul_one])
    exact ⟨c₁ ≪≫ (R(p)_![ModuleCat.{u + 1} Λ]).mapIso (c₂ ≪≫
      (R(q)_![ModuleCat.{u + 1} Λ]).mapIso (c₃ ≪≫ a) ≪≫ t ≪≫
        (twistShift Λ B d).mapIso ((R(q)_![ModuleCat.{u + 1} Λ]).mapIso b ≪≫ l)) ≪≫ ih⟩

/-- The affine-space trace is an isomorphism: for the projection `p : 𝔸(n; S) ⟶ S` of relative
affine space of dimension `d = #n`, over a scheme `S` on which the exponent of `Λ` is invertible,
`Rp_! Λ(d)[2d] ≅ Λ_S`. -/
theorem nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace
    (n : Type u) [Fintype n] (S : Scheme.{u})
    [HasInvertibleExponent Λ S] [HasCompactification (𝔸(n; S) ↘ S)] :
    Nonempty ((R(𝔸(n; S) ↘ S)_![ModuleCat.{u + 1} Λ]).obj
        ((twistShift Λ 𝔸(n; S) (Fintype.card n)).obj (constantComplex Λ 𝔸(n; S))) ≅
      constantComplex Λ S) := by
  let φ := (AffineSpace.reindexIso S (Equiv.ulift.trans (Fintype.equivFin n).symm)).hom
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin (Fintype.card n)); S) := .of_hom (_ ↘ S)
  obtain ⟨c⟩ := nonempty_iso_rightDerivedLowerShriek_obj_of_comp_eq Λ (f := φ)
    (g := 𝔸(ULift.{u} (Fin (Fintype.card n)); S) ↘ S) (h := 𝔸(n; S) ↘ S)
    (by simp [φ]) ((twistShift Λ 𝔸(n; S) (Fintype.card n)).obj (constantComplex Λ 𝔸(n; S)))
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_constantComplex_of_isIso Λ φ
    (Fintype.card n)
  obtain ⟨t⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace_fin Λ
    (Fintype.card n) S
  exact ⟨c ≪≫ (R(𝔸(ULift.{u} (Fin (Fintype.card n)); S) ↘ S)_![ModuleCat.{u + 1} Λ]).mapIso e ≪≫
    t⟩

end AffineSpace

end AlgebraicGeometry.Etale
