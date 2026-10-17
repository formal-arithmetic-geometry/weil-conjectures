/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineCompactification
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!
# The affine-space trace

For the projection `p : 𝔸^d_S ⟶ S` of relative affine space, the *affine-space trace*
`t_p : Rp_! Λ(d)[2d] ⟶ Λ_S` is an isomorphism (blueprint `lem-amb-affine-space-top-trace`, a
step of the model purity `sk-prop-an`): the compactly supported cohomology of affine `d`-space
is `Λ(-d)` in degree `2d` and vanishes otherwise.

The proof follows the blueprint. For `d = 1`, compactify `p` by the projective line
`q : ℙ¹_S ⟶ S`, with the open chart `j : 𝔸¹_S ⟶ ℙ¹_S` and the section at infinity
`∞ : S ⟶ ℙ¹_S`. Applying `Rq_*` to the open–closed triangle `j_! j^* Λ ⟶ Λ ⟶ ∞_* ∞^* Λ` gives a
distinguished triangle

`Rp_! Λ ⟶ Rq_* Λ ⟶ Λ_S ⟶ [1]`

whose second map, precomposed with the unit `Λ_S ⟶ Rq_* Λ`, is an isomorphism (`q ∘ ∞ = 𝟙`).
By the cohomology of the projective line (`thm-amb-p1-decomposition`), the unit and the first
Chern class of `𝒪(1)` decompose `Rq_* Λ ≅ Λ_S ⊕ Λ_S(-1)[-2]`, so `Rp_! Λ ≅ Λ_S(-1)[-2]`
(`AlgebraicGeometry.Etale.nonempty_iso_of_distTriang_of_isIso_biprod_desc`). The general case
follows by induction along `𝔸^{d+1}_S ≅ 𝔸¹_{𝔸^d_S}`, using the composition of compactly
supported direct images and the projection formula.

## Main statements

- `AlgebraicGeometry.Etale.exists_isIso_biprod_desc_projectiveLine`: the cohomology of the
  projective line (`thm-amb-p1-decomposition`, a node of `sk-lem-geo-p1-cohomology`, recorded
  without proof).
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_affineLine`:
  `Rp_! Λ ≅ Λ_S(-1)[-2]` for the affine line.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace`:
  `Rp_! Λ(d)[2d] ≅ Λ_S`.

## Implementation notes

The trace map itself, the counit of the affine-space adjunction, is not constructed: only the
existence of the isomorphism is recorded.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section Triangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasBinaryBiproducts C]

/-- In a distinguished triangle `X ⟶ Y ⟶[g] Z ⟶ X[1]`, if `Y ≅ Z' ⊕ N` through `s : Z' ⟶ Y`
and `h : N ⟶ Y`, with `s ≫ g` an isomorphism, then `X ≅ N`, whatever the composite `h ≫ g`. -/
theorem nonempty_iso_of_distTriang_of_isIso_biprod_desc {X Y Z Z' N : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (w : Z ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g w ∈ distTriang C) (s : Z' ⟶ Y)
    (h : N ⟶ Y) [IsIso (biprod.desc s h)] [IsIso (s ≫ g)] : Nonempty (X ≅ N) := by
  set a := inv (s ≫ g)
  have ha : a ≫ s ≫ g = 𝟙 _ := by simp [a]
  set c : N ⟶ Z' := h ≫ g ≫ a
  -- the change of basis `N ⊕ Z' ≅ Z' ⊕ N` killing the component `h ≫ g`
  let M : N ⊞ Z' ⟶ Z' ⊞ N := biprod.lift (biprod.snd - biprod.fst ≫ c) biprod.fst
  let M' : Z' ⊞ N ⟶ N ⊞ Z' := biprod.lift biprod.snd (biprod.fst + biprod.snd ≫ c)
  have hM : IsIso M := ⟨M', by ext <;> simp [M, M'], by ext <;> simp [M, M']⟩
  let E : N ⊞ Z' ⟶ Y := M ≫ biprod.desc s h
  have hE : E = biprod.desc (h - c ≫ s) s := by
    ext <;> simp [E, M, sub_eq_add_neg, Preadditive.add_comp]
  have hEg : E ≫ g ≫ a = biprod.snd := by
    rw [hE]
    ext
    · simp only [biprod.inl_desc_assoc, Preadditive.sub_comp, Category.assoc, ha,
        Category.comp_id, biprod.inl_snd, c]
      simp
    · simp [ha]
  have hT₂ := rot_of_distTriang _ (binaryBiproductTriangle_distinguished N Z')
  have e := isoTriangleOfIso₁₂ _ _ (rot_of_distTriang _ hT) hT₂ (asIso E).symm (asIso a) (by
    dsimp
    rw [← hEg, asIso_inv, IsIso.inv_hom_id_assoc])
  exact ⟨(shiftFunctor C (1 : ℤ)).preimageIso (Triangle.π₃.mapIso e)⟩

end Triangulated

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

section ProjectiveLine

/-- The unit `Λ_Y ⟶ Rf_* Λ_X` of the derived adjunction `Lf^* ⊣ Rf_*` at the constant
complex. -/
noncomputable def constantComplexUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constantComplex Λ Y ⟶ (R((f)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app _ ≫
    (R((f)_*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ f).hom

instance (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    HasInvertibleExponent Λ (ProjectiveLine S) :=
  .of_hom (ProjectiveLine S ↘ S)

/-- Blueprint `thm-amb-p1-decomposition`: The projective-line calculation before purity

Let `q : ℙ¹_S ⟶ S` be the projective line over a scheme on which the exponent of `Λ` is
invertible, and `h` the Kummer first Chern class of `𝒪(1)`, read as a morphism
`Λ_S(-1)[-2] ⟶ Rq_* Λ_{ℙ¹_S}`. Then `(1, h) : Λ_S ⊕ Λ_S(-1)[-2] ⟶ Rq_* Λ_{ℙ¹_S}`, the first
component being the unit of `Lq^* ⊣ Rq_*`, is an isomorphism.

This is a node of the blueprint subsection `sk-lem-geo-p1-cohomology` (where `S` is noetherian),
recorded here without proof. The first Chern class is not constructed in the library, so the
statement records the existence of a second component `h`, the content being that the
complement of the unit summand is `Λ_S(-1)[-2]`. -/
theorem exists_isIso_biprod_desc_projectiveLine [HasTateTwist.IsNormalized Λ]
    (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    ∃ h : (tateObject Λ S (-1))⟦(-2 : ℤ)⟧ ⟶
        (R((ProjectiveLine S ↘ S)_*[ModuleCat.{u + 1} Λ])).obj
          (constantComplex Λ (ProjectiveLine S)),
      IsIso (biprod.desc (constantComplexUnit Λ (ProjectiveLine S ↘ S)) h) :=
  sorry

/-- The derived pullback along the identity is the identity. -/
lemma nonempty_leftDerivedUpperStar_id_iso (S : Scheme.{u}) (h : S ⟶ S) (hh : h = 𝟙 S) :
    Nonempty (L((h)^*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _) := by
  subst hh
  exact ⟨Functor.leftDerivedFunctorNatIso _ (Etale.upperStarId _ _) ≪≫
    (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _⟩

/-- For a section `i : S ⟶ X` of `q : X ⟶ S` which is a closed immersion, the unit
`Λ_S ⟶ Rq_* Λ_X` followed by `Rq_*` of the unit `Λ_X ⟶ Ri_* i^* Λ_X` is an isomorphism: it is
the unit of the composite adjunction `Lq^* ⋙ i^* ⊣ Ri_* ⋙ Rq_*`, whose left adjoint is
`L(i ≫ q)^* = L(𝟙)^* ≅ 𝟭`. -/
theorem isIso_constantComplexUnit_comp_map_unit {X S : Scheme.{u}} (q : X ⟶ S) (i : S ⟶ X)
    (hi : i ≫ q = 𝟙 S) :
    IsIso (constantComplexUnit Λ q ≫ (R((q)_*[ModuleCat.{u + 1} Λ])).map
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app
        (constantComplex Λ X))) := by
  set A := ModuleCat.{u + 1} Λ
  let adj := (derivedUpperStarLowerStarAdjunction A q).comp
    (mapDerivedUpperStarLowerStarAdjunction A i)
  obtain ⟨eid⟩ := nonempty_leftDerivedUpperStar_id_iso Λ S (i ≫ q) hi
  let e : L((q)^*[A]) ⋙ D((i)^*[A]) ≅ 𝟭 _ :=
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory A i).symm ≪≫
      (leftDerivedUpperStarComp A i q).symm ≪≫ eid
  have : (L((q)^*[A]) ⋙ D((i)^*[A])).Full := Functor.Full.of_iso e.symm
  have : (L((q)^*[A]) ⋙ D((i)^*[A])).Faithful := Functor.Faithful.of_iso e.symm
  have hu : IsIso (adj.unit.app (constantComplex Λ S)) := inferInstance
  have key : constantComplexUnit Λ q ≫ (R((q)_*[A])).map
      ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app (constantComplex Λ X)) =
      adj.unit.app (constantComplex Λ S) ≫ (R((q)_*[A])).map ((R((i)_*[A])).map
        ((D((i)^*[A])).map (leftDerivedUpperStarConstantComplexIso Λ q).hom)) := by
    simp only [constantComplexUnit, adj, Adjunction.comp_unit_app, Category.assoc,
      ← Functor.map_comp]
    congr 2
    exact ((mapDerivedUpperStarLowerStarAdjunction A i).unit.naturality _)
  rw [key]
  infer_instance

end ProjectiveLine

section AffineLine

variable [HasTateTwist.IsNormalized Λ]

/-- Compactly supported cohomology of the affine line: for the projection `p : 𝔸¹_S ⟶ S` over a
scheme on which the exponent of `Λ` is invertible, `Rp_! Λ ≅ Λ_S(-1)[-2]`. -/
theorem nonempty_iso_rightDerivedLowerShriek_affineLine (S : Scheme.{u})
    [HasInvertibleExponent Λ S] :
    Nonempty ((R(𝔸(ULift.{u} (Fin 1); S) ↘ S)_![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ 𝔸(ULift.{u} (Fin 1); S)) ≅ (tateObject Λ S (-1))⟦(-2 : ℤ)⟧) := by
  set A := ModuleCat.{u + 1} Λ
  let c := ProjectiveLine.affineLineCompactification' S
  let j := c.i
  let q := ProjectiveLine S ↘ S
  let i := ProjectiveLine.infinity S
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    have h₁ := ProjectiveLine.range_infinity S
    have h₂ : Set.range j.base = Set.range (ProjectiveLine.affineChart S).base := by
      simp only [j, c, ProjectiveLine.affineLineCompactification'_i, Scheme.Hom.comp_base,
        TopCat.hom_comp, ContinuousMap.coe_comp]
      exact Set.range_comp_of_surjective _ _
        (ConcreteCategory.bijective_of_isIso (ProjectiveLine.affineLineIso S).hom.base).2
    rw [h₂]
    exact h₁
  obtain ⟨w, hT⟩ := exists_distTriang_openClosed A j i hij (constantComplex Λ (ProjectiveLine S))
  have : (R((q)_*[A])).IsTriangulated :=
    (mapDerivedUpperStarLowerStarAdjunction A q).isTriangulated_rightAdjoint
  have hT' := (R((q)_*[A])).map_distinguished _ hT
  obtain ⟨h, hh⟩ := exists_isIso_biprod_desc_projectiveLine Λ S
  have hs := isIso_constantComplexUnit_comp_map_unit Λ q i (ProjectiveLine.infinity_over S)
  obtain ⟨e⟩ := nonempty_iso_of_distTriang_of_isIso_biprod_desc _ _ _ hT'
    (constantComplexUnit Λ q) h
  -- `Rp_! Λ = Rq_* j_! Λ = Rq_* j_! j^* Λ`
  exact ⟨((rightDerivedLowerShriekIso Λ c).app _).symm ≪≫
    (R((q)_*[A])).mapIso ((D((j)_!open[A])).mapIso
      ((leftDerivedUpperStarConstantComplexIso Λ j).symm ≪≫
        (leftDerivedUpperStarIsoMapDerivedCategory A j).app _)) ≪≫ e⟩

/-- `Rf_!(M(m)[2m]) ≅ (Rf_! M)(m)[2m]`, by the projection formula. -/
theorem nonempty_iso_rightDerivedLowerShriek_obj_twistShift {X Y : Scheme.{u}}
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f]
    (m : ℤ) (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(f)_![ModuleCat.{u + 1} Λ]).obj ((twistShift Λ X m).obj M) ≅
      (twistShift Λ Y m).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj M)) := by
  obtain ⟨pf⟩ := nonempty_iso_rightDerivedLowerShriek_comp_derivedTensorRight
    (ModuleCat.{u + 1} Λ) f (tateObject Λ Y m) (fun K ↦ hasProjectionFormula_of_finite Λ _ K _)
  exact ⟨((R(f)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * m)).app _ ≪≫
    (shiftFunctor _ (2 * m)).mapIso ((R(f)_![ModuleCat.{u + 1} Λ]).mapIso
      (((derivedTensor _ X).flip.mapIso (leftDerivedUpperStarTateObjectIso f m)).symm.app M) ≪≫
        (pf.app M).symm)⟩

/-- The affine-line case of the affine-space trace: `Rp_! Λ(1)[2] ≅ Λ_S`. -/
theorem nonempty_iso_rightDerivedLowerShriek_twistShift_affineLine (S : Scheme.{u})
    [HasInvertibleExponent Λ S] :
    Nonempty ((R(𝔸(ULift.{u} (Fin 1); S) ↘ S)_![ModuleCat.{u + 1} Λ]).obj
        ((twistShift Λ 𝔸(ULift.{u} (Fin 1); S) 1).obj
          (constantComplex Λ 𝔸(ULift.{u} (Fin 1); S))) ≅ constantComplex Λ S) := by
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedLowerShriek_obj_twistShift Λ
    (𝔸(ULift.{u} (Fin 1); S) ↘ S) 1 (constantComplex Λ 𝔸(ULift.{u} (Fin 1); S))
  obtain ⟨e₂⟩ := nonempty_iso_rightDerivedLowerShriek_affineLine Λ S
  exact ⟨e₁ ≪≫ (twistShift Λ S 1).mapIso (e₂ ≪≫ (twistShiftConstantComplexIso Λ S (-1)).symm) ≪≫
    twistShiftTwistShiftIso Λ S (-1) 1 _ ≪≫ twistShiftZeroIso Λ S (by norm_num) _⟩

end AffineLine

section AffineSpace

omit [Finite Λ] [HasTateTwist Λ] in
/-- Compactly supported direct images along equal morphisms agree. -/
lemma nonempty_iso_rightDerivedLowerShriek_of_eq {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [HasCompactification f] [HasCompactification f'] (h : f = f') :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ≅ R(f')_![ModuleCat.{u + 1} Λ]) := by
  subst h
  exact ⟨Iso.refl _⟩

variable [HasTateTwist.IsNormalized Λ]

/-- For an isomorphism of schemes `e : X ≅ Y`, `Re_! Λ_X ≅ Λ_Y`, compatibly with twists. -/
theorem nonempty_iso_rightDerivedLowerShriek_twistShift_of_iso {X Y : Scheme.{u}}
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] (e : X ≅ Y)
    [HasCompactification e.hom] (m : ℤ) :
    Nonempty ((R(e.hom)_![ModuleCat.{u + 1} Λ]).obj ((twistShift Λ X m).obj
        (constantComplex Λ X)) ≅ (twistShift Λ Y m).obj (constantComplex Λ Y)) := by
  obtain ⟨t⟩ := nonempty_iso_rightDerivedLowerShriek_obj_twistShift Λ e.hom m
    (constantComplex Λ X)
  exact ⟨t ≪≫ (twistShift Λ Y m).mapIso
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) e.hom ≪≫
      rightDerivedLowerStarIsoLeftDerivedUpperStarInv (ModuleCat.{u + 1} Λ) e).app _ ≪≫
        leftDerivedUpperStarConstantComplexIso Λ e.inv)⟩

/-- The affine-space trace for the standard affine spaces `𝔸(ULift (Fin d); S)`, by induction
on `d` along `𝔸^{d+1}_S ≅ 𝔸¹_{𝔸^d_S}`. -/
theorem nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace_fin (d : ℕ) :
    ∀ (S : Scheme.{u}) [HasInvertibleExponent Λ S],
      Nonempty ((R(𝔸(ULift.{u} (Fin d); S) ↘ S)_![ModuleCat.{u + 1} Λ]).obj
        ((twistShift Λ 𝔸(ULift.{u} (Fin d); S) d).obj
          (constantComplex Λ 𝔸(ULift.{u} (Fin d); S))) ≅ constantComplex Λ S) := by
  induction d with
  | zero =>
    intro S _
    let e := asIso (𝔸(ULift.{u} (Fin 0); S) ↘ S)
    have : HasCompactification e.hom := inferInstanceAs
      (HasCompactification (𝔸(ULift.{u} (Fin 0); S) ↘ S))
    obtain ⟨t⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_of_iso Λ e ((0 : ℕ) : ℤ)
    exact ⟨t ≪≫ twistShiftZeroIso Λ S (by simp) _⟩
  | succ d ih =>
    intro S _
    set A := ModuleCat.{u + 1} Λ
    set φ := affineSpaceSuccIso d S
    set q := 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S)) ↘ 𝔸(ULift.{u} (Fin d); S)
    set p := 𝔸(ULift.{u} (Fin d); S) ↘ S
    have : HasCompactification φ.hom :=
      (Compactification.ofIsOpenImmersion φ.hom).hasCompactification
    have h : 𝔸(ULift.{u} (Fin (d + 1)); S) ↘ S = φ.hom ≫ q ≫ p :=
      (affineSpaceSuccIso_hom_over_over d S).symm
    have h' : φ.inv ≫ 𝔸(ULift.{u} (Fin (d + 1)); S) ↘ S = q ≫ p := by
      rw [h, Iso.inv_hom_id_assoc]
    have : HasCompactification (q ≫ p) := by
      have := HasCompactification.comp_of_isOpenImmersion
        (𝔸(ULift.{u} (Fin (d + 1)); S) ↘ S) φ.inv
      exact .of_eq h'
    have : HasCompactification (φ.hom ≫ q ≫ p) := .of_eq h
    obtain ⟨heq⟩ := nonempty_iso_rightDerivedLowerShriek_of_eq Λ h
    obtain ⟨c₁⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ φ.hom (q ≫ p)
    obtain ⟨c₂⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ q p
    obtain ⟨t₀⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_of_iso Λ φ
      ((d + 1 : ℕ) : ℤ)
    obtain ⟨t₁⟩ := nonempty_iso_rightDerivedLowerShriek_obj_twistShift Λ q d
      ((twistShift Λ _ 1).obj (constantComplex Λ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); S))))
    obtain ⟨t₂⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_affineLine Λ
      𝔸(ULift.{u} (Fin d); S)
    obtain ⟨t₃⟩ := ih S
    exact ⟨heq.app _ ≪≫ c₁.app _ ≪≫ (R(q ≫ p)_![A]).mapIso t₀ ≪≫ c₂.app _ ≪≫
      (R(p)_![A]).mapIso ((R(q)_![A]).mapIso
        ((twistShift Λ _ _).mapIso (eqToIso (by push_cast; rfl)) ≪≫
          (twistShiftTwistShiftIso Λ _ 1 d _).symm) ≪≫ t₁ ≪≫ (twistShift Λ _ d).mapIso t₂) ≪≫ t₃⟩

end AffineSpace

variable [HasTateTwist.IsNormalized Λ]

/-- Blueprint `lem-amb-affine-space-top-trace`: the affine-space trace is an isomorphism.

For the projection `p : 𝔸(n; S) ⟶ S` of relative affine space of dimension `d = #n`, over a
scheme `S` on which the exponent of `Λ` is invertible, the compactly supported direct image of
the twisted constant complex is the constant complex: `Rp_! Λ(d)[2d] ≅ Λ_S`. Equivalently
`Rp_! Λ ≅ Λ_S(-d)[-2d]`: compactly supported cohomology of affine `d`-space is `Λ(-d)`,
concentrated in degree `2d`. -/
theorem nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace
    (n : Type u) [Fintype n] (S : Scheme.{u})
    [HasInvertibleExponent Λ S] [HasCompactification (𝔸(n; S) ↘ S)] :
    Nonempty ((R(𝔸(n; S) ↘ S)_![ModuleCat.{u + 1} Λ]).obj
        ((twistShift Λ 𝔸(n; S) (Fintype.card n)).obj (constantComplex Λ 𝔸(n; S))) ≅
      constantComplex Λ S) := by
  set A := ModuleCat.{u + 1} Λ
  set d := Fintype.card n
  let σ : ULift.{u} (Fin d) ≃ n := Equiv.ulift.trans (Fintype.equivFin n).symm
  let e := AffineSpace.reindexIso S σ
  have : HasCompactification e.hom :=
    (Compactification.ofIsOpenImmersion e.hom).hasCompactification
  have h : 𝔸(n; S) ↘ S = e.hom ≫ 𝔸(ULift.{u} (Fin d); S) ↘ S := by
    simp [e, AffineSpace.reindex_over]
  have : HasCompactification (e.hom ≫ 𝔸(ULift.{u} (Fin d); S) ↘ S) := .of_eq h
  obtain ⟨heq⟩ := nonempty_iso_rightDerivedLowerShriek_of_eq Λ h
  obtain ⟨c⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ e.hom (𝔸(ULift.{u} (Fin d); S) ↘ S)
  obtain ⟨t₀⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_of_iso Λ e d
  obtain ⟨t₁⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace_fin Λ d S
  exact ⟨heq.app _ ≪≫ c.app _ ≪≫ (R(𝔸(ULift.{u} (Fin d); S) ↘ S)_![A]).mapIso t₀ ≪≫ t₁⟩

end AlgebraicGeometry.Etale
