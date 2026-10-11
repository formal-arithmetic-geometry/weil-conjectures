/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Trace

/-!
# Normalization of the smooth trace on the affine line

The fundamental class of the affine line `p : 𝔸¹_k ⟶ Spec k` is the image of the orientation
`pur_s : Λ_{V(t)} ⟶ Rs^! Λ(1)[2]` of its zero section
(`AlgebraicGeometry.Etale.affineLineOrientation`)
under `Rp_!` and the counit of `Rs_! ⊣ Rs^!`:

`cl : Λ ≅ R(s ≫ p)_! Λ ≅ Rp_! Rs_! Λ ⟶ Rp_! Rs_! Rs^! Λ(1)[2] ⟶ Rp_! Λ(1)[2]`.

The normalization of the smooth trace (blueprint `thm-pur-trace-normalization-transitivity`,
Step 2) is that `Tr^sm_p(cl) = 1`.

## Main definitions

- `AlgebraicGeometry.Etale.affineLineFundamentalClass`: the fundamental class `cl`.

## Main statements

- `AlgebraicGeometry.Etale.exists_affineLineFundamentalClass_comp_smoothPurityTrace`: the trace of
  the fundamental class is `1`.

## Implementation notes

The composition isomorphism `α : R(s ≫ p)_! ≅ Rs_! ⋙ Rp_!` and the identification
`ψ : Λ_k ≅ R(s ≫ p)_! Λ_{V(t)}` (the morphism `s ≫ p` is an isomorphism) are only known to
exist, so they are arguments; the purity map of `p` is only known to exist as well, so the
normalization asserts that some purity map is normalized, which is the form in which it
determines the canonical one.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ] (Y : Scheme.{u})
  [HasCompactification (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
    {AffineSpace.coord Y (ULift.up 0)} ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))]

/-- The derived pullback along an isomorphism of schemes is an equivalence, with inverse the
derived pullback along the inverse isomorphism. -/
noncomputable def leftDerivedUpperStarEquivalenceOfIso {X' Y' : Scheme.{u}} (e : X' ≅ Y') :
    CategoryTheory.Equivalence
      (_root_.DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (_root_.DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  let idIso (T : Scheme.{u}) : L((𝟙 T)^*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _ :=
    Functor.leftDerivedFunctorNatIso _ (Etale.upperStarId _ T) ≪≫
      (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _
  CategoryTheory.Equivalence.mk L((e.hom)^*[ModuleCat.{u + 1} Λ]) L((e.inv)^*[ModuleCat.{u + 1} Λ])
    ((idIso Y').symm ≪≫ leftDerivedUpperStarComp _ e.inv e.hom (𝟙 Y') e.inv_hom_id.symm)
    ((leftDerivedUpperStarComp _ e.hom e.inv (𝟙 X') e.hom_inv_id.symm).symm ≪≫ idIso X')

/-- For an isomorphism of schemes `e`, the counit of `Re_! ⊣ Re^!` is an isomorphism: `Re^!` is
the derived pullback `Le^*` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekIsoOfIso`), an
equivalence. -/
instance isIso_rightDerivedUpperShriekAdjunction_counit_of_iso {X' Y' : Scheme.{u}}
    (e : X' ≅ Y') [HasCompactification e.hom] :
    IsIso (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) e.hom).counit := by
  have : L((e.hom)^*[ModuleCat.{u + 1} Λ]).IsEquivalence :=
    (leftDerivedUpperStarEquivalenceOfIso Λ e).isEquivalence_functor
  have : (R(e.hom)^![ModuleCat.{u + 1} Λ]).IsEquivalence :=
    Functor.isEquivalence_of_iso (rightDerivedUpperShriekIsoOfIso _ e).symm
  infer_instance

omit [HasKummerClass Λ] in
/-- A composite `L ⟶ R(s ≫ p)_! L₀ ≅ Rp_! Rs_! L₀ ⟶ Rp_! Rs_! Rs^! M ⟶ Rp_! M ⟶ Rp_! Rp^! K ⟶ K`
built from an isomorphism `pur : L₀ ≅ Rs^! M`, the counit of `Rs_! ⊣ Rs^!`, an isomorphism
`δ : M ≅ Rp^! K` and the counit of `Rp_! ⊣ Rp^!` is an isomorphism as soon as the counit of
`R(s ≫ p)_! ⊣ R(s ≫ p)^!` at `K` is: through the composition isomorphism conjugate to `α`, it is
`R(s ≫ p)_!` of an isomorphism followed by that counit. -/
lemma isIso_comp_counit_comp_counit {Z P B : Scheme.{u}} (s : Z ⟶ P) (p : P ⟶ B)
    [HasCompactification s] [HasCompactification p] [HasCompactification (s ≫ p)]
    (α : R(s ≫ p)_![ModuleCat.{u + 1} Λ] ≅
      R(s)_![ModuleCat.{u + 1} Λ] ⋙ R(p)_![ModuleCat.{u + 1} Λ])
    {L₀ : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {M : _root_.DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K L : _root_.DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (ψ : L ⟶ (R(s ≫ p)_![ModuleCat.{u + 1} Λ]).obj L₀) [IsIso ψ]
    (pur : L₀ ⟶ (R(s)^![ModuleCat.{u + 1} Λ]).obj M) [IsIso pur]
    (δ : M ⟶ (R(p)^![ModuleCat.{u + 1} Λ]).obj K) [IsIso δ]
    [IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (s ≫ p)).counit.app K)] :
    IsIso (ψ ≫ α.hom.app L₀ ≫ (R(p)_![ModuleCat.{u + 1} Λ]).map
      ((R(s)_![ModuleCat.{u + 1} Λ]).map pur ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) s).counit.app M) ≫
      (R(p)_![ModuleCat.{u + 1} Λ]).map δ ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) p).counit.app K) := by
  have hε := (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) s).counit.naturality δ
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hε
  have hα := α.hom.naturality (pur ≫ (R(s)^![ModuleCat.{u + 1} Λ]).map δ)
  simp only [Functor.comp_obj, Functor.comp_map] at hα
  have hc := rightDerivedUpperShriekCompIsoOfLowerShriek_hom_app_counit Λ s p α K
  have key : ψ ≫ α.hom.app L₀ ≫ (R(p)_![ModuleCat.{u + 1} Λ]).map
      ((R(s)_![ModuleCat.{u + 1} Λ]).map pur ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) s).counit.app M) ≫
      (R(p)_![ModuleCat.{u + 1} Λ]).map δ ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) p).counit.app K =
      ψ ≫ (R(s ≫ p)_![ModuleCat.{u + 1} Λ]).map (pur ≫ (R(s)^![ModuleCat.{u + 1} Λ]).map δ ≫
        (rightDerivedUpperShriekCompIsoOfLowerShriek Λ s p α).hom.app K) ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (s ≫ p)).counit.app K := by
    simp only [Functor.map_comp, Category.assoc, hc]
    rw [α.hom.naturality_assoc, α.hom.naturality_assoc]
    simp only [Functor.comp_map]
    congr 3
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    congr 2
    exact hε.symm
  rw [key]
  infer_instance

/-- The identification `Lp^* Λ_Y(1)[2] ≅ Λ_{𝔸¹}(1)[2]` of the source of the smooth trace of the
affine line with the shifted Tate twist. -/
noncomputable def affineLineTwistShiftIso :
    (twistShift Λ 𝔸(ULift.{u} (Fin 1); Y) ((1 : ℕ) : ℤ)).obj
        ((L((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ Y)) ≅
      (tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧ :=
  (twistShift Λ _ _).mapIso (leftDerivedUpperStarConstantComplexIso Λ _) ≪≫
    twistShiftConstantComplexIso Λ _ _ ≪≫ eqToIso (by norm_num)

/-- The fundamental class `cl : R(s ≫ p)_! Λ ⟶ Rp_! Λ(1)[2]` of the affine line, the image of
the orientation of the zero section `s` under `Rp_!` and the counit of `Rs_! ⊣ Rs^!`, read
through a composition isomorphism `α : R(s ≫ p)_! ≅ Rs_! ⋙ Rp_!`. -/
noncomputable def affineLineFundamentalClass
    (α : R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)} ≫ (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))_![ModuleCat.{u + 1} Λ] ≅
      R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)})_![ModuleCat.{u + 1} Λ] ⋙
        R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]) :
    (R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Y) ↘ Y))_![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ _) ⟶
      (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧) :=
  α.hom.app _ ≫ (R(𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_![ModuleCat.{u + 1} Λ]).map
    ((R(𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)})_![ModuleCat.{u + 1} Λ]).map
        (affineLineOrientation Λ Y) ≫
      (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ)
        (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)})).counit.app
          ((tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1)⟦(2 : ℤ)⟧))

/-- Blueprint `thm-pur-trace-normalization-transitivity`: Trace normalization and transitivity

**The trace of the fundamental class is invertible.** Over a separably closed field, for every
purity isomorphism `γ_{p,Λ}` of the affine line, `Tr^sm_{p,Λ} ∘ cl ∘ ψ : Λ ⟶ Λ` is an
isomorphism. Through the composition isomorphism conjugate to `α` it is `R(s ≫ p)_!` of the
isomorphism `Λ_{V(t)} ≅ Rs^! Λ(1)[2] ≅ Rs^! Rp^! Λ ≅ R(s ≫ p)^! Λ` (the orientation
`AlgebraicGeometry.Etale.isIso_affineLineOrientation`, then `γ`), followed by the counit of
`R(s ≫ p)_! ⊣ R(s ≫ p)^!`, an isomorphism because `s ≫ p : V(t) ⟶ Spec k` is one. -/
theorem isIso_affineLineFundamentalClass_comp_smoothPurityTrace {k : Type u} [Field k]
    [IsSepClosed k] [HasKummerClass.IsNormalized Λ]
    [HasInvertibleExponent Λ (Spec (.of k))]
    [HasCompactification (𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
      {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
        (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))]
    (α : R(𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))_![ModuleCat.{u + 1} Λ] ≅
      R(𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)})_![ModuleCat.{u + 1} Λ] ⋙
        R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ])
    (ψ : constantComplex Λ (Spec (.of k)) ≅
      (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))_![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ _))
    (γ : (twistShift Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ((1 : ℕ) : ℤ)).obj
        ((L((𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^*[ModuleCat.{u + 1} Λ])).obj
          (constantComplex Λ (Spec (.of k)))) ≅
      (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ (Spec (.of k)))) :
    IsIso (ψ.hom ≫ affineLineFundamentalClass Λ (Spec (.of k)) α ≫
      (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ]).map
        (affineLineTwistShiftIso Λ (Spec (.of k))).inv ≫
      smoothPurityTrace Λ ((1 : ℕ) : ℤ) _ γ) := by
  have := isIso_affineLineOrientation Λ (Spec (.of k))
  let e := (AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) (Spec (.of k))
    (s := {AffineSpace.coord (Spec (.of k)) (ULift.up 0)}) Set.range_unique).symm
  have : HasCompactification e.hom := ‹_›
  have := isIso_rightDerivedUpperShriekAdjunction_counit_of_iso Λ e
  have : IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))).counit.app
      (constantComplex Λ (Spec (.of k)))) :=
    inferInstanceAs (IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ)
      e.hom).counit.app _))
  have h := isIso_comp_counit_comp_counit Λ _ _ α ψ.hom (affineLineOrientation Λ (Spec (.of k)))
    ((affineLineTwistShiftIso Λ (Spec (.of k))).inv ≫ γ.hom) (K := constantComplex Λ _)
  simpa only [affineLineFundamentalClass, smoothPurityTrace, Category.assoc,
    Functor.map_comp] using h

/-- Blueprint `thm-pur-trace-normalization-transitivity`: Trace normalization and transitivity

**Normalization on the affine line.** Over a separably closed field `k`, the smooth trace of
the affine line `p : 𝔸¹_k ⟶ Spec k` sends the fundamental class of `𝔸¹` to `1`: for every
composition isomorphism `α` and identification `ψ : Λ_k ≅ R(s ≫ p)_! Λ_{V(t)}` there is a
purity isomorphism `γ_{p,Λ} : Lp^* Λ(1)[2] ≅ Rp^! Λ` with `Tr^sm_{p,Λ} ∘ cl ∘ ψ = 1`. Together
with the transitivity `AlgebraicGeometry.Etale.smoothPurityTrace_comp` this gives the
normalization of
`Tr^sm_{p_d}` on the ordered fundamental class of `𝔸^d` by induction on `d`. -/
theorem exists_affineLineFundamentalClass_comp_smoothPurityTrace {k : Type u} [Field k]
    [IsSepClosed k] [HasKummerClass.IsNormalized Λ]
    [HasInvertibleExponent Λ (Spec (.of k))]
    [HasCompactification (𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
      {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
        (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))]
    (α : R(𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))_![ModuleCat.{u + 1} Λ] ≅
      R(𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)})_![ModuleCat.{u + 1} Λ] ⋙
        R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ])
    (ψ : constantComplex Λ (Spec (.of k)) ≅
      (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)).zeroLocusSubschemeι
        {AffineSpace.coord (Spec (.of k)) (ULift.up 0)} ≫
          (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))_![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ _)) :
    ∃ γ : (twistShift Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ((1 : ℕ) : ℤ)).obj
        ((L((𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^*[ModuleCat.{u + 1} Λ])).obj
          (constantComplex Λ (Spec (.of k)))) ≅
      (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ (Spec (.of k))),
      ψ.hom ≫ affineLineFundamentalClass Λ (Spec (.of k)) α ≫
        (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ]).map
          (affineLineTwistShiftIso Λ (Spec (.of k))).inv ≫
        smoothPurityTrace Λ ((1 : ℕ) : ℤ) _ γ = 𝟙 _ := by
  have : SmoothOfRelativeDimension 1 (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) := by
    have := AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin 1)) (Spec (.of k))
    rwa [show Nat.card (ULift.{u} (Fin 1)) = 1 by simp] at this
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) :=
    .of_hom (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))
  obtain ⟨θ⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := 1)
    (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)) (𝟙 _)
  let γ₀ : (twistShift Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k)) ((1 : ℕ) : ℤ)).obj
        ((L((𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^*[ModuleCat.{u + 1} Λ])).obj
          (constantComplex Λ (Spec (.of k)))) ≅
      (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ (Spec (.of k))) :=
    (twistShift Λ _ _).mapIso
      (leftDerivedUpperStarConstantComplexIso Λ (𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k)))
      ≪≫ θ.symm
  have hu := isIso_affineLineFundamentalClass_comp_smoothPurityTrace Λ α ψ γ₀
  refine ⟨γ₀ ≪≫
    (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))^![ModuleCat.{u + 1} Λ]).mapIso
      (asIso (ψ.hom ≫ affineLineFundamentalClass Λ (Spec (.of k)) α ≫
        (R(𝔸(ULift.{u} (Fin 1); Spec (.of k)) ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ]).map
          (affineLineTwistShiftIso Λ (Spec (.of k))).inv ≫
          smoothPurityTrace Λ ((1 : ℕ) : ℤ) _ γ₀)).symm, ?_⟩
  rw [smoothPurityTrace, Iso.trans_hom, Functor.map_comp, Category.assoc, Functor.mapIso_hom,
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) _).counit_naturality]
  simp only [smoothPurityTrace, Iso.symm_hom, asIso_inv] at hu ⊢
  simp only [← Category.assoc] at hu ⊢
  exact IsIso.hom_inv_id _

end Etale

end AlgebraicGeometry
