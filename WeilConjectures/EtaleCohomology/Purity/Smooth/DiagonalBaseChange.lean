/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompIsoExchangeCompatible
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalPasteHoriz
public import WeilConjectures.EtaleCohomology.Purity.Smooth.IdentitySquareBaseChange
public import WeilConjectures.CategoryTheory.Adjunction.MateCompConjugate

/-!
# The diagonal of a smooth morphism under base change

Let `g' ≫ f = f' ≫ g` be a cartesian square with `f`, `f'` smooth separated of relative
dimension `d`, and let `e : W' = X' ×_{Y'} X' ⟶ W = X ×_Y X` be the induced morphism
(`AlgebraicGeometry.Etale.IsoSquare.map`). The diagonals and the first projections of `W`, `W'`
form cartesian squares over `g'` (`AlgebraicGeometry.Etale.isPullback_diagonal_map`,
`AlgebraicGeometry.Etale.isPullback_map_fst`). This file proves the compatibilities of the
ingredients of the canonical orientation (`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`)
with the exceptional base change, for any such square:

* the smooth base change identifications `𝒞(p₁, Δ) ≅ ω_f`
  (`AlgebraicGeometry.Etale.sectionInvariantDiagonalIso_baseChange`);
* the composition isomorphisms `RΔ^! ω_{p₁} ≅ Λ_X`
  (`rightDerivedUpperShriekDualizingComplexIsoOfCompEqId_diagonal_baseChange`),
  from the vertical pasting of `Ex_!` along `Δ ≫ p₁ = 𝟙`, the identity square and the horizontal
  pasting of the exceptional base change along the rectangle `p₁' / f`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme IsoSquare

section Geometry

variable {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : IsPullback g' f' f g)

/-- The first projections of `X' ×_{Y'} X'` and `X ×_Y X` form a cartesian square over `g'`. -/
lemma isPullback_map_fst :
    IsPullback (IsoSquare.map sq) (pullback.fst f' f') (pullback.fst f f) g' := by
  have S₀ : IsPullback (pullback.snd f f) (pullback.fst f f) f f :=
    (IsPullback.of_hasPullback f f).flip
  have S₀' : IsPullback (pullback.snd f' f') (pullback.fst f' f') f' f' :=
    (IsPullback.of_hasPullback f' f').flip
  have R : IsPullback (IsoSquare.map sq ≫ pullback.snd f f) (pullback.fst f' f') f (g' ≫ f) := by
    rw [(commSq_snd sq).w, sq.w]
    exact S₀'.paste_horiz sq
  exact IsPullback.of_right R (by simp) S₀

/-- The diagonals of `X' ×_{Y'} X'` and `X ×_Y X` form a cartesian square over `g'`. -/
lemma isPullback_diagonal_map :
    IsPullback g' (pullback.diagonal f') (pullback.diagonal f) (IsoSquare.map sq) :=
  IsPullback.of_bot (by rw [pullback.diagonal_fst, pullback.diagonal_fst]; exact .id_vert g')
    (diagonal_comp_map sq).symm (isPullback_map_fst sq)

variable (g') in
/-- The square of `Δ ≫ p₁ = 𝟙` over `g'`. -/
lemma isPullback_diagonal_fst_map :
    IsPullback g' (pullback.diagonal f' ≫ pullback.fst f' f')
      (pullback.diagonal f ≫ pullback.fst f f) g' := by
  rw [pullback.diagonal_fst, pullback.diagonal_fst]
  exact .id_vert g'

end Geometry

-- `rfl` compares the tensor unit of `constantComplex` with the one inside the definition, which
-- needs a deep (but fast: elaboration and type checking well below 0.1 s, measured) recursion.
set_option maxRecDepth 20000 in
/-- The unfolding of
`AlgebraicGeometry.Etale.rightDerivedUpperShriekDualizingComplexIsoOfCompEqId`. -/
lemma IsoSquare.compEqId_eq (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {V B : Scheme.{u}}
    (p : V ⟶ B) [HasCompactification p] (s : B ⟶ V) [HasCompactification s] (hs : s ≫ p = 𝟙 B) :
    rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ p s hs =
      (conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ s).comp
          (rightDerivedUpperShriekAdjunction Λ p)) (rightDerivedUpperShriekAdjunction Λ (𝟙 B))
          (rightDerivedLowerShriekCompIsoOfEq Λ s p (𝟙 B) hs)).app (constantComplex Λ B) ≪≫
        (rightDerivedUpperShriekIdIso Λ B).app (constantComplex Λ B) :=
  rfl

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X}
  {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (d : ℕ)
  [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f'] [HasCompactification f]
  [HasCompactification f'] [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ X']
  [QuasiSeparatedSpace Y] [QuasiSeparatedSpace Y'] [QuasiCompact f] [QuasiCompact f']

/-- The exceptional base change of the dualizing complexes at the unit,
`Lg'^* ω_f ⟶ Rf'^! Lg^* Λ_Y ≅ ω_{f'}`, an isomorphism by smooth base change. -/
noncomputable def dualizingComplexBaseChangeIso :
    (L((g')^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ f' :=
  have : IsIso (upperShriekBaseChangeMap Λ sq) :=
    isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ f d sq
  asIso ((upperShriekBaseChangeMap Λ sq).app (constantComplex Λ Y) ≫
    (R(f')^![Λ]).map (leftDerivedUpperStarUnitIso _ g).hom)

/-- The identification `Le^* ω_{p₁} ≅ ω_{p₁'}` induced by `vω : Lg'^* ω_f ≅ ω_{f'}` through
`ω_{p₁} ≅ Lp₂^* ω_f` (`AlgebraicGeometry.Etale.dualizingComplexPullbackFstIso`) and the square
isomorphism `Le^* Lp₂^* ≅ Lp₂'^* Lg'^*`. -/
noncomputable def dualizingComplexPullbackFstBaseChangeIso
    (vω : (L((g')^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ f') :
    (L((IsoSquare.map sq)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ (pullback.fst f f)) ≅
      dualizingComplex Λ (pullback.fst f' f') :=
  (L((IsoSquare.map sq)^*[ModuleCat.{u + 1} Λ])).mapIso (dualizingComplexPullbackFstIso Λ f d) ≪≫
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) (commSq_snd sq)).symm.app
      (dualizingComplex Λ f) ≪≫
    (L((pullback.snd f' f')^*[ModuleCat.{u + 1} Λ])).mapIso vω ≪≫
    (dualizingComplexPullbackFstIso Λ f' d).symm

/-- **The smooth base change identifications `𝒞(p₁, Δ) ≅ ω_f` are compatible with base
change**, for the identification
`AlgebraicGeometry.Etale.dualizingComplexPullbackFstBaseChangeIso` of the dualizing complexes of
the first projections:
```
Lg'^* LΔ^* ω_{p₁} ──────────────Lg'^* c_f─────────────▶ Lg'^* ω_f
        ≅ │                                                │ vω
          ▼                                                ▼
LΔ'^* Le^* ω_{p₁} ──LΔ'^* vω₁──▶ LΔ'^* ω_{p₁'} ──c_{f'}──▶ ω_{f'}
```
where `c_f : 𝒞(p₁, Δ) = LΔ^* ω_{p₁} ≅ ω_f` and `vω₁` is induced by `vω`. -/
theorem sectionInvariantDiagonalIso_baseChange
    (vω : (L((g')^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ f) ≅ dualizingComplex Λ f') :
    (L((g')^*[ModuleCat.{u + 1} Λ])).map (sectionInvariantDiagonalIso Λ f d).hom ≫ vω.hom =
      (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) (isPullback_diagonal_map sq).toCommSq
          _ ≫
          (L((pullback.diagonal f')^*[ModuleCat.{u + 1} Λ])).map
            (dualizingComplexPullbackFstBaseChangeIso Λ sq d vω).hom) ≫
        (sectionInvariantDiagonalIso Λ f' d).hom := by
  have key := leftDerivedUpperStar_map_comp_compSectionIso (ModuleCat.{u + 1} Λ) g'
    (pullback.snd f f) (pullback.snd f' f') (IsoSquare.map sq) (pullback.diagonal f)
    (pullback.diagonal f') (commSq_snd sq).w (diagonal_comp_map sq) (pullback.diagonal_snd f)
    (pullback.diagonal_snd f') (dualizingComplex Λ f)
  rw [← derivedSquareUpperStarIso_hom_app_eq (ModuleCat.{u + 1} Λ)
    (isPullback_diagonal_map sq).toCommSq _ (diagonal_comp_map sq)] at key
  have hS : (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) (commSq_snd sq)).inv.app
      (dualizingComplex Λ f) =
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (IsoSquare.map sq) (pullback.snd f f)).inv.app
        (dualizingComplex Λ f) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (pullback.snd f' f') g'
        (IsoSquare.map sq ≫ pullback.snd f f) (commSq_snd sq).w).hom.app
        (dualizingComplex Λ f) := rfl
  rw [← hS] at key
  have hnat := (derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ)
    (isPullback_diagonal_map sq).toCommSq).inv.naturality (dualizingComplexPullbackFstIso Λ f d).hom
  simp only [Functor.comp_map] at hnat
  have hcs := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ) (pullback.diagonal f')
    (pullback.snd f' f') (pullback.diagonal_snd f')).hom.naturality vω.hom
  simp only [Functor.comp_map, Functor.id_map] at hcs
  simp only [sectionInvariantDiagonalIso, dualizingComplexPullbackFstBaseChangeIso,
    derivedSquareUpperStarIsoInvApp, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (L((pullback.diagonal f')^*[ModuleCat.{u + 1} Λ]))
      (dualizingComplexPullbackFstIso Λ f' d).inv (dualizingComplexPullbackFstIso Λ f' d).hom,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp, hcs, ← reassoc_of% hnat,
    reassoc_of% key, Iso.inv_hom_id_app_assoc]

-- the ascriptions compare `constantComplex` with the tensor unit (deep, fast)
set_option maxRecDepth 20000 in
/-- The comparison `Le^* ω_{p₁} ≅ ω_{p₁'}` of
`AlgebraicGeometry.Etale.dualizingComplexPullbackFstBaseChangeIso` induced by the exceptional base
change `Lg'^* ω_f ≅ ω_{f'}` is the exceptional base change of `p₁` at the unit. Both are the
exceptional base change of the rectangle `p₁' / f`, by horizontal pasting. -/
theorem dualizingComplexPullbackFstBaseChangeIso_hom_eq :
    (dualizingComplexPullbackFstBaseChangeIso Λ sq d
        (dualizingComplexBaseChangeIso Λ sq d)).hom =
      (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_map_fst sq)).app (constantComplex Λ X) ≫
        (R(pullback.fst f' f')^![Λ]).map (leftDerivedUpperStarConstantComplexIso Λ g').hom := by
  have S₀ : IsPullback (pullback.snd f f) (pullback.fst f f) f f :=
    (IsPullback.of_hasPullback f f).flip
  have S₀' : IsPullback (pullback.snd f' f') (pullback.fst f' f') f' f' :=
    (IsPullback.of_hasPullback f' f').flip
  have R : IsPullback (IsoSquare.map sq ≫ pullback.snd f f) (pullback.fst f' f') f (f' ≫ g) := by
    rw [(commSq_snd sq).w]; exact S₀'.paste_horiz sq
  have h1 := rightDerivedUpperShriekBaseChangeMap_paste_horiz (Λ := Λ) S₀ (isPullback_map_fst sq) R
    sq.w.symm rfl (constantComplex Λ Y)
  have h2 := rightDerivedUpperShriekBaseChangeMap_paste_horiz (Λ := Λ) sq S₀' R rfl
    (commSq_snd sq).w (constantComplex Λ Y)
  -- the pasting law `h1 = h2`, solved for the second decomposition
  have hE : (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (pullback.snd f' f') g'
          (IsoSquare.map sq ≫ pullback.snd f f) (commSq_snd sq).w).hom.app
          (dualizingComplex Λ f) ≫
        (L((pullback.snd f' f')^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekBaseChangeMap Λ sq).app (constantComplex Λ Y)) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ S₀').app
          ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ Y)) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (IsoSquare.map sq) (pullback.snd f f)
          (IsoSquare.map sq ≫ pullback.snd f f) rfl).hom.app (dualizingComplex Λ f) ≫
        (L((IsoSquare.map sq)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekBaseChangeMap Λ S₀).app (constantComplex Λ Y)) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_map_fst sq)).app
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ Y)) ≫
        (R(pullback.fst f' f')^![Λ]).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) g' f (f' ≫ g) sq.w.symm).inv.app
              (constantComplex Λ Y) ≫
            (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f' g (f' ≫ g) rfl).hom.app
              (constantComplex Λ Y)) := by
    have h := congrArg (fun t ↦ t ≫ (R(pullback.fst f' f')^![Λ]).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f' g (f' ≫ g) rfl).hom.app
        (constantComplex Λ Y))) (h1.symm.trans h2)
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id, Functor.comp_obj] at h
    exact h.symm
  -- naturality of the exceptional base changes along the unit identifications
  have hN := (rightDerivedUpperShriekBaseChangeMap Λ S₀').naturality
    (leftDerivedUpperStarConstantComplexIso Λ g).hom
  have hN2 := (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_map_fst sq)).naturality
    (leftDerivedUpperStarConstantComplexIso Λ f).hom
  simp only [Functor.comp_map] at hN hN2
  -- the unit coherence, under `Rp₁'^!`
  have hU : (R(pullback.fst f' f')^![Λ]).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) g' f (f' ≫ g) sq.w.symm).inv.app
            (constantComplex Λ Y) ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f' g (f' ≫ g) rfl).hom.app
            (constantComplex Λ Y)) ≫
        (R(pullback.fst f' f')^![Λ]).map ((L((f')^*[ModuleCat.{u + 1} Λ])).map
          (leftDerivedUpperStarConstantComplexIso Λ g).hom) ≫
        (R(pullback.fst f' f')^![Λ]).map (leftDerivedUpperStarConstantComplexIso Λ f').hom =
      (R(pullback.fst f' f')^![Λ]).map ((L((g')^*[ModuleCat.{u + 1} Λ])).map
          (leftDerivedUpperStarConstantComplexIso Λ f).hom) ≫
        (R(pullback.fst f' f')^![Λ]).map (leftDerivedUpperStarConstantComplexIso Λ g').hom := by
    simp only [← Functor.map_comp, Category.assoc, unit_coherence Λ sq]
  -- unfold the comparison
  have hI := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ f d S₀
  have hI' : IsIso (dualizingComplexBaseChangeMap Λ S₀) :=
    (isIso_dualizingComplexBaseChangeMap_iff Λ S₀).2 inferInstance
  simp only [dualizingComplexPullbackFstBaseChangeIso, dualizingComplexPullbackFstIso,
    dualizingComplexBaseChangeIso, upperShriekBaseChangeMap_eq, derivedSquareUpperStarIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, asIso_hom, asIso_inv,
    Functor.mapIso_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.map_inv, IsIso.inv_comp_eq, dualizingComplexBaseChangeMap_eq,
    dualizingComplexBaseChangeMap_eq, ← leftDerivedUpperStarConstantComplexIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hN, reassoc_of% hE, Iso.inv_hom_id_app_assoc, hU, ← reassoc_of% hN2]

variable [IsSeparated f] [IsSeparated f']

omit [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ X'] [QuasiSeparatedSpace Y]
  [QuasiSeparatedSpace Y'] in
/-- **Vertical pasting of `Ex_!` along `Δ ≫ p₁ = 𝟙`**: the compactly supported base change maps
of the squares of `Δ`, `p₁` and `𝟙 = Δ ≫ p₁` are compatible with the composition
isomorphisms. -/
theorem exchangeCompCompatible_diagonal_fst :
    Adjunction.ExchangeCompCompatible
      (rightDerivedLowerShriekBaseChangeMap Λ (isPullback_diagonal_map sq))
      (rightDerivedLowerShriekBaseChangeMap Λ (isPullback_map_fst sq))
      (rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.id_vert g'))
      (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f) (pullback.fst f f) (𝟙 X)
        (pullback.diagonal_fst f))
      (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f') (pullback.fst f' f') (𝟙 X')
        (pullback.diagonal_fst f')) := by
  refine exchangeCompCompatible_of_eq (pullback.diagonal_fst f) (pullback.diagonal_fst f') _ _
    (IsPullback.id_vert g') (isPullback_diagonal_fst_map g') ?_
  let _ : HasCompactification (pullback.diagonal f ≫ pullback.fst f f) :=
    HasCompactification.of_eq (pullback.diagonal_fst f).symm
  let _ : HasCompactification (pullback.diagonal f' ≫ pullback.fst f' f') :=
    HasCompactification.of_eq (pullback.diagonal_fst f').symm
  have : QuasiCompact (pullback.diagonal f ≫ pullback.fst f f) := by
    rw [pullback.diagonal_fst]; infer_instance
  have : QuasiCompact (pullback.diagonal f' ≫ pullback.fst f' f') := by
    rw [pullback.diagonal_fst]; infer_instance
  exact exchangeCompCompatible_rightDerivedLowerShriekCompIso _ _ _

-- the ascription compares `dualizingComplex` with `R^!` of `constantComplex` (deep, fast)
set_option maxRecDepth 20000 in
omit [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ X'] [QuasiSeparatedSpace Y]
  [QuasiSeparatedSpace Y'] in
/-- The pasting of the exceptional base changes along `Δ ≫ p₁ = 𝟙` at the unit, through the
conjugates of the composition isomorphisms. -/
lemma mate_paste_unit_diagonal :
    (L((g')^*[ModuleCat.{u + 1} Λ])).map
        ((conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ (pullback.diagonal f)).comp
          (rightDerivedUpperShriekAdjunction Λ (pullback.fst f f)))
          (rightDerivedUpperShriekAdjunction Λ (𝟙 X))
          (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f) (pullback.fst f f) (𝟙 X)
            (pullback.diagonal_fst f))).inv.app (constantComplex Λ X)) ≫
      (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_diagonal_map sq)).app
        (dualizingComplex Λ (pullback.fst f f)) ≫
      (R(pullback.diagonal f')^![Λ]).map
        ((rightDerivedUpperShriekBaseChangeMap Λ (isPullback_map_fst sq)).app
          (constantComplex Λ X)) =
      (rightDerivedUpperShriekBaseChangeMap Λ (IsPullback.id_vert g')).app (constantComplex Λ X) ≫
        (conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ (pullback.diagonal f')).comp
          (rightDerivedUpperShriekAdjunction Λ (pullback.fst f' f')))
          (rightDerivedUpperShriekAdjunction Λ (𝟙 X'))
          (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f') (pullback.fst f' f')
            (𝟙 X') (pullback.diagonal_fst f'))).inv.app
          ((L((g')^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X)) :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ (isPullback_diagonal_map sq)
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ (isPullback_map_fst sq)
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.id_vert g')
  Adjunction.mateEquiv_inv_comp_conjugate _ _ _ _ _ _ _ _ _ _ _
    (exchangeCompCompatible_diagonal_fst Λ sq) (constantComplex Λ X)

/-- **The composition isomorphisms `RΔ^! ω_{p₁} ≅ Λ_X` are compatible with base change**
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekDualizingComplexIsoOfCompEqId` for the diagonal,
a section of the first projection), through the exceptional base change and the identification
`vω₁ : Le^* ω_{p₁} ≅ ω_{p₁'}` of
`AlgebraicGeometry.Etale.dualizingComplexPullbackFstBaseChangeIso`:
```
Lg'^* RΔ^! ω_{p₁} ────────────Lg'^* ε────────────▶ Lg'^* Λ_X
         β │                                          │ ≅
           ▼                                          ▼
RΔ'^! Le^* ω_{p₁} ──RΔ'^! vω₁──▶ RΔ'^! ω_{p₁'} ──ε'──▶ Λ_{X'}
```
-/
theorem rightDerivedUpperShriekDualizingComplexIsoOfCompEqId_diagonal_baseChange :
    (L((g')^*[ModuleCat.{u + 1} Λ])).map
          (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ (pullback.fst f f)
            (pullback.diagonal f) (pullback.diagonal_fst f)).hom ≫
        (leftDerivedUpperStarConstantComplexIso Λ g').hom =
      ((rightDerivedUpperShriekBaseChangeMap Λ (isPullback_diagonal_map sq)).app
          (dualizingComplex Λ (pullback.fst f f)) ≫
          (R(pullback.diagonal f')^![Λ]).map
            (dualizingComplexPullbackFstBaseChangeIso Λ sq d
              (dualizingComplexBaseChangeIso Λ sq d)).hom) ≫
        (rightDerivedUpperShriekDualizingComplexIsoOfCompEqId Λ (pullback.fst f' f')
          (pullback.diagonal f') (pullback.diagonal_fst f')).hom := by
  have key := mate_paste_unit_diagonal Λ sq
  have key' : (rightDerivedUpperShriekBaseChangeMap Λ (isPullback_diagonal_map sq)).app
        (dualizingComplex Λ (pullback.fst f f)) ≫
      (R(pullback.diagonal f')^![Λ]).map
        ((rightDerivedUpperShriekBaseChangeMap Λ (isPullback_map_fst sq)).app
          (constantComplex Λ X)) =
      (L((g')^*[ModuleCat.{u + 1} Λ])).map
          ((conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ (pullback.diagonal f)).comp
            (rightDerivedUpperShriekAdjunction Λ (pullback.fst f f)))
            (rightDerivedUpperShriekAdjunction Λ (𝟙 X))
            (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f) (pullback.fst f f) (𝟙 X)
              (pullback.diagonal_fst f))).hom.app (constantComplex Λ X)) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ (IsPullback.id_vert g')).app
          (constantComplex Λ X) ≫
        (conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ (pullback.diagonal f')).comp
          (rightDerivedUpperShriekAdjunction Λ (pullback.fst f' f')))
          (rightDerivedUpperShriekAdjunction Λ (𝟙 X'))
          (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f') (pullback.fst f' f')
            (𝟙 X') (pullback.diagonal_fst f'))).inv.app
          ((L((g')^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X)) := by
    rw [← key, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hnat := (conjugateIsoEquiv ((rightDerivedUpperShriekAdjunction Λ (pullback.diagonal f')).comp
      (rightDerivedUpperShriekAdjunction Λ (pullback.fst f' f')))
      (rightDerivedUpperShriekAdjunction Λ (𝟙 X'))
      (rightDerivedLowerShriekCompIsoOfEq Λ (pullback.diagonal f') (pullback.fst f' f')
        (𝟙 X') (pullback.diagonal_fst f'))).inv.naturality
    (leftDerivedUpperStarConstantComplexIso Λ g').hom
  simp only [Functor.comp_map] at hnat
  have hid := (rightDerivedUpperShriekIdIso Λ X').hom.naturality
    (leftDerivedUpperStarConstantComplexIso Λ g').hom
  simp only [Functor.id_map] at hid
  rw [dualizingComplexPullbackFstBaseChangeIso_hom_eq, compEqId_eq, compEqId_eq]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% key', ← reassoc_of% hnat, Iso.inv_hom_id_app_assoc, hid,
    reassoc_of% (rightDerivedUpperShriekBaseChangeMap_id_app_comp Λ g' (IsPullback.id_vert g')
      (constantComplex Λ X))]

end AlgebraicGeometry.Etale
