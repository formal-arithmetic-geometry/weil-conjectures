/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageComparisonMap
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquarePaths
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareComponent
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquarePasting
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionMapDerived

/-!
# Transport of unbounded base change along the site comparison

For a Cartesian square of schemes

```
  X' ──g'──▶ X
  │          │
  f'         f
  ▼          ▼
  Y' ──g───▶ Y
```

and `L ∈ D(X_ét, Λ)` (unbounded), the étale exchange map `Lg^* Rf_* L ⟶ Rf'_* Lg'^* L`
(`AlgebraicGeometry.Etale.derivedBaseChangeMap`) and the pro-étale exchange map at `ν_X^* L`
(`AlgebraicGeometry.ProEtale.derivedBaseChangeMap`) are identified through the comparison
`ν^*`: this is `AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap_unbounded`, the
unbounded analogue of `AlgebraicGeometry.ProEtale.comparison_derivedBaseChangeMap`. The
direct image comparisons are `AlgebraicGeometry.ProEtale.unboundedDirectImageComparisonMap`, the
pullback comparisons `AlgebraicGeometry.ProEtale.leftDerivedUpperStarComparisonIsoUnbounded`.
Consequently (`AlgebraicGeometry.ProEtale.isIso_derivedBaseChangeMap_app_comparisonUpperStar`)
the pro-étale exchange map at `ν_X^* L` is an isomorphism whenever the étale one at `L` and the
two relevant unbounded direct image comparison maps are.

The proof transports mates along comparison functors
(`CategoryTheory.mateEquiv_app_comparison_transport`). Its inputs are the compatibility of the
unbounded direct image comparison with the counits, which holds by construction, and the
commutativity of the cube of pullback comparisons. The latter is reduced to the underived
coherence `AlgebraicGeometry.ProEtale.comparison_square_component_of_commRing`: exact derivation
preserves commutative cubes (`CategoryTheory.Functor.mapDerivedCategorySquareIso_cube`), and
replacing the induced functors `D(-)` by the derived pullbacks `L(-)` conjugates the cube
(`CategoryTheory.cube_conjugation`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

section MateTransport

variable {E₀ E₁ E₂ E₃ P₀ P₁ P₂ P₃ : Type*}
  [Category E₀] [Category E₁] [Category E₂] [Category E₃]
  [Category P₀] [Category P₁] [Category P₂] [Category P₃]
  {l : E₀ ⥤ E₁} {r : E₁ ⥤ E₀} {l' : E₂ ⥤ E₃} {r' : E₃ ⥤ E₂}
  {p : P₀ ⥤ P₁} {s : P₁ ⥤ P₀} {p' : P₂ ⥤ P₃} {s' : P₃ ⥤ P₂}
  {g : E₀ ⥤ E₂} {h : E₁ ⥤ E₃} {q : P₀ ⥤ P₂} {t : P₁ ⥤ P₃}
  {A₀ : E₀ ⥤ P₀} {A₁ : E₁ ⥤ P₁} {A₂ : E₂ ⥤ P₂} {A₃ : E₃ ⥤ P₃}

/-- Transport of mates along comparison functors. Consider two squares of left adjoints
```
        g                      q
   E₀ ────▶ E₂            P₀ ────▶ P₂
   │        │             │        │
  l│   θ    │l'          p│   ϑ    │p'
   ▼        ▼             ▼        ▼
   E₁ ────▶ E₃            P₁ ────▶ P₃
        h                      t
```
with `e : l ⊣ r`, `e' : l' ⊣ r'`, `d : p ⊣ s`, `d' : p' ⊣ s'`, and comparison functors
`Aᵢ : Eᵢ ⥤ Pᵢ` together with isomorphisms `a, a', c, c'` between the left adjoints and
families of maps `b, b'` between the right adjoints (not required to be natural). If `b, b'`
are compatible with the counits (`hb`, `hb'`) and the cube of left adjoints commutes (`hsq`),
then the mate of `θ`, conjugated by the comparison functors, is the mate of `ϑ`. -/
theorem CategoryTheory.mateEquiv_app_comparison_transport (e : l ⊣ r) (e' : l' ⊣ r')
    (d : p ⊣ s) (d' : p' ⊣ s') (a : l ⋙ A₁ ≅ A₀ ⋙ p) (a' : l' ⋙ A₃ ≅ A₂ ⋙ p')
    (c : g ⋙ A₂ ≅ A₀ ⋙ q) (c' : h ⋙ A₃ ≅ A₁ ⋙ t)
    (b : ∀ K, A₀.obj (r.obj K) ⟶ s.obj (A₁.obj K))
    (b' : ∀ K, A₂.obj (r'.obj K) ⟶ s'.obj (A₃.obj K))
    (θ : g ⋙ l' ⟶ l ⋙ h) (ϑ : q ⋙ p' ⟶ p ⋙ t)
    (hb : ∀ K, a.hom.app (r.obj K) ≫ p.map (b K) ≫ d.counit.app (A₁.obj K) =
      A₁.map (e.counit.app K))
    (hb' : ∀ K, a'.hom.app (r'.obj K) ≫ p'.map (b' K) ≫ d'.counit.app (A₃.obj K) =
      A₃.map (e'.counit.app K))
    (hsq : ∀ M, A₃.map (θ.app M) ≫ c'.hom.app (l.obj M) ≫ t.map (a.hom.app M) =
      a'.hom.app (g.obj M) ≫ p'.map (c.hom.app M) ≫ ϑ.app (A₀.obj M)) (K : E₁) :
    A₂.map ((mateEquiv e e' (TwoSquare.mk _ _ _ _ θ)).natTrans.app K) ≫ b' (h.obj K) ≫
      s'.map (c'.hom.app K) =
    c.hom.app (r.obj K) ≫ q.map (b K) ≫
      (mateEquiv d d' (TwoSquare.mk _ _ _ _ ϑ)).natTrans.app (A₁.obj K) := by
  apply (d'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  apply (cancel_epi (a'.hom.app (g.obj (r.obj K)))).1
  have hn := a'.hom.naturality ((mateEquiv e e' (TwoSquare.mk _ _ _ _ θ)).natTrans.app K)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [d'.counit_naturality, reassoc_of% hb']
  rw [← A₃.map_comp_assoc, mateEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  have hn' := c'.hom.naturality (e.counit.app K)
  simp only [Functor.comp_map] at hn'
  erw [hn', mateEquiv_counit]
  have ht := ϑ.naturality (b K)
  simp only [Functor.comp_map] at ht
  erw [reassoc_of% ht, ← reassoc_of% hsq]
  simp only [← Functor.map_comp, hb, TwoSquare.mk, Functor.comp_obj]

end MateTransport

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section SquareIso

variable {A B B' B'' E : Type*} [Category A] [Category B] [Category B'] [Category B'']
  [Category E]
  [Abelian A] [Abelian B] [Abelian B'] [Abelian B''] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory B']
  [HasDerivedCategory B''] [HasDerivedCategory E]

/-- The derived comparison of a vertical composite of two squares with the same edges is the
composite of the derived comparisons. -/
lemma mapDerivedCategorySquareIso_trans_hom {F₁ : A ⥤ B} {F₂ : B ⥤ E} {H₁ : A ⥤ B'}
    {H₂ : B' ⥤ E} {G₁ : A ⥤ B''} {G₂ : B'' ⥤ E}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [H₁.Additive] [PreservesFiniteLimits H₁] [PreservesFiniteColimits H₁]
    [H₂.Additive] [PreservesFiniteLimits H₂] [PreservesFiniteColimits H₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (x : F₁ ⋙ F₂ ≅ H₁ ⋙ H₂) (y : H₁ ⋙ H₂ ≅ G₁ ⋙ G₂) :
    (mapDerivedCategorySquareIso (x ≪≫ y)).hom =
      (mapDerivedCategorySquareIso x).hom ≫ (mapDerivedCategorySquareIso y).hom := by
  simp [mapDerivedCategoryNatIso_trans]

/-- The derived comparison of a left whiskered isomorphism is the whiskered derived
isomorphism. -/
lemma mapDerivedCategorySquareIso_isoWhiskerLeft_hom (F : A ⥤ B) {G G' : B ⥤ E}
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (e : G ≅ G') :
    (mapDerivedCategorySquareIso (F₁ := F) (F₂ := G) (G₁ := F) (G₂ := G')
      (isoWhiskerLeft F e)).hom = whiskerLeft D(F) (mapDerivedCategoryNatIso e).hom := by
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom]
  rw [mapDerivedCategoryNatIso_isoWhiskerLeft, Iso.hom_inv_id_assoc]

/-- The derived comparison of a right whiskered isomorphism is the whiskered derived
isomorphism. -/
lemma mapDerivedCategorySquareIso_isoWhiskerRight_hom {F F' : A ⥤ B} (G : B ⥤ E)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ F') :
    (mapDerivedCategorySquareIso (F₁ := F) (F₂ := G) (G₁ := F') (G₂ := G)
      (isoWhiskerRight e G)).hom = whiskerRight (mapDerivedCategoryNatIso e).hom D(G) := by
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom]
  rw [mapDerivedCategoryNatIso_isoWhiskerRight, Iso.hom_inv_id_assoc]

end SquareIso

section Cube

variable {A B B' C P Q Q' R : Type*}
  [Category A] [Category B] [Category B'] [Category C]
  [Category P] [Category Q] [Category Q'] [Category R]
  [Abelian A] [Abelian B] [Abelian B'] [Abelian C]
  [Abelian P] [Abelian Q] [Abelian Q'] [Abelian R]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory B']
  [HasDerivedCategory C] [HasDerivedCategory P] [HasDerivedCategory Q]
  [HasDerivedCategory Q'] [HasDerivedCategory R]
  {L₁ : A ⥤ B} {L₂ : B ⥤ C} {L₁' : A ⥤ B'} {L₂' : B' ⥤ C}
  {K₀ : A ⥤ P} {K₁ : B ⥤ Q} {K₁' : B' ⥤ Q'} {K₂ : C ⥤ R}
  {R₁ : P ⥤ Q} {R₂ : Q ⥤ R} {R₁' : P ⥤ Q'} {R₂' : Q' ⥤ R}
  [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [L₁'.Additive] [PreservesFiniteLimits L₁'] [PreservesFiniteColimits L₁']
  [L₂'.Additive] [PreservesFiniteLimits L₂'] [PreservesFiniteColimits L₂']
  [K₀.Additive] [PreservesFiniteLimits K₀] [PreservesFiniteColimits K₀]
  [K₁.Additive] [PreservesFiniteLimits K₁] [PreservesFiniteColimits K₁]
  [K₁'.Additive] [PreservesFiniteLimits K₁'] [PreservesFiniteColimits K₁']
  [K₂.Additive] [PreservesFiniteLimits K₂] [PreservesFiniteColimits K₂]
  [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [R₁'.Additive] [PreservesFiniteLimits R₁'] [PreservesFiniteColimits R₁']
  [R₂'.Additive] [PreservesFiniteLimits R₂'] [PreservesFiniteColimits R₂']

/-- Exact derivation preserves commutative cubes of comparison squares: if the cube
```
        L₁       L₂                 L₁'      L₂'
   A ────▶ B ────▶ C           A ────▶ B' ────▶ C
   │       │       │           │       │        │
 K₀│  c₁   │K₁ c₂  │K₂       K₀│  c₁'  │K₁' c₂' │K₂
   ▼       ▼       ▼           ▼       ▼        ▼
   P ────▶ Q ────▶ R           P ────▶ Q' ────▶ R
        R₁       R₂                 R₁'      R₂'
```
with top face `se` and bottom face `sp` commutes, that is, the two pasted isomorphisms
`(L₁ ⋙ L₂) ⋙ K₂ ≅ K₀ ⋙ (R₁' ⋙ R₂')` agree, then so does the cube of the derived comparisons
`mapDerivedCategorySquareIso` on unbounded derived categories. -/
theorem mapDerivedCategorySquareIso_cube (c₂ : L₂ ⋙ K₂ ≅ K₁ ⋙ R₂)
    (c₁ : L₁ ⋙ K₁ ≅ K₀ ⋙ R₁) (c₂' : L₂' ⋙ K₂ ≅ K₁' ⋙ R₂') (c₁' : L₁' ⋙ K₁' ≅ K₀ ⋙ R₁')
    (se : L₁ ⋙ L₂ ≅ L₁' ⋙ L₂') (sp : R₁ ⋙ R₂ ≅ R₁' ⋙ R₂')
    (h : isoWhiskerLeft L₁ c₂ ≪≫ isoWhiskerRight c₁ R₂ ≪≫ isoWhiskerLeft K₀ sp =
      isoWhiskerRight se K₂ ≪≫ isoWhiskerLeft L₁' c₂' ≪≫ isoWhiskerRight c₁' R₂')
    (M : DerivedCategory A) :
    (mapDerivedCategorySquareIso c₂).hom.app (D(L₁).obj M) ≫
        D(R₂).map ((mapDerivedCategorySquareIso c₁).hom.app M) ≫
        (mapDerivedCategorySquareIso sp).hom.app (D(K₀).obj M) =
      D(K₂).map ((mapDerivedCategorySquareIso se).hom.app M) ≫
        (mapDerivedCategorySquareIso c₂').hom.app (D(L₁').obj M) ≫
        D(R₂').map ((mapDerivedCategorySquareIso c₁').hom.app M) := by
  have hpath : (isoWhiskerLeft L₁ c₂ ≪≫ isoWhiskerRight c₁ R₂) ≪≫ isoWhiskerLeft K₀ sp =
      isoWhiskerRight se K₂ ≪≫ (isoWhiskerLeft L₁' c₂' ≪≫ isoWhiskerRight c₁' R₂') :=
    (Iso.trans_assoc _ _ _).trans h
  have hS := congrArg (fun e ↦ (mapDerivedCategorySquareIso (F₁ := L₁ ⋙ L₂) (F₂ := K₂)
    (G₁ := K₀) (G₂ := R₁' ⋙ R₂') e).hom.app M) hpath
  replace hS := hS
  rw [mapDerivedCategorySquareIso_trans_hom (H₁ := K₀) (H₂ := R₁ ⋙ R₂),
    mapDerivedCategorySquareIso_trans_hom (H₁ := L₁' ⋙ L₂') (H₂ := K₂),
    mapDerivedCategorySquareIso_paste, mapDerivedCategorySquareIso_paste,
    mapDerivedCategorySquareIso_isoWhiskerLeft_hom,
    mapDerivedCategorySquareIso_isoWhiskerRight_hom] at hS
  have hS' := D(K₂).map ((mapDerivedCategoryCompIso L₁ L₂).hom.app M) ≫= hS =≫
    (mapDerivedCategoryCompIso R₁' R₂').inv.app (D(K₀).obj M)
  simp only [NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, Iso.symm_hom, Category.assoc] at hS'
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc] at hS' ⊢
  rw [← Functor.map_comp_assoc D(K₂) ((mapDerivedCategoryCompIso L₁ L₂).hom.app M)
    ((mapDerivedCategoryCompIso L₁ L₂).inv.app M), Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp] at hS'
  simpa only [Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id] using hS'

end Cube

end CategoryTheory.Functor

section CubeConjugation

variable {E₀ E₁ E₂ E₃ P₀ P₁ P₂ P₃ : Type*}
  [Category E₀] [Category E₁] [Category E₂] [Category E₃]
  [Category P₀] [Category P₁] [Category P₂] [Category P₃]
  {l lD : E₀ ⥤ E₁} {l' l'D : E₂ ⥤ E₃} {g gD : E₀ ⥤ E₂} {h hD : E₁ ⥤ E₃}
  {p pD : P₀ ⥤ P₁} {p' p'D : P₂ ⥤ P₃} {q qD : P₀ ⥤ P₂} {t tD : P₁ ⥤ P₃}
  {A₀ : E₀ ⥤ P₀} {A₁ : E₁ ⥤ P₁} {A₂ : E₂ ⥤ P₂} {A₃ : E₃ ⥤ P₃}

/-- A commutative cube of comparison squares stays commutative after replacing each of the
eight edge functors `lD, l'D, gD, hD, pD, p'D, qD, tD` by an isomorphic functor and
conjugating the six faces accordingly. -/
theorem CategoryTheory.cube_conjugation (jl : l ≅ lD) (jl' : l' ≅ l'D) (jg : g ≅ gD)
    (jh : h ≅ hD) (kp : p ≅ pD) (kp' : p' ≅ p'D) (kq : q ≅ qD) (kt : t ≅ tD)
    (Sl : lD ⋙ A₁ ≅ A₀ ⋙ pD) (Sl' : l'D ⋙ A₃ ≅ A₂ ⋙ p'D) (Sg : gD ⋙ A₂ ≅ A₀ ⋙ qD)
    (Sh : hD ⋙ A₃ ≅ A₁ ⋙ tD) (θD : gD ⋙ l'D ≅ lD ⋙ hD) (ϑD : qD ⋙ p'D ≅ pD ⋙ tD)
    (hcube : ∀ M, Sl'.hom.app (gD.obj M) ≫ p'D.map (Sg.hom.app M) ≫ ϑD.hom.app (A₀.obj M) =
      A₃.map (θD.hom.app M) ≫ Sh.hom.app (lD.obj M) ≫ tD.map (Sl.hom.app M)) (M : E₀) :
    A₃.map (((Functor.isoWhiskerLeft g jl' ≪≫ Functor.isoWhiskerRight jg l'D) ≪≫ θD ≪≫
        (Functor.isoWhiskerLeft l jh ≪≫ Functor.isoWhiskerRight jl hD).symm).hom.app M) ≫
      (Functor.isoWhiskerRight jh A₃ ≪≫ Sh ≪≫ Functor.isoWhiskerLeft A₁ kt.symm).hom.app
        (l.obj M) ≫
      t.map ((Functor.isoWhiskerRight jl A₁ ≪≫ Sl ≪≫
        Functor.isoWhiskerLeft A₀ kp.symm).hom.app M) =
    (Functor.isoWhiskerRight jl' A₃ ≪≫ Sl' ≪≫ Functor.isoWhiskerLeft A₂ kp'.symm).hom.app
        (g.obj M) ≫
      p'.map ((Functor.isoWhiskerRight jg A₂ ≪≫ Sg ≪≫
        Functor.isoWhiskerLeft A₀ kq.symm).hom.app M) ≫
      ((Functor.isoWhiskerLeft q kp' ≪≫ Functor.isoWhiskerRight kq p'D) ≪≫ ϑD ≪≫
        (Functor.isoWhiskerLeft p kt ≪≫ Functor.isoWhiskerRight kp tD).symm).hom.app
        (A₀.obj M) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc, Functor.comp_obj]
  have h₁ := Sh.hom.naturality (jl.inv.app M)
  have h₂ := Sl'.hom.naturality (jg.hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂
  rw [← A₃.map_comp_assoc (jh.inv.app (l.obj M)), Iso.inv_hom_id_app, A₃.map_id,
    Category.id_comp, reassoc_of% h₁, ← kt.inv.naturality_assoc, ← kt.inv.naturality_assoc,
    ← kt.inv.naturality, ← tD.map_comp_assoc, ← A₁.map_comp, Iso.inv_hom_id_app,
    A₁.map_id, tD.map_id, Category.id_comp]
  rw [← kp'.inv.naturality_assoc, ← kp'.inv.naturality_assoc, ← kp'.inv.naturality_assoc,
    Iso.inv_hom_id_app_assoc, ← p'D.map_comp_assoc (kq.inv.app (A₀.obj M)),
    Iso.inv_hom_id_app, p'D.map_id, Category.id_comp, ← reassoc_of% h₂, reassoc_of% (hcube M)]

end CubeConjugation

namespace AlgebraicGeometry

/-- The composition isomorphism `Etale.upperStarComp` along a morphism `h₁₂` equal to the
composite `h₁ ≫ h₂` is the one along the composite, preceded by the transport along
`h₁₂ = h₁ ≫ h₂`. -/
lemma Etale.upperStarComp_eq_eqToIso_trans (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] {T S R : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R)
    (h₁₂ : T ⟶ R) (hh₁₂ : h₁₂ = h₁ ≫ h₂) :
    Etale.upperStarComp A h₁ h₂ h₁₂ hh₁₂ =
      eqToIso (congrArg (Etale.upperStar A) hh₁₂) ≪≫ Etale.upperStarComp A h₁ h₂ := by
  subst hh₁₂
  simp

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The unbounded comparison `L(f^*) ν_X^* ≅ ν_Y^* L(f^*)` between the étale and the
pro-étale derived pullbacks along `f : X ⟶ Y`, as functors `D(Y_ét) ⥤ D(X_proét)`: both
derived pullbacks are identified with the functors induced by the exact pullbacks, which
commute with the comparison by `comparisonUpperStarCompUpperStarIso`. -/
noncomputable def leftDerivedUpperStarComparisonIsoUnbounded {X Y : Scheme.{u}} (f : X ⟶ Y) :
    L(Etale.upperStar (ModuleCat.{u + 1} Λ) f) ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ]) ≅
      D(ν^*(Y)[ModuleCat.{u + 1} Λ]) ⋙ L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f) :=
  Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ f) _ ≪≫
    Functor.mapDerivedCategorySquareIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ f).symm

/-- The unbounded direct image comparison map is compatible with the counits of the étale
and the pro-étale derived adjunctions `Lf^* ⊣ Rf_*`. -/
theorem leftDerivedUpperStarComparisonIsoUnbounded_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarComparisonIsoUnbounded Λ f).hom.app
        (R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
        (unboundedDirectImageComparisonMap Λ f K) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K) =
    D(ν^*(X)[ModuleCat.{u + 1} Λ]).map
      ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  have hb : (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategory.map
        (unboundedDirectImageComparisonMap Λ f K) ≫
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        f).mapDerivedCategoryRightDerivedAdjunction.counit.app
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K) =
      (unboundedDirectImagePullbackIso Λ f).hom.app
          ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj K) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
          ((Etale.upperStarLowerStarAdjunction
            (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryRightDerivedAdjunction.counit.app K) := by
    have h := (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      f).mapDerivedCategoryRightDerivedAdjunction.homEquiv_counit
      (g := unboundedDirectImageComparisonMap Λ f K)
    rw [← h]
    exact Equiv.symm_apply_apply _ _
  simp only [derivedUpperStarLowerStarAdjunction, Etale.derivedUpperStarLowerStarAdjunction,
    Adjunction.derivedAdjunction_eq_ofNatIsoLeft, Adjunction.ofNatIsoLeft_counit,
    leftDerivedUpperStarComparisonIsoUnbounded, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Iso.symm_inv, Category.assoc, Functor.map_comp,
    leftDerivedUpperStarIsoMapDerivedCategory, Etale.leftDerivedUpperStarIsoMapDerivedCategory]
  rw [(Functor.leftDerivedFunctorIsoMapDerivedCategory
    (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f)).hom.naturality_assoc
    (unboundedDirectImageComparisonMap Λ f K), Iso.inv_hom_id_app_assoc, hb]
  simp [unboundedDirectImagePullbackIso, Functor.mapDerivedCategoryNatIso_symm]

/-- The étale derived square isomorphism `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of a commutative square,
expressed through the functors induced by the exact pullbacks and the underived square
isomorphism. -/
theorem Etale.derivedSquareUpperStarIso_eq_mapDerivedCategorySquareIso
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq =
      (Functor.isoWhiskerLeft L(Etale.upperStar (ModuleCat.{u + 1} Λ) g)
          (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ f') ≪≫
        Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ g)
          D(Etale.upperStar (ModuleCat.{u + 1} Λ) f')) ≪≫
      Functor.mapDerivedCategorySquareIso
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) f' g).symm ≪≫
          eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm) ≪≫
          Etale.upperStarComp (ModuleCat.{u + 1} Λ) g' f) ≪≫
      (Functor.isoWhiskerLeft L(Etale.upperStar (ModuleCat.{u + 1} Λ) f)
          (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ g') ≪≫
        Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ f)
          D(Etale.upperStar (ModuleCat.{u + 1} Λ) g')).symm := by
  have hc : (Functor.mapDerivedCategoryNatIso
      (Etale.upperStarComp (ModuleCat.{u + 1} Λ) f' g (g' ≫ f) sq.w)).inv =
      (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} Λ) f' g)).inv ≫
        (Functor.mapDerivedCategoryNatIso
          (eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm))).hom := by
    rw [Etale.upperStarComp_eq_eqToIso_trans _ f' g (g' ≫ f) sq.w,
      ← Functor.mapDerivedCategoryNatIso_symm, Iso.trans_symm,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm]
    congr 2
  ext M
  simp [Etale.derivedSquareUpperStarIso, Etale.leftDerivedUpperStarComp, hc,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    Etale.leftDerivedUpperStarIsoMapDerivedCategory, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm]

/-- Transport of the pro-étale derived pullback along an equality of morphisms is induced by
the transport of the underived pullback. -/
theorem leftDerivedUpperStarCongr_eq {X Y : Scheme.{u}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) :
    leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) h =
      leftDerivedUpperStarIsoMapDerivedCategory _ f₁ ≪≫
        Functor.mapDerivedCategoryNatIso
          (eqToIso (congrArg (ProEtale.upperStar (ModuleCat.{u + 1} Λ)) h)) ≪≫
        (leftDerivedUpperStarIsoMapDerivedCategory _ f₂).symm := by
  subst h
  ext M
  simp [Functor.mapDerivedCategoryNatIso_refl]

/-- The pro-étale derived square isomorphism `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of a commutative
square, expressed through the functors induced by the exact pullbacks and the underived square
isomorphism. -/
theorem leftDerivedUpperStarSquareIso_eq_mapDerivedCategorySquareIso
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq =
      (Functor.isoWhiskerLeft L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g)
          (leftDerivedUpperStarIsoMapDerivedCategory _ f') ≪≫
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ g)
          D(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f')) ≪≫
      Functor.mapDerivedCategorySquareIso
        ((ProEtale.upperStarComp (ModuleCat.{u + 1} Λ) f' g).symm ≪≫
          eqToIso (congrArg (ProEtale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm) ≪≫
          ProEtale.upperStarComp (ModuleCat.{u + 1} Λ) g' f) ≪≫
      (Functor.isoWhiskerLeft L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f)
          (leftDerivedUpperStarIsoMapDerivedCategory _ g') ≪≫
        Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ f)
          D(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g')).symm := by
  ext M
  simp [leftDerivedUpperStarSquareIso, leftDerivedUpperStarComp, leftDerivedUpperStarCongr_eq,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm]

/-- The underived comparison pullbacks commute with the étale and the pro-étale square
isomorphisms of a Cartesian square, written with `Etale.upperStarComp` and
`ProEtale.upperStarComp`: the two pasted isomorphisms `g^* f'^* ν_{X'}^* ≅ ν_Y^* f^* g'^*`
agree. -/
theorem comparisonUpperStarCompUpperStarIso_square
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) :
    Functor.isoWhiskerLeft (Etale.upperStar (ModuleCat.{u + 1} Λ) g)
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f').symm ≪≫
      Functor.isoWhiskerRight (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f') ≪≫
      Functor.isoWhiskerLeft ν^*(Y)[ModuleCat.{u + 1} Λ]
        ((ProEtale.upperStarComp (ModuleCat.{u + 1} Λ) f' g).symm ≪≫
          eqToIso (congrArg (ProEtale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm) ≪≫
          ProEtale.upperStarComp (ModuleCat.{u + 1} Λ) g' f) =
    Functor.isoWhiskerRight
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) f' g).symm ≪≫
          eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm) ≪≫
          Etale.upperStarComp (ModuleCat.{u + 1} Λ) g' f) ν^*(X')[ModuleCat.{u + 1} Λ] ≪≫
      Functor.isoWhiskerLeft (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g').symm ≪≫
      Functor.isoWhiskerRight (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm
        (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g') := by
  let cs : ChosenCartesianSquare g' f' f g :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  have he : comparisonSquareEtalePath Λ cs = comparisonSquareProEtalePath Λ cs :=
    comparisonSquarePaths_eq (comparisonSquareData (ModuleCat.{u + 1} Λ) g' f' f g cs)
      (comparison_square_component_of_commRing Λ cs)
  exact he.symm

/-- The unbounded comparison isomorphisms `L(-^*) ν^* ≅ ν^* L(-^*)` commute with the étale and
the pro-étale derived square isomorphisms of a Cartesian square. -/
theorem leftDerivedUpperStarComparisonIsoUnbounded_square
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g)
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D(ν^*(X')[ModuleCat.{u + 1} Λ]).map
        ((Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app M) ≫
      (leftDerivedUpperStarComparisonIsoUnbounded Λ g').hom.app
        (L(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
        ((leftDerivedUpperStarComparisonIsoUnbounded Λ f).hom.app M) =
    (leftDerivedUpperStarComparisonIsoUnbounded Λ f').hom.app
        (L(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f').map
        ((leftDerivedUpperStarComparisonIsoUnbounded Λ g).hom.app M) ≫
      (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app
        (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj M) := by
  let cs : ChosenCartesianSquare g' f' f g :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  have hcube := Functor.mapDerivedCategorySquareIso_cube
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f').symm
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g').symm
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) f' g).symm ≪≫
      eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm) ≪≫
      Etale.upperStarComp (ModuleCat.{u + 1} Λ) g' f)
    ((ProEtale.upperStarComp (ModuleCat.{u + 1} Λ) f' g).symm ≪≫
      eqToIso (congrArg (ProEtale.upperStar (ModuleCat.{u + 1} Λ)) sq.w.symm) ≪≫
      ProEtale.upperStarComp (ModuleCat.{u + 1} Λ) g' f)
    (comparisonUpperStarCompUpperStarIso_square Λ sq)
  have h := cube_conjugation
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f')
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g')
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f')
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g')
    _ _ _ _ _ _ (fun M ↦ hcube M) M
  rw [Etale.derivedSquareUpperStarIso_eq_mapDerivedCategorySquareIso,
    leftDerivedUpperStarSquareIso_eq_mapDerivedCategorySquareIso]
  exact h

/-- **Transport of the unbounded exchange map along the site comparison.** For a Cartesian
square
```
  X' ──g'──▶ X
  │          │
  f'         f
  ▼          ▼
  Y' ──g───▶ Y
```
and `L ∈ D(X_ét, Λ)`, conjugating the étale exchange map `Lg^* Rf_* L ⟶ Rf'_* Lg'^* L` by the
comparison maps `ν_{Y'}^* Lg^* Rf_* L ≅ Lg^* ν_Y^* Rf_* L ⟶ Lg^* Rf_* ν_X^* L` and
`ν_{Y'}^* Rf'_* Lg'^* L ⟶ Rf'_* ν_{X'}^* Lg'^* L ≅ Rf'_* Lg'^* ν_X^* L` (built from
`AlgebraicGeometry.ProEtale.unboundedDirectImageComparisonMap` and
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarComparisonIsoUnbounded`) gives the pro-étale
exchange map at `ν_X^* L`. -/
theorem comparison_derivedBaseChangeMap_unbounded
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D(ν^*(Y')[ModuleCat.{u + 1} Λ]).map
        ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app L) ≫
      unboundedDirectImageComparisonMap Λ f'
        (L(Etale.upperStar (ModuleCat.{u + 1} Λ) g').obj L) ≫
      R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f').map
        ((leftDerivedUpperStarComparisonIsoUnbounded Λ g').hom.app L) =
    (leftDerivedUpperStarComparisonIsoUnbounded Λ g).hom.app
        (R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj L) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).map
        (unboundedDirectImageComparisonMap Λ f L) ≫
      (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj L) :=
  mateEquiv_app_comparison_transport
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f')
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f')
    (leftDerivedUpperStarComparisonIsoUnbounded Λ f)
    (leftDerivedUpperStarComparisonIsoUnbounded Λ f')
    (leftDerivedUpperStarComparisonIsoUnbounded Λ g)
    (leftDerivedUpperStarComparisonIsoUnbounded Λ g')
    (unboundedDirectImageComparisonMap Λ f) (unboundedDirectImageComparisonMap Λ f')
    (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom
    (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom
    (leftDerivedUpperStarComparisonIsoUnbounded_counit Λ f)
    (leftDerivedUpperStarComparisonIsoUnbounded_counit Λ f')
    (leftDerivedUpperStarComparisonIsoUnbounded_square Λ sq) L

/-- For a Cartesian square of schemes and `L ∈ D(X_ét, Λ)`, the pro-étale exchange map
`Lg^* Rf_* ν_X^* L ⟶ Rf'_* Lg'^* ν_X^* L` is an isomorphism as soon as the étale exchange map
`Lg^* Rf_* L ⟶ Rf'_* Lg'^* L` is, and the unbounded direct image comparison maps
`ν_Y^* Rf_* L ⟶ Rf_* ν_X^* L` and `ν_{Y'}^* Rf'_* Lg'^* L ⟶ Rf'_* ν_{X'}^* Lg'^* L` are
isomorphisms. -/
theorem isIso_derivedBaseChangeMap_app_comparisonUpperStar
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hL : IsIso ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app L))
    (hf : IsIso (unboundedDirectImageComparisonMap Λ f L))
    (hf' : IsIso (unboundedDirectImageComparisonMap Λ f'
      (L(Etale.upperStar (ModuleCat.{u + 1} Λ) g').obj L))) :
    IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L)) := by
  have h := comparison_derivedBaseChangeMap_unbounded Λ sq L
  have : IsIso ((leftDerivedUpperStarComparisonIsoUnbounded Λ g).hom.app
        (R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj L) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).map
        (unboundedDirectImageComparisonMap Λ f L) ≫
      (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj L)) := by
    rw [← h]
    infer_instance
  rw [← Category.assoc] at this
  exact IsIso.of_isIso_comp_left ((leftDerivedUpperStarComparisonIsoUnbounded Λ g).hom.app
    (R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj L) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).map
        (unboundedDirectImageComparisonMap Λ f L)) _

end AlgebraicGeometry.ProEtale
