/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence

/-!
# Properties of the global operator

The global operator `T_c(u)` of an endocorrespondence `(C, c, u)` on `(X, K)` with proper
ordinary leg `c₂` (`AlgebraicGeometry.ProEtale.Correspondence.globalOperator`) is the composite
of the proper pullback `RΓ_c(X, K) ⟶ RΓ_c(C, Lc₂^* K)`, of `RΓ_c(C, u)` and of the exceptional
pushforward `RΓ_c(C, Rc₁^! K) ⟶ RΓ_c(X, K)`. We record the properties of this operator
(blueprint `sk-d-operator`).

## Main definitions

- `AlgebraicGeometry.ProEtale.GeometricOperations.properPullback`: the pullback
  `RΓ_c(X, K) ⟶ RΓ_c(X', Lh^* K)` along a proper morphism `h : X' ⟶ X`.
- `AlgebraicGeometry.ProEtale.GeometricOperations.exceptionalPushforward`: the pushforward
  `RΓ_c(C, Rf^! L) ⟶ RΓ_c(Y, L)` along a morphism `f : C ⟶ Y`.

## Main results

- `AlgebraicGeometry.ProEtale.Correspondence.globalOperator_naturality`: the global operator is
  natural in the pair `(u, K)` (blueprint `lem-trf-global-operator-naturality`).
- `AlgebraicGeometry.ProEtale.Correspondence.ctf_globalOperator`: every intermediate complex of
  the composite defining the global operator is compactly supported cohomology of an object of
  `Dᵇctf` (blueprint `lem-trf-global-operator-perfect`).
- `AlgebraicGeometry.ProEtale.Correspondence.globalOperator_ofGraph`,
  `AlgebraicGeometry.ProEtale.Correspondence.globalOperator_ofGraph_naturality`,
  `AlgebraicGeometry.ProEtale.Correspondence.globalOperator_ofGraph_comp`: the global operator of
  a graph correspondence `(1, h)` is the proper pullback along `h` followed by `RΓ_c(X, v)`; it
  is functorial in `(K, v)` and compatible with composition of proper endomorphisms
  (blueprint `prop-trf-graph-operator`).
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA] {s : Scheme.{u}}

/-- The transport `ctfLowerShriekCongr` of the exceptional direct image on `Dᵇctf` along an
equality of morphisms is the transport `rightDerivedLowerShriekCongr` on `D(X, A)`. -/
lemma ctfLowerShriekCongr_hom_app_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    [HasCompactification f] [HasCompactification g]
    (h₁ : ∀ K, DerivedCategory.constructibleFiniteTor A X K →
      DerivedCategory.constructibleFiniteTor A Y ((rightDerivedLowerShriek A f).obj K))
    (h₂ : ∀ K, DerivedCategory.constructibleFiniteTor A X K →
      DerivedCategory.constructibleFiniteTor A Y ((rightDerivedLowerShriek A g).obj K))
    (M : Ctf A X) :
    ((ctfLowerShriekCongr e h₁ h₂).hom.app M).hom =
      (rightDerivedLowerShriekCongr A e).hom.app M.obj := by
  subst e
  rfl

/-- The inverse of the transport `ctfLowerShriekCongr` is the inverse of the transport
`rightDerivedLowerShriekCongr` on `D(X, A)`. -/
lemma ctfLowerShriekCongr_inv_app_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    [HasCompactification f] [HasCompactification g]
    (h₁ : ∀ K, DerivedCategory.constructibleFiniteTor A X K →
      DerivedCategory.constructibleFiniteTor A Y ((rightDerivedLowerShriek A f).obj K))
    (h₂ : ∀ K, DerivedCategory.constructibleFiniteTor A X K →
      DerivedCategory.constructibleFiniteTor A Y ((rightDerivedLowerShriek A g).obj K))
    (M : Ctf A X) :
    ((ctfLowerShriekCongr e h₁ h₂).inv.app M).hom =
      (rightDerivedLowerShriekCongr A e).inv.app M.obj := by
  subst e
  rfl

namespace GeometricOperations

variable [DerivedBraiding A] (G : GeometricOperations A s)

section Naturality

variable {X Y Z : Scheme.{u}}

/-- The identification `Rf_* ≃ Rf_!` of `properComparison` is natural, as a family of
morphisms of `D(Y, A)` indexed by `Dᵇctf(X)`. -/
@[reassoc]
lemma properComparison_inv_app_naturality (f : X ⟶ Y) (hf : IsGeometricHom s f)
    [HasCompactification f] [IsProper f] {M M' : Ctf A X} (φ : M.obj ⟶ M'.obj) :
    ((lowerStar A f).rightDerivedFunctor).map φ ≫ ((G.properComparison f hf).inv.app M').hom =
      ((G.properComparison f hf).inv.app M).hom ≫ (rightDerivedLowerShriek A f).map φ :=
  congrArg (·.hom) ((G.properComparison f hf).inv.naturality (ObjectProperty.homMk φ))

/-- The composition isomorphism `Rg_! Rf_! ≃ R(f ≫ g)_!` of `lowerShriekComp` is natural, as a
family of morphisms of `D(Z, A)` indexed by `Dᵇctf(X)`. -/
@[reassoc]
lemma lowerShriekComp_hom_app_naturality (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsGeometricHom s f)
    (hg : IsGeometricHom s g) (hfg : IsGeometricHom s (f ≫ g)) [HasCompactification f]
    [HasCompactification g] [HasCompactification (f ≫ g)] {M M' : Ctf A X}
    (φ : M.obj ⟶ M'.obj) :
    (rightDerivedLowerShriek A g).map ((rightDerivedLowerShriek A f).map φ) ≫
        ((G.lowerShriekComp f g hf hg hfg).hom.app M').hom =
      ((G.lowerShriekComp f g hf hg hfg).hom.app M).hom ≫
        (rightDerivedLowerShriek A (f ≫ g)).map φ :=
  congrArg (·.hom) ((G.lowerShriekComp f g hf hg hfg).hom.naturality (ObjectProperty.homMk φ))

/-- The inverse `R(f ≫ g)_! ≃ Rg_! Rf_!` of `lowerShriekComp` is natural, as a family of
morphisms of `D(Z, A)` indexed by `Dᵇctf(X)`. -/
@[reassoc]
lemma lowerShriekComp_inv_app_naturality (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsGeometricHom s f)
    (hg : IsGeometricHom s g) (hfg : IsGeometricHom s (f ≫ g)) [HasCompactification f]
    [HasCompactification g] [HasCompactification (f ≫ g)] {M M' : Ctf A X}
    (φ : M.obj ⟶ M'.obj) :
    (rightDerivedLowerShriek A (f ≫ g)).map φ ≫
        ((G.lowerShriekComp f g hf hg hfg).inv.app M').hom =
      ((G.lowerShriekComp f g hf hg hfg).inv.app M).hom ≫
        (rightDerivedLowerShriek A g).map ((rightDerivedLowerShriek A f).map φ) :=
  congrArg (·.hom) ((G.lowerShriekComp f g hf hg hfg).inv.naturality (ObjectProperty.homMk φ))

/-- The counit `Rf_! Rf^! L ⟶ L` of the exceptional adjunction is natural in `L ∈ Dᵇctf(Y)`. -/
@[reassoc]
lemma exceptionalCounit_naturality (f : X ⟶ Y) (hf : IsGeometricHom s f)
    [HasCompactification f] {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : G.ctf Y L) (hL' : G.ctf Y L') (φ : L ⟶ L') :
    (rightDerivedLowerShriek A f).map ((rightDerivedUpperShriek A f).map φ) ≫
        G.exceptionalCounit f hf L' hL' =
      G.exceptionalCounit f hf L hL ≫ φ :=
  congrArg (·.hom) ((G.exceptionalAdjunction f hf).counit.naturality (X := ⟨L, hL⟩)
    (Y := ⟨L', hL'⟩) (ObjectProperty.homMk φ))

/-- The inverse form of the field `properComparison_comp`: for proper `f` and `g`, the
identification `R(f ≫ g)_* ≃ R(f ≫ g)_!` at `K ∈ Dᵇctf(X)` is the composite

```
  R(f ≫ g)_* K ≃ Rg_* Rf_* K ≃ Rg_! Rf_* K ≃ Rg_! Rf_! K ≃ R(f ≫ g)_! K.
``` -/
lemma properComparison_comp_inv_app_hom (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsGeometricHom s f)
    (hg : IsGeometricHom s g) (hfg : IsGeometricHom s (f ≫ g)) [HasCompactification f]
    [HasCompactification g] [HasCompactification (f ≫ g)] [IsProper f] [IsProper g]
    (K : Ctf A X) :
    ((G.properComparison (f ≫ g) hfg).inv.app K).hom =
      (conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction A (f ≫ g))
          ((derivedUpperStarLowerStarAdjunction A g).comp
            (derivedUpperStarLowerStarAdjunction A f))
          (leftDerivedUpperStarComp A f g).symm).hom.app K.obj ≫
        ((G.properComparison g hg).inv.app ((G.lowerStarCtf f hf).obj K)).hom ≫
        (rightDerivedLowerShriek A g).map ((G.properComparison f hf).inv.app K).hom ≫
        ((G.lowerShriekComp f g hf hg hfg).hom.app K).hom := by
  rw [← cancel_epi ((G.properComparison (f ≫ g) hfg).hom.app K).hom,
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app,
    G.properComparison_comp f g hf hg hfg]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have e₁ : ((G.properComparison g hg).hom.app ((G.lowerStarCtf f hf).obj K)).hom ≫
      ((G.properComparison g hg).inv.app ((G.lowerStarCtf f hf).obj K)).hom = 𝟙 _ := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app]
    rfl
  have e₂ : (rightDerivedLowerShriek A g).map ((G.properComparison f hf).hom.app K).hom ≫
      (rightDerivedLowerShriek A g).map ((G.properComparison f hf).inv.app K).hom = 𝟙 _ := by
    rw [← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id_app]
    exact CategoryTheory.Functor.map_id _ _
  have e₃ : ((G.lowerShriekComp f g hf hg hfg).inv.app K).hom ≫
      ((G.lowerShriekComp f g hf hg hfg).hom.app K).hom = 𝟙 _ := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app]
    rfl
  rw [reassoc_of% e₁, reassoc_of% e₂, e₃]
  rfl

end Naturality

/-- The unit of `L(f ≫ g)^* ⊣ R(f ≫ g)_*` is the composite of the units of `Lg^* ⊣ Rg_*` and
`Lf^* ⊣ Rf_*`, read through `L(f ≫ g)^* ≃ Lg^* ⋙ Lf^*` and its conjugate
`R(f ≫ g)_* ≃ Rf_* ⋙ Rg_*`. -/
lemma derivedUpperStarLowerStarAdjunction_comp_unit_app {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) :
    (derivedUpperStarLowerStarAdjunction A (f ≫ g)).unit.app K =
      (derivedUpperStarLowerStarAdjunction A g).unit.app K ≫
        ((lowerStar A g).rightDerivedFunctor).map
          ((derivedUpperStarLowerStarAdjunction A f).unit.app
            (((upperStar A g).leftDerivedFunctor).obj K)) ≫
        ((lowerStar A g).rightDerivedFunctor).map (((lowerStar A f).rightDerivedFunctor).map
          ((leftDerivedUpperStarComp A f g).inv.app K)) ≫
        (conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction A (f ≫ g))
          ((derivedUpperStarLowerStarAdjunction A g).comp
            (derivedUpperStarLowerStarAdjunction A f))
          (leftDerivedUpperStarComp A f g).symm).inv.app
            (((upperStar A (f ≫ g)).leftDerivedFunctor).obj K) := by
  rw [← cancel_mono ((conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction A (f ≫ g))
    ((derivedUpperStarLowerStarAdjunction A g).comp (derivedUpperStarLowerStarAdjunction A f))
    (leftDerivedUpperStarComp A f g).symm).hom.app _)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [conjugateIsoEquiv_apply_hom, unit_conjugateEquiv, Adjunction.comp_unit_app]
  simp

section ProperPullback

variable {X X' X'' : Scheme.{u}} {aX : X ⟶ s} {aX' : X' ⟶ s} {aX'' : X'' ⟶ s}
  [IsGeometric aX] [IsGeometric aX'] [IsGeometric aX''] [HasCompactification aX]
  [HasCompactification aX'] [HasCompactification aX'']

/-- The pullback `RΓ_c(X, K) ⟶ RΓ_c(X', Lh^* K)` along a proper morphism `h : X' ⟶ X` of
geometric schemes over `s`, for `K ∈ Dᵇctf(X)`: the composite

```
  Ra_{X!} K ──η──▶ Ra_{X!} Rh_* Lh^* K ≅ Ra_{X!} Rh_! Lh^* K ≅ R(h ≫ a_X)_! Lh^* K = Ra_{X'!} Lh^* K
```

of the unit of `Lh^* ⊣ Rh_*`, the proper identification `Rh_* = Rh_!` and the composition
`Ra_{X!} Rh_! ≃ R(h ≫ a_X)_!` (part of blueprint `def-trf-global-operator`). -/
noncomputable def properPullback (h : X' ⟶ X) [IsProper h] (hh : h ≫ aX = aX')
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : G.ctf X K) :
    (rightDerivedLowerShriek A aX).obj K ⟶
      (rightDerivedLowerShriek A aX').obj (((upperStar A h).leftDerivedFunctor).obj K) :=
  haveI : HasCompactification (h ≫ aX) := .of_eq hh.symm
  (rightDerivedLowerShriek A aX).map
      ((derivedUpperStarLowerStarAdjunction A h).unit.app K) ≫
    (rightDerivedLowerShriek A aX).map
      ((G.properComparison h (.mk hh)).inv.app ⟨_, G.ctf_upperStar h (.mk hh) hK⟩).hom ≫
    ((G.lowerShriekComp h aX (.mk hh) (.of_isGeometric aX)
      (.mk (aX := aX') (aY := 𝟙 s) (by rw [Category.comp_id, hh]))).hom.app
        ⟨_, G.ctf_upperStar h (.mk hh) hK⟩).hom ≫
    (rightDerivedLowerShriekCongr A hh).hom.app _

/-- The proper pullback is natural in `K ∈ Dᵇctf(X)`. -/
@[reassoc]
lemma properPullback_naturality (h : X' ⟶ X) [IsProper h] (hh : h ≫ aX = aX')
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : G.ctf X K)
    (hK' : G.ctf X K') (φ : K ⟶ K') :
    G.properPullback h hh hK ≫
        (rightDerivedLowerShriek A aX').map (((upperStar A h).leftDerivedFunctor).map φ) =
      (rightDerivedLowerShriek A aX).map φ ≫ G.properPullback h hh hK' := by
  subst hh
  simp only [properPullback, rightDerivedLowerShriekCongr_rfl, Iso.refl_hom, NatTrans.id_app,
    Category.assoc]
  erw [Category.id_comp, Category.comp_id]
  rw [← G.lowerShriekComp_hom_app_naturality h aX _ _ _
      (M' := ⟨_, G.ctf_upperStar h (.mk (aY := aX) rfl) hK'⟩),
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    ← G.properComparison_inv_app_naturality h _ (M' := ⟨_, G.ctf_upperStar h (.mk (aY := aX) rfl) hK'⟩),
    ← Category.assoc, (derivedUpperStarLowerStarAdjunction A h).unit_naturality]
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.map_comp, Category.assoc]

-- the composite of the two proper pullbacks is a long chain of morphisms between objects of
-- `Dᵇctf`, whose types are only defeq after unfolding the functors on `Dᵇctf`
set_option maxHeartbeats 400000 in
/-- The proper pullback is compatible with composition: for proper `h : X' ⟶ X` and
`h' : X'' ⟶ X'`, the pullback along `h' ≫ h` is the pullback along `h` followed by the
pullback along `h'`, read through `Lh'^* Lh^* K ≃ L(h' ≫ h)^* K`. -/
theorem properPullback_comp (h : X' ⟶ X) (h' : X'' ⟶ X') [IsProper h] [IsProper h']
    (hh : h ≫ aX = aX') (hh' : h' ≫ aX' = aX'')
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : G.ctf X K) :
    G.properPullback (h' ≫ h) (by rw [Category.assoc, hh, hh']) hK =
      G.properPullback h hh hK ≫ G.properPullback h' hh' (G.ctf_upperStar h (.mk hh) hK) ≫
        (rightDerivedLowerShriek A aX'').map (leftDerivedUpperStarCompIso h' rfl K).hom := by
  subst hh hh'
  simp only [properPullback, rightDerivedLowerShriekCongr_rfl, Iso.refl_hom, NatTrans.id_app,
    leftDerivedUpperStarCompIso, leftDerivedUpperStarCongr_rfl, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Category.assoc, Category.comp_id]
  erw [Category.comp_id, Category.id_comp, Category.id_comp]
  rw [← Functor.map_comp_assoc, derivedUpperStarLowerStarAdjunction_comp_unit_app,
    G.properComparison_comp_inv_app_hom h' h (.mk (aY := h ≫ aX) rfl) (.mk (aY := aX) rfl)]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have hN : G.ctf X'' (((upperStar A h').leftDerivedFunctor).obj
      (((upperStar A h).leftDerivedFunctor).obj K)) :=
    G.ctf_upperStar h' (.mk (aY := h ≫ aX) rfl) (G.ctf_upperStar h (.mk (aY := aX) rfl) hK)
  have hM : G.ctf X'' (((upperStar A (h' ≫ h)).leftDerivedFunctor).obj K) :=
    G.ctf_upperStar (h' ≫ h) (.mk (aY := aX) rfl) hK
  rw [G.properComparison_inv_app_naturality_assoc h (.mk (aY := aX) rfl)
      (M := (G.lowerStarCtf h' (.mk (aY := h ≫ aX) rfl)).obj ⟨_, hN⟩)
      (M' := (G.lowerStarCtf h' (.mk (aY := h ≫ aX) rfl)).obj ⟨_, hM⟩),
    ← Functor.map_comp_assoc (rightDerivedLowerShriek A h),
    G.properComparison_inv_app_naturality h' (.mk (aY := h ≫ aX) rfl) (M := ⟨_, hN⟩)
      (M' := ⟨_, hM⟩),
    Functor.map_comp_assoc (rightDerivedLowerShriek A h),
    G.lowerShriekComp_hom_app_naturality h' h _ _ _ (M := ⟨_, hN⟩) (M' := ⟨_, hM⟩)]
  simp only [Functor.map_comp, Category.assoc]
  haveI : HasCompactification ((h' ≫ h) ≫ aX) := .of_eq (Category.assoc _ _ _).symm
  rw [G.lowerShriekComp_hom_app_naturality (h' ≫ h) aX _ _ _ (M := ⟨_, hN⟩) (M' := ⟨_, hM⟩)]
  rw [reassoc_of% (G.lowerShriekComp_assoc h' h aX (.mk (aY := h ≫ aX) rfl) (.mk (aY := aX) rfl)
    (.of_isGeometric aX) (.mk (aY := aX) rfl) (.of_isGeometric (h ≫ aX))
    (.of_isGeometric (h' ≫ h ≫ aX)) (.mk (aX := h' ≫ h ≫ aX) (aY := 𝟙 s) (by simp))
    ⟨_, hN⟩)]
  rw [← G.lowerShriekComp_hom_app_naturality_assoc h aX _ _ _
      (M := ⟨_, G.ctf_upperStar h (.mk (aY := aX) rfl) hK⟩)
      (M' := (G.lowerStarCtf h' (.mk (aY := h ≫ aX) rfl)).obj ⟨_, hN⟩)
      ((derivedUpperStarLowerStarAdjunction A h').unit.app
        (((upperStar A h).leftDerivedFunctor).obj K))]
  rw [← G.lowerShriekComp_hom_app_naturality_assoc h aX _ _ _
      (M := (G.lowerStarCtf h' (.mk (aY := h ≫ aX) rfl)).obj ⟨_, hN⟩)
      (M' := (G.lowerShriekCtf h' (.mk (aY := h ≫ aX) rfl)).obj ⟨_, hN⟩)
      ((G.properComparison h' (.mk (aY := h ≫ aX) rfl)).inv.app ⟨_, hN⟩).hom]
  have e : (rightDerivedLowerShriek A aX).map (((lowerStar A h).rightDerivedFunctor).map
        ((derivedUpperStarLowerStarAdjunction A h').unit.app
          (((upperStar A h).leftDerivedFunctor).obj K))) ≫
      (rightDerivedLowerShriek A aX).map ((G.properComparison h (.mk (aY := aX) rfl)).inv.app
        ((G.lowerStarCtf h' (.mk (aY := h ≫ aX) rfl)).obj ⟨_, hN⟩)).hom =
      (rightDerivedLowerShriek A aX).map ((G.properComparison h (.mk (aY := aX) rfl)).inv.app
        ⟨_, G.ctf_upperStar h (.mk (aY := aX) rfl) hK⟩).hom ≫
      (rightDerivedLowerShriek A aX).map ((rightDerivedLowerShriek A h).map
        ((derivedUpperStarLowerStarAdjunction A h').unit.app
          (((upperStar A h).leftDerivedFunctor).obj K))) := by
    rw [← Functor.map_comp, ← Functor.map_comp, G.properComparison_inv_app_naturality h
      (.mk (aY := aX) rfl) (M := ⟨_, G.ctf_upperStar h (.mk (aY := aX) rfl) hK⟩)
      (M' := (G.lowerStarCtf h' (.mk (aY := h ≫ aX) rfl)).obj ⟨_, hN⟩)]
  rw [← reassoc_of% e]
  rw [ctfLowerShriekCongr_hom_app_hom]
  simp only [rightDerivedLowerShriekCongr_rfl, Iso.refl_hom, NatTrans.id_app]
  erw [Category.id_comp]
  rfl

end ProperPullback

section ExceptionalPushforward

variable {C Y : Scheme.{u}} {aC : C ⟶ s} {aY : Y ⟶ s} [IsGeometric aC] [IsGeometric aY]
  [HasCompactification aC] [HasCompactification aY]

/-- The pushforward `RΓ_c(C, Rf^! L) ⟶ RΓ_c(Y, L)` along a morphism `f : C ⟶ Y` of geometric
schemes over `s`, for `L ∈ Dᵇctf(Y)`: the composite

```
  Ra_{C!} Rf^! L = R(f ≫ a_Y)_! Rf^! L ≅ Ra_{Y!} Rf_! Rf^! L ──ε──▶ Ra_{Y!} L
```

of the composition `R(f ≫ a_Y)_! ≃ Ra_{Y!} Rf_!` and the counit of `Rf_! ⊣ Rf^!`
(part of blueprint `def-trf-global-operator`). -/
noncomputable def exceptionalPushforward (f : C ⟶ Y) [HasCompactification f] (hf : f ≫ aY = aC)
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)} (hL : G.ctf Y L) :
    (rightDerivedLowerShriek A aC).obj ((rightDerivedUpperShriek A f).obj L) ⟶
      (rightDerivedLowerShriek A aY).obj L :=
  haveI : HasCompactification (f ≫ aY) := .of_eq hf.symm
  (rightDerivedLowerShriekCongr A hf.symm).hom.app _ ≫
    ((G.lowerShriekComp f aY (.mk hf) (.of_isGeometric aY)
      (.mk (aX := aC) (aY := 𝟙 s) (by rw [Category.comp_id, hf]))).inv.app
        ⟨_, G.ctf_upperShriek f (.mk hf) hL⟩).hom ≫
    (rightDerivedLowerShriek A aY).map (G.exceptionalCounit f (.mk hf) L hL)

/-- The exceptional pushforward is natural in `L ∈ Dᵇctf(Y)`. -/
@[reassoc]
lemma exceptionalPushforward_naturality (f : C ⟶ Y) [HasCompactification f]
    (hf : f ≫ aY = aC) {L L' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}
    (hL : G.ctf Y L) (hL' : G.ctf Y L') (φ : L ⟶ L') :
    (rightDerivedLowerShriek A aC).map ((rightDerivedUpperShriek A f).map φ) ≫
        G.exceptionalPushforward f hf hL' =
      G.exceptionalPushforward f hf hL ≫ (rightDerivedLowerShriek A aY).map φ := by
  subst hf
  simp only [exceptionalPushforward, rightDerivedLowerShriekCongr_rfl, Iso.refl_hom,
    NatTrans.id_app]
  erw [Category.id_comp, Category.id_comp]
  rw [G.lowerShriekComp_inv_app_naturality_assoc f aY _ _ _
      (M := ⟨_, G.ctf_upperShriek f (.mk (aY := aY) rfl) hL⟩)
      (M' := ⟨_, G.ctf_upperShriek f (.mk (aY := aY) rfl) hL'⟩),
    ← Functor.map_comp, Category.assoc, ← Functor.map_comp, G.exceptionalCounit_naturality]

/-- For the identity `𝟙 X`, read through `K ≃ (𝟙 X)^! K`, the exceptional pushforward is the
transport `RΓ_c(X, K) ≃ RΓ_c(X, K)` along the two structure morphisms. -/
lemma exceptionalPushforward_id {aX : Y ⟶ s} [IsGeometric aX] [HasCompactification aX]
    {aX' : Y ⟶ s} [IsGeometric aX'] [HasCompactification aX'] (hf : 𝟙 Y ≫ aX = aX')
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)} (hK : G.ctf Y K) :
    (rightDerivedLowerShriek A aX').map (G.upperShriekIdIso Y (.mk hf) K hK).hom ≫
        G.exceptionalPushforward (𝟙 Y) hf hK =
      (rightDerivedLowerShriekCongr A (hf.symm.trans (Category.id_comp aX))).hom.app K := by
  subst hf
  have hY : IsGeometricHom s (𝟙 Y) := .mk (aY := aX) rfl
  have key : (G.upperShriekId Y hY).inv.app ⟨K, hK⟩ ≫
      (G.lowerShriekId Y hY).inv.app ((G.upperShriekCtf (𝟙 Y) hY).obj ⟨K, hK⟩) ≫
        (G.exceptionalAdjunction (𝟙 Y) hY).counit.app ⟨K, hK⟩ = 𝟙 _ := by
    have := conjugateEquiv_counit Adjunction.id (G.exceptionalAdjunction (𝟙 Y) hY)
      (G.lowerShriekId Y hY).hom ⟨K, hK⟩
    have nat := (G.lowerShriekId Y hY).inv.naturality
      ((conjugateEquiv Adjunction.id (G.exceptionalAdjunction (𝟙 Y) hY)
        (G.lowerShriekId Y hY).hom).app ⟨K, hK⟩)
    rw [upperShriekId, Iso.symm_inv, conjugateIsoEquiv_apply_hom, ← Category.assoc]
    erw [nat]
    rw [Category.assoc, this]
    simp
  simp only [exceptionalPushforward, rightDerivedLowerShriekCongr_rfl, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp, G.lowerShriekComp_id_left]
  simp only [Iso.trans_inv, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    ctfLowerShriekCongr_inv_app_hom, Functor.leftUnitor_inv_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, ObjectProperty.lift_map, ObjectProperty.homMk_hom, Functor.comp_map,
    ObjectProperty.ι_map, Category.assoc, Category.id_comp]
  have keyD : (G.upperShriekIdIso Y hY K hK).hom ≫
      ((G.lowerShriekId Y hY).inv.app ⟨_, G.ctf_upperShriek (𝟙 Y) hY hK⟩).hom ≫
        G.exceptionalCounit (𝟙 Y) hY K hK = 𝟙 K :=
    congrArg (·.hom) key
  rw [(rightDerivedLowerShriekCongr A _).inv.naturality_assoc, ← Functor.map_comp,
    ← Functor.map_comp, keyD]
  simp
  rfl

end ExceptionalPushforward

end GeometricOperations

namespace Correspondence

variable [DerivedBraiding A] (G : GeometricOperations A s) {X Y : Scheme.{u}}
  {aX : X ⟶ s} {aY : Y ⟶ s}
  {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
  {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)}

/-- The first half of the global operator is the proper pullback along the ordinary leg. -/
lemma globalOperatorUnit_eq (c : Correspondence aX aY K L) (hK : G.ctf X K) [IsGeometric aX]
    [IsGeometric c.str] [HasCompactification aX] [IsProper c.snd] [HasCompactification c.str] :
    globalOperatorUnit G c hK = G.properPullback c.snd c.snd_comp hK :=
  rfl

/-- The second half of the global operator is the exceptional pushforward along the exceptional
leg. -/
lemma globalOperatorCounit_eq (c : Correspondence aX aY K L) (hL : G.ctf Y L) [IsGeometric aY]
    [IsGeometric c.str] [HasCompactification aY] [HasCompactification c.str] :
    globalOperatorCounit G c hL = G.exceptionalPushforward c.fst c.fst_comp hL :=
  rfl

variable [IsGeometric aX] [HasCompactification aX]

/-- Blueprint `lem-trf-global-operator-naturality`: the global operator `T_c(u)` is natural in
the pair `(u, K)`. A morphism `φ : K ⟶ K'` of `Dᵇctf(X)` together with a coefficient map
`u' : Lc₂^* K' ⟶ Rc₁^! K'` on the same support and legs, compatible with `u` along `φ`, induces
a commutative square

```
  RΓ_c(X, K) ──T_c(u)──▶ RΓ_c(X, K)
      │                     │
    RΓ_c(φ)               RΓ_c(φ)
      ▼                     ▼
  RΓ_c(X, K') ──T_c(u')──▶ RΓ_c(X, K')
``` -/
theorem globalOperator_naturality (c : Correspondence aX aX K K) [IsGeometric c.str]
    [IsProper c.snd] [HasCompactification c.str] (hK : G.ctf X K)
    {K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK' : G.ctf X K') (φ : K ⟶ K')
    (u' : ((upperStar A c.snd).leftDerivedFunctor).obj K' ⟶
      (rightDerivedUpperShriek A c.fst).obj K')
    (w : c.coeff ≫ (rightDerivedUpperShriek A c.fst).map φ =
      ((upperStar A c.snd).leftDerivedFunctor).map φ ≫ u') :
    globalOperator G c hK ≫ (rightDerivedLowerShriek A aX).map φ =
      (rightDerivedLowerShriek A aX).map φ ≫ globalOperator G { c with coeff := u' } hK' := by
  simp only [globalOperator, globalOperatorUnit_eq, globalOperatorCounit_eq, Category.assoc]
  rw [← G.exceptionalPushforward_naturality, ← Functor.map_comp_assoc, w,
    Functor.map_comp_assoc, G.properPullback_naturality_assoc]

/-- Blueprint `lem-trf-global-operator-perfect`: every intermediate complex of the composite
defining the global operator `T_c(u)` is compactly supported cohomology of an object of
`Dᵇctf`: the coefficient complexes `Lc₂^* K`, `Rc₂_* Lc₂^* K`, `Rc₂_! Lc₂^* K`, `Rc₁^! K` and
`Rc₁_! Rc₁^! K` all lie in `Dᵇctf`. -/
theorem ctf_globalOperator (c : Correspondence aX aX K K) [IsGeometric c.str] [IsProper c.snd]
    (hK : G.ctf X K) :
    G.ctf c.supp (((upperStar A c.snd).leftDerivedFunctor).obj K) ∧
      G.ctf X (((lowerStar A c.snd).rightDerivedFunctor).obj
        (((upperStar A c.snd).leftDerivedFunctor).obj K)) ∧
      G.ctf X ((rightDerivedLowerShriek A c.snd).obj
        (((upperStar A c.snd).leftDerivedFunctor).obj K)) ∧
      G.ctf c.supp ((rightDerivedUpperShriek A c.fst).obj K) ∧
      G.ctf X ((rightDerivedLowerShriek A c.fst).obj ((rightDerivedUpperShriek A c.fst).obj K)) :=
  have h₂ : IsGeometricHom s c.snd := .mk c.snd_comp
  have h₁ : IsGeometricHom s c.fst := .mk c.fst_comp
  ⟨G.ctf_upperStar _ h₂ hK, G.ctf_lowerStar _ h₂ (G.ctf_upperStar _ h₂ hK),
    G.ctf_lowerShriek _ h₂ (G.ctf_upperStar _ h₂ hK), G.ctf_upperShriek _ h₁ hK,
    G.ctf_lowerShriek _ h₁ (G.ctf_upperShriek _ h₁ hK)⟩

variable (hK : G.ctf X K)

/-- The ordinary-pullback leg of `ofGraph G aX K hK g hg v` is `g`, proper when `g` is. -/
instance isProper_snd_ofGraph (g : X ⟶ X) (hg : g ≫ aX = aX) [IsProper g]
    (v : ((upperStar A g).leftDerivedFunctor).obj K ⟶ K) :
    IsProper (ofGraph G aX K hK g hg v).snd :=
  inferInstanceAs (IsProper g)

/-- Blueprint `prop-trf-graph-operator`: the global operator of the graph correspondence `(1, g)`
of a proper `s`-endomorphism `g : X ⟶ X` with coefficient map `v : Lg^* K ⟶ K` is the composite

```
  RΓ_c(X, K) ──g^*──▶ RΓ_c(X, Lg^* K) ──RΓ_c(v)──▶ RΓ_c(X, K)
```

of the proper pullback along `g` (the unit `K ⟶ Rg_* Lg^* K` read through `Rg_* = Rg_!`) and
`RΓ_c(X, v)`. -/
theorem globalOperator_ofGraph (g : X ⟶ X) (hg : g ≫ aX = aX) [IsProper g]
    (v : ((upperStar A g).leftDerivedFunctor).obj K ⟶ K) :
    globalOperator G (ofGraph G aX K hK g hg v) hK =
      G.properPullback g hg hK ≫ (rightDerivedLowerShriek A aX).map v := by
  simp only [globalOperator, globalOperatorUnit_eq, globalOperatorCounit_eq]
  change G.properPullback g hg hK ≫ (rightDerivedLowerShriek A aX).map
      (v ≫ (G.upperShriekIdIso X (.id aX) K hK).hom) ≫
      G.exceptionalPushforward (𝟙 X) (Category.id_comp aX) hK = _
  rw [Functor.map_comp_assoc, G.exceptionalPushforward_id]
  simp


/-- Blueprint `prop-trf-graph-operator`: the global operator of a graph correspondence is
functorial in `(K, v)`. A morphism `φ : K ⟶ K'` of `Dᵇctf(X)` compatible with the coefficient
maps `v : Lg^* K ⟶ K` and `v' : Lg^* K' ⟶ K'` intertwines the global operators. -/
theorem globalOperator_ofGraph_naturality (g : X ⟶ X) (hg : g ≫ aX = aX) [IsProper g]
    (v : ((upperStar A g).leftDerivedFunctor).obj K ⟶ K)
    {K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK' : G.ctf X K')
    (v' : ((upperStar A g).leftDerivedFunctor).obj K' ⟶ K') (φ : K ⟶ K')
    (w : ((upperStar A g).leftDerivedFunctor).map φ ≫ v' = v ≫ φ) :
    globalOperator G (ofGraph G aX K hK g hg v) hK ≫ (rightDerivedLowerShriek A aX).map φ =
      (rightDerivedLowerShriek A aX).map φ ≫ globalOperator G (ofGraph G aX K' hK' g hg v') hK' := by
  rw [globalOperator_ofGraph, globalOperator_ofGraph, Category.assoc, ← Functor.map_comp, ← w,
    Functor.map_comp, G.properPullback_naturality_assoc]

/-- Blueprint `prop-trf-graph-operator`: the global operator of graph correspondences is
compatible with composition of proper endomorphisms. For proper `s`-endomorphisms `g` and `h`
of `X` with coefficient maps `v_g : Lg^* K ⟶ K` and `v_h : Lh^* K ⟶ K`, the graph
correspondence of `h ≫ g` with the composite coefficient map

```
  L(h ≫ g)^* K ≃ Lh^* Lg^* K ──Lh^* v_g──▶ Lh^* K ──v_h──▶ K
```

has global operator `T(v_g)` followed by `T(v_h)`. -/
theorem globalOperator_ofGraph_comp (g h : X ⟶ X) (hg : g ≫ aX = aX) (hh : h ≫ aX = aX)
    [IsProper g] [IsProper h] (vg : ((upperStar A g).leftDerivedFunctor).obj K ⟶ K)
    (vh : ((upperStar A h).leftDerivedFunctor).obj K ⟶ K) :
    globalOperator G (ofGraph G aX K hK (h ≫ g) (by rw [Category.assoc, hg, hh])
        ((leftDerivedUpperStarCompIso h rfl K).inv ≫
          ((upperStar A h).leftDerivedFunctor).map vg ≫ vh)) hK =
      globalOperator G (ofGraph G aX K hK g hg vg) hK ≫
        globalOperator G (ofGraph G aX K hK h hh vh) hK := by
  rw [globalOperator_ofGraph, globalOperator_ofGraph, globalOperator_ofGraph,
    G.properPullback_comp g h hg hh hK, Category.assoc, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_assoc, Functor.map_comp, Category.assoc,
    ← G.properPullback_naturality_assoc]
end Correspondence

end AlgebraicGeometry.ProEtale
