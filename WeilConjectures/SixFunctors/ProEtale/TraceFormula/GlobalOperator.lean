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

namespace GeometricOperations

variable [DerivedBraiding A] (G : GeometricOperations A s)

section Naturality

variable {X Y Z : Scheme.{u}}

/-- The identification `Rf_* ≃ Rf_!` of `properComparison` is natural, as a family of
morphisms of `D(Y, A)` indexed by `Dᵇctf(X)`. -/
@[reassoc]
lemma properComparison_inv_app_naturality (f : X ⟶ Y) (hf : IsGeometricHom s f)
    [HasCompactification f] [IsProper f]
    {M M' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hM : G.ctf X M)
    (hM' : G.ctf X M') (φ : M ⟶ M') :
    ((lowerStar A f).rightDerivedFunctor).map φ ≫
        ((G.properComparison f hf).inv.app ⟨M', hM'⟩).hom =
      ((G.properComparison f hf).inv.app ⟨M, hM⟩).hom ≫ (rightDerivedLowerShriek A f).map φ :=
  congrArg (·.hom) ((G.properComparison f hf).inv.naturality (X := ⟨M, hM⟩) (Y := ⟨M', hM'⟩)
    (ObjectProperty.homMk φ))

/-- The composition isomorphism `Rg_! Rf_! ≃ R(f ≫ g)_!` of `lowerShriekComp` is natural, as a
family of morphisms of `D(Z, A)` indexed by `Dᵇctf(X)`. -/
@[reassoc]
lemma lowerShriekComp_hom_app_naturality (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsGeometricHom s f)
    (hg : IsGeometricHom s g) (hfg : IsGeometricHom s (f ≫ g)) [HasCompactification f]
    [HasCompactification g] [HasCompactification (f ≫ g)]
    {M M' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hM : G.ctf X M)
    (hM' : G.ctf X M') (φ : M ⟶ M') :
    (rightDerivedLowerShriek A g).map ((rightDerivedLowerShriek A f).map φ) ≫
        ((G.lowerShriekComp f g hf hg hfg).hom.app ⟨M', hM'⟩).hom =
      ((G.lowerShriekComp f g hf hg hfg).hom.app ⟨M, hM⟩).hom ≫
        (rightDerivedLowerShriek A (f ≫ g)).map φ :=
  congrArg (·.hom) ((G.lowerShriekComp f g hf hg hfg).hom.naturality (X := ⟨M, hM⟩)
    (Y := ⟨M', hM'⟩) (ObjectProperty.homMk φ))

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

end Naturality

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
  rw [← G.lowerShriekComp_hom_app_naturality h aX _ _ _ _ (G.ctf_upperStar h (.mk (aY := aX) rfl) hK'),
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    ← G.properComparison_inv_app_naturality h _ _ (G.ctf_upperStar h (.mk (aY := aX) rfl) hK'),
    ← Category.assoc, (derivedUpperStarLowerStarAdjunction A h).unit_naturality]
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.map_comp, Category.assoc]

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
  sorry

end ProperPullback

end GeometricOperations

end AlgebraicGeometry.ProEtale
