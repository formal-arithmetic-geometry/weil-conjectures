/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.DirectImageStalk

/-!
# Stalks of pullbacks and stalks on the point

The stalk of the pullback `φ^* F` of a Weil sheaf at a closed point `y` is the stalk of `F` at
`φ y` when the two points have the same degree over `k₀`, with the same local Frobenius
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_upperStar`). On the point `Spec k₀` the stalk
at the unique point is the space of global sections with its Frobenius
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_globalSections`): the geometric fibre of
`Spec k₀` is `Spec k̄` itself, so the restriction of global sections to the stalk is bijective.
Together they compute the stalk of a Weil sheaf at a `k₀`-rational point as the global sections
of its pullback to the point.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilCoefficients

variable {l : ℕ} [Fact l.Prime]

/-- The Frobenius module `(A, e)` of a finite-dimensional `ℚ̄_ℓ`-module `A` with an automorphism
`e`. -/
noncomputable def frobeniusModule (A : WeilCoefficients.{u} l)
    [FiniteDimensional (PadicAlgCl l) ((toModuleCat l).obj A)] (e : A ≅ A) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) where
  carrier := (toModuleCat l).obj A
  frobenius := linearEquivOfIso e

/-- An isomorphism `g : A ≅ B` intertwining automorphisms `e_A`, `e_B` is an isomorphism of the
Frobenius modules `(A, e_A) ≅ (B, e_B)`. -/
theorem nonempty_equiv_frobeniusModule {A B : WeilCoefficients.{u} l}
    [FiniteDimensional (PadicAlgCl l) ((toModuleCat l).obj A)]
    [FiniteDimensional (PadicAlgCl l) ((toModuleCat l).obj B)]
    (eA : A ≅ A) (eB : B ≅ B) (g : A ⟶ B) [IsIso g] (h : g ≫ eB.hom = eA.hom ≫ g) :
    Nonempty ((frobeniusModule A eA).Equiv (frobeniusModule B eB)) :=
  ⟨⟨linearEquivOfIso (asIso g), fun x ↦ by
    change ((toModuleCat l).map g).hom (((toModuleCat l).map eA.hom).hom x) =
      ((toModuleCat l).map eB.hom).hom (((toModuleCat l).map g).hom x)
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, h]⟩⟩

end WeilCoefficients

namespace WeilSheaf

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The stalk of a pullback.** For a morphism `φ : X ⟶ Y` of `k₀`-schemes, a Weil sheaf `F` on
`Y` and closed points `y` of `X` and `x = φ y` of `Y` of the same degree over `k₀`, the stalk of
`F` at `x` is the stalk of `φ^* F` at `y`, Frobenius-equivariantly. -/
theorem nonempty_equiv_stalk_upperStar {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l Y) (y : X.finitePoints) (x : Y.finitePoints) (hxy : φ.base y.1 = x.1)
    (hdeg : (X ↘ Spec (CommRingCat.of k₀)).degreeOver y.1 =
      (Y ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) :
    Nonempty ((F.stalk x).Equiv (((upperStar φ).obj F).stalk y)) := by
  have hφ := comp_over φ (Spec (CommRingCat.of k₀))
  set s := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint y
  have ht := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) y
  have ht' : (s ≫ Scheme.Hom.geometricFiberMap φ hφ) ≫
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (X ↘ Spec (CommRingCat.of k₀)).degreeOver y.1).hom =
      (specGeometricFrobenius k₀ ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver y.1).hom ≫
        (s ≫ Scheme.Hom.geometricFiberMap φ hφ) := by
    rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow,
      ← Category.assoc, ht, Category.assoc]
  have ht'' : (s ≫ Scheme.Hom.geometricFiberMap φ hφ) ≫
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (Y ↘ Spec (CommRingCat.of k₀)).degreeOver x.1).hom =
      (specGeometricFrobenius k₀ ^ (Y ↘ Spec (CommRingCat.of k₀)).degreeOver x.1).hom ≫
        (s ≫ Scheme.Hom.geometricFiberMap φ hφ) := hdeg ▸ ht'
  -- the stalk of `φ^* F` at `y` is the stalk of `F` at `s ≫ φ̄`
  have : IsIso (𝟙 _ : (Scheme.Hom.geometricFiberMap φ hφ)^*[WeilCoefficients.{u} l].obj
      F.obj.carrier.X ⟶ ((upperStar φ).obj F).obj.carrier.X) :=
    inferInstanceAs (IsIso (𝟙 ((Scheme.Hom.geometricFiberMap φ hφ)^*[WeilCoefficients.{u} l].obj
      F.obj.carrier.X)))
  obtain ⟨e₂⟩ := nonempty_equiv_stalkAt_of_upperStar (G := (upperStar φ).obj F)
    (θ := 𝟙 _) (upperStar_frobeniusStr_compatible (φ := φ) F) s _ ht ht'
  -- the geometric points over `x`: the chosen one and `s ≫ φ̄`
  have hx₁ := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base
    (Y ↘ Spec (CommRingCat.of k₀)) x
  have hss' : ((Y ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x ≫
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      ((s ≫ Scheme.Hom.geometricFiberMap φ hφ) ≫
        (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
          (IsLocalRing.closedPoint (AlgebraicClosure k₀)) := by
    rw [hx₁, Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Category.assoc, Scheme.Hom.comp_base, TopCat.comp_app,
      Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base, hxy]
  obtain ⟨e₃⟩ := F.nonempty_equiv_stalkAt _ _ hss' (hx₁ ▸ x.2) _
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
      (Y ↘ Spec (CommRingCat.of k₀)) x) ht''
  obtain ⟨e₄⟩ := F.nonempty_equiv_stalkAt_of_eq _ hdeg.symm ht'' ht'
  exact ⟨(e₃.trans e₄).trans e₂⟩

/-- The restriction `Γ(X̄, F) ⟶ F_s` of global sections to the stalk at a geometric point `s`
which is an isomorphism `Spec k̄ ≅ X̄` is bijective: the unit `F ⟶ s_* s^* F` is an isomorphism,
`s_*` being an equivalence. -/
instance isIso_globalSectionsToStalkObj {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l X)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    [IsIso s] : IsIso (F.globalSectionsToStalkObj s) := by
  have : (s)_*[WeilCoefficients.{u} l].IsEquivalence :=
    (ProEtale.lowerStarEquivalence (WeilCoefficients.{u} l) (asIso s)).isEquivalence_functor
  have : IsIso ((ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) s).unit.app
      F.obj.carrier.X) :=
    (Adjunction.isIso_unit_app_iff_mem_essImage _).2 (Functor.EssSurj.mem_essImage _ _)
  unfold globalSectionsToStalkObj
  infer_instance

/-- **The stalk on the point is the space of global sections.** For a geometric point `s` of a
`k₀`-scheme which is an isomorphism `Spec k̄ ≅ X̄` (as for `X = Spec k₀`) and is fixed by the
Frobenius, the restriction of global sections to the stalk at `s` is an isomorphism of Frobenius
modules `Γ(X̄, F) ≅ F_s`. -/
theorem nonempty_equiv_globalSections_stalkAt {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    [IsIso s] (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).hom =
      (specGeometricFrobenius k₀ ^ 1).hom ≫ s) :
    Nonempty (F.globalSections.Equiv (F.stalkAt s 1 hs)) :=
  have := F.finiteDimensional_globalSections
  have := F.finiteDimensional_stalkObj s
  WeilCoefficients.nonempty_equiv_frobeniusModule (A := (Sheaf.Γ _ _).obj F.obj.carrier.X)
    (B := F.stalkObj s) _ _ _ (globalSectionsToStalkObj_comp_stalkAt_iso F s hs)

end WeilSheaf

end AlgebraicGeometry
