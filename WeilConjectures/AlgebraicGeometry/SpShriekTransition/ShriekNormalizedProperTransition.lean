/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedTransitionData
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedPullTransition
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation

/-! # The normalized transition of one geometric operation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpShriekTransition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local irreducible] scalarCoordinates quotientMap
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

attribute [-instance] CategoryTheory.catToReflQuiver in
end AlgebraicGeometry.ProEtale.SpShriekTransition

namespace AlgebraicGeometry.ProEtale.SpShriekTransition

private theorem coordinate_naturality
    {A B : Type*} [categoryA : Category A] [categoryB : Category B]
    {S S' : A ⥤ B} (s : S ≅ S') {K L : A} {M N : B}
    (v : K ⟶ L) (w : M ⟶ N) (a : S.obj K ⟶ M) (b : S.obj L ⟶ N)
    (h : S.map v ≫ b = a ≫ w) :
    S'.map v ≫ coordinateReduction s b = coordinateReduction s a ≫ w := by
  dsimp only [coordinateReduction]
  rw [← Category.assoc, s.inv.naturality, Category.assoc, h, Category.assoc]

private theorem rho_naturality (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    {m n : ℕ} (h : m ≤ n) {M N : SpTowerShriek.D l E T} (v : M ⟶ N) :
    (scalarExtensionFunctor (quotientMap l E h) T).map
        ((SpTowerShriek.Ev l E T n).map v) ≫ rho l E b T h N =
      rho l E b T h M ≫ (SpTowerShriek.Ev l E T m).map v := by
  have result := coordinate_naturality
    (A := proEtaleDerivedCategory T (SpTowerShriek.R l E n))
    (B := proEtaleDerivedCategory T (SpTowerShriek.R l E m))
    (categoryA := @instCategoryDerivedCategory _ _ _ (HasDerivedCategory.standard _))
    (categoryB := @instCategoryDerivedCategory _ _ _ (HasDerivedCategory.standard _))
    (scalarCoordinates l E b T h) ((SpTowerShriek.Ev l E T n).map v)
    ((SpTowerShriek.Ev l E T m).map v)
    (SemilinearSections.reduction (ProEt.topology T) (SpTowerShriek.B l E T)
      (SpTowerShriek.tau l E T) h ((b.calculus T).scalar h) M)
    (SemilinearSections.reduction (ProEt.topology T) (SpTowerShriek.B l E T)
      (SpTowerShriek.tau l E T) h ((b.calculus T).scalar h) N)
    (SemilinearSections.reduction_naturality.{u + 1, u, u + 1}
      (ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
      h ((b.calculus T).scalar h) v)
  exact result

/-- Direct-image transition in the specified constant-ring coordinates.
Source: Zheng 4.10 and blueprint integral-adjunction direct-image paragraph (1).
Proof: the finite-unit normalization identifies the ordinary restriction/pullback
square with its canonical constant-ring presentation. The proved normalized inverse-image
transition localizes and scalar-transposes that square. Apply the lower finite geometric
adjunction to the desired equation. The finite counit evaluation equations, naturality of
rho and of the scalar/pullback isomorphism, and the defining counit equation of the mate
give directImageScalarComparison. No input transition is assumed invertible.
This works in ambient derived categories without flatness or Tor hypotheses.
(blueprint: lem-sp-normalized-proper-transition). -/
theorem normalized_proper_transition (b : SpTowerShriek.Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    {m n : ℕ} (h : m ≤ n) (M : SpTowerShriek.D l E X) :
    rho l E b Y h ((SpTowerShriek.push l E b g).obj M) ≫
        (g.pushEvaluation m).hom.app M =
      (scalarExtensionFunctor (quotientMap l E h) Y).map
          ((g.pushEvaluation n).hom.app M) ≫
        (directImageScalarComparison (quotientMap l E h) f).app
          ((SpTowerShriek.Ev l E X n).obj M) ≫
        (directImageConstantPush (SpTowerShriek.R l E m) f).map (rho l E b X h M) := by
  let V := proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E m) f
  let S := scalarExtensionFunctor (quotientMap l E h) X
  let P := (SpTowerShriek.push l E b g).obj M
  let aₙ := directImageConstantAdjunction (SpTowerShriek.R l E n) f
  let aₘ := directImageConstantAdjunction (SpTowerShriek.R l E m) f
  have hc (k : ℕ) :
      (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E k) f).map
          ((g.pushEvaluation k).hom.app M) ≫
        (directImageConstantAdjunction (SpTowerShriek.R l E k) f).counit.app
          ((SpTowerShriek.Ev l E X k).obj M) =
      (g.pullEvaluation k).inv.app ((SpTowerShriek.push l E b g).obj M) ≫
        (SpTowerShriek.Ev l E X k).map ((SpTowerShriek.adjunction l E b g).counit.app M) := by
    exact (SpTowerShriek.geometry_adjunction_evaluation l E b g k).2 M
  have hr : V.map (rho l E b Y h P) ≫ (g.pullEvaluation m).inv.app P =
      (directImageScalarPullbackIso (quotientMap l E h) f).hom.app
          ((SpTowerShriek.Ev l E Y n).obj P) ≫
        S.map ((g.pullEvaluation n).inv.app P) ≫
          rho l E b X h ((SpTowerShriek.pull l E b g).obj P) := by
    have : IsIso (S.map ((g.pullEvaluation n).hom.app P)) :=
      (S.mapIso ((g.pullEvaluation n).app P)).isIso_hom
    have : IsIso ((directImageScalarPullbackIso (quotientMap l E h) f).inv.app
        ((SpTowerShriek.Ev l E Y n).obj P)) :=
      ((directImageScalarPullbackIso (quotientMap l E h) f).symm.app _).isIso_hom
    apply (cancel_epi
      (S.map ((g.pullEvaluation n).hom.app P) ≫
        (directImageScalarPullbackIso (quotientMap l E h) f).inv.app
          ((SpTowerShriek.Ev l E Y n).obj P))).1
    simp only [Category.assoc]
    rw [← reassoc_of% (normalized_pull_transition l E b g h P)]
    simp only [Iso.inv_hom_id_app_assoc]
    have hi := (S.mapIso ((g.pullEvaluation n).app P)).hom_inv_id
    change S.map ((g.pullEvaluation n).hom.app P) ≫
      S.map ((g.pullEvaluation n).inv.app P) = 𝟙 _ at hi
    simp only [← Category.assoc, hi, Category.id_comp]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  apply (aₘ.homEquiv _ _).symm.injective
  change V.map _ ≫ aₘ.counit.app _ = V.map _ ≫ aₘ.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [V, aₘ]
  rw [hc m]
  rw [reassoc_of% hr]
  have hn := rho_naturality l E b X h
    (M := (SpTowerShriek.pull l E b g).obj P) (N := M)
    ((SpTowerShriek.adjunction l E b g).counit.app M)
  erw [← hn]
  have hcₙ := hc n
  change (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f).map
      ((g.pushEvaluation n).hom.app M) ≫ aₙ.counit.app _ =
    (g.pullEvaluation n).inv.app P ≫
      (SpTowerShriek.Ev l E X n).map
        ((SpTowerShriek.adjunction l E b g).counit.app M) at hcₙ
  rw [← S.map_comp_assoc, ← hcₙ, S.map_comp]
  have hq := (directImageScalarPullbackIso (quotientMap l E h) f).hom.naturality
    ((g.pushEvaluation n).hom.app M)
  change V.map ((scalarExtensionFunctor (quotientMap l E h) Y).map
      ((g.pushEvaluation n).hom.app M)) ≫
      (directImageScalarPullbackIso (quotientMap l E h) f).hom.app
        ((directImageConstantPush (SpTowerShriek.R l E n) f).obj
          ((SpTowerShriek.Ev l E X n).obj M)) =
    (directImageScalarPullbackIso (quotientMap l E h) f).hom.app
        ((SpTowerShriek.Ev l E Y n).obj P) ≫
      S.map ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f).map
        ((g.pushEvaluation n).hom.app M)) at hq
  simp only [Category.assoc]
  rw [← reassoc_of% hq]
  have he := aₘ.counit.naturality (rho l E b X h M)
  dsimp only [Functor.comp_map, Functor.id_map] at he
  rw [he]
  have hm : V.map ((directImageScalarComparison (quotientMap l E h) f).app
        ((SpTowerShriek.Ev l E X n).obj M)) ≫
      aₘ.counit.app ((scalarExtensionFunctor (quotientMap l E h) X).obj
        ((SpTowerShriek.Ev l E X n).obj M)) =
    (directImageScalarPullbackIso (quotientMap l E h) f).hom.app
        ((directImageConstantPush (SpTowerShriek.R l E n) f).obj
          ((SpTowerShriek.Ev l E X n).obj M)) ≫
      S.map (aₙ.counit.app ((SpTowerShriek.Ev l E X n).obj M)) := by
    exact mateEquiv_counit aₙ aₘ
      (TwoSquare.mk _ _ _ _ (directImageScalarPullbackIso (quotientMap l E h) f).hom)
      ((SpTowerShriek.Ev l E X n).obj M)
  rw [reassoc_of% hm]

end AlgebraicGeometry.ProEtale.SpShriekTransition
