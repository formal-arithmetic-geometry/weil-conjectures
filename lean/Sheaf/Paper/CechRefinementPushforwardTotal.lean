/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Paper.CechComplexAugmentations
public import Sheaf.Paper.CechRefinementCochainMap

/-! # Tuplewise refinement of the pushed-forward target resolution

Source: Stacks Project, Tag 01FD, the right upper square and augmentation pentagon.
(blueprint: lem-sc-cech-refinement-pushforward-total)
-/

@[expose] public section

universe v
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The adjunction unit followed by the pushed-forward resolution augmentation.
Source: Stacks 01FD (blueprint: lem-sc-cech-refinement-pushforward-total). -/
def cechPushforwardAugmentation {X X' : Scheme.{v}} (f : X' ⟶ X)
    (F : X.Modules) (I : InjectiveResolution ((tensorPullback f).obj F)) :
    F ⟶ (pushforward f).obj (I.cocomplex.X 0) :=
  ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F) ≫
    (pushforward f).map (I.ι.f 0)

/-- The pushed-forward augmentation is a cocycle.
Source: Stacks 01FD (blueprint: lem-sc-cech-refinement-pushforward-total). -/
theorem cechPushforwardAugmentation_d {X X' : Scheme.{v}} (f : X' ⟶ X)
    (F : X.Modules) (I : InjectiveResolution ((tensorPullback f).obj F)) :
    cechPushforwardAugmentation f F I ≫ (pushforward f).map (I.cocomplex.d 0 1) = 0 := by
  dsimp only [cechPushforwardAugmentation]
  rw [Category.assoc, ← Functor.map_comp]
  have h : I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0 := by simp
  rw [h, Functor.map_zero, comp_zero]

/-- Tuple restriction on the pushed-forward resolution preserves both augmentations.
This statement involves only the target resolution: there is no source resolution,
resolution lift, injective replacement, covering assumption, or inverse total map.
Source: Stacks Project, Tag 01FD, the map B-double-prime to A in the displayed diagram.
(blueprint: lem-sc-cech-refinement-pushforward-total)

Proof: In bidegree (r,q), send a tuple section of f_*I^r to its component indexed
by refine composed with the target tuple, then restrict it to the target intersection.
Pushforward evaluates on the inverse-image open, so this is a section of I^r on the
required intersection. Restrictions commute with I's differential and with all face
maps. The alternating face sums and the total signs are therefore preserved, giving
a cochain map between the forgotten module total complexes. Apply homology and
transport the two ends through the canonical forgetful homology isomorphisms to
obtain s. On the alpha summands (r,0), restrictions of global sections commute with
this map. The given component formula for a.inv identifies the source global
sections with those on X', proving the first equality. On beta summands (0,q),
naturality of I's augmentation moves it past the restrictions. The remaining tuple
formula is hgamma, proving the second equality. This needs no cover on either side;
empty families give zero tuple products, and the same formulas apply in degree zero.
-/
theorem exists_cechRefinement_pushforward_total
    {X X' : Scheme.{v}} (f : X' ⟶ X) {ι ι' : Type v}
    (U : ι → X.Opens) (U' : ι' → X'.Opens)
    (refine : ι' → ι) (hrefine : ∀ i, U' i ≤ f ⁻¹ᵁ U (refine i))
    (F : X.Modules) (I : InjectiveResolution ((tensorPullback f).obj F)) (p : ℕ)
    (gamma : ((forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj F.presheafModuleCat) ⟶
      ((forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          ((cechComplexFunctor U').obj ((tensorPullback f).obj F).presheafModuleCat))
    (hgamma : IsCechRefinementMap f U U' refine hrefine F gamma)
    (a : ((RingedSpace.globalSectionsFunctor X'.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex ≅
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        forget₂ _ AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex))
    (ha : ∀ n : ℕ, a.inv.f n = (Scheme.Modules.presheaf (I.cocomplex.X n)).map
      (eqToHom (by simp) : (⊤ : X'.Opens) ⟶ f ⁻¹ᵁ (⊤ : X.Opens)).op) :
    let P := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let e := forget₂ (ModuleCat.{v} Γ(X, ⊤)) AddCommGrpCat.{v}
    let e' := forget₂ (ModuleCat.{v} Γ(X', ⊤)) AddCommGrpCat.{v}
    let S := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)
    ∃ s : e.obj (((moduleCechTotalFunctor U).obj P).homology p) ⟶
        e'.obj (((moduleCechDouble U' I).total (ComplexShape.up ℕ)).homology p),
      e.map (HomologicalComplex.homologyMap (moduleCechComplexAlpha U P) p) ≫ s =
        (((S.obj P).sc p).mapHomologyIso e).inv ≫
          HomologicalComplex.homologyMap a.inv p ≫
          (((RingedSpace.globalSectionsComplex I).sc p).mapHomologyIso e').hom ≫
          e'.map (HomologicalComplex.homologyMap (moduleCechAlpha U' I) p) ∧
      e.map (HomologicalComplex.homologyMap
          (moduleCechComplexBeta U P (cechPushforwardAugmentation f F I)
            (cechPushforwardAugmentation_d f F I)) p) ≫ s =
        cechRefinementHomology gamma p ≫
          e'.map (HomologicalComplex.homologyMap (moduleCechBeta U' I) p) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
