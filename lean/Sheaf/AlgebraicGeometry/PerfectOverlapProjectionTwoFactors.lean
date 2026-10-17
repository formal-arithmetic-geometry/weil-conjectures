/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase
public import Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle
import Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositeAbstract
/-! # Naturality before the cartesian projection prism -/
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
/-- Precompose the projection prism by two arbitrary coefficient maps.
Source: Stacks Project, Tag 0D5S. Apply the projection prism, then use naturality
of cartesian transport twice. No open restriction or local composition is involved.
(blueprint: lem-pc-perfect-overlap-projection-two-factors). -/
theorem perfectOverlapProjectionTwoFactors
    {X K W S Z C T : Scheme.{u}} (s : W ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S) (l : Over.mk b ⟶ Over.mk q)
    (r : X ⟶ K) (eX : X ≅ pullback s b)
    (eK : K ≅ pullback s q)
    (hmap : eX.inv ≫ r = baseChangeMap s l ≫ eK.inv)
    (p : K ⟶ Z) (t : X ⟶ Z) (hr : r ≫ p = t) (a : W ⟶ Z)
    (ht : eX.inv ≫ t = pullback.fst s b ≫ a)
    (hp : eK.inv ≫ p = pullback.fst s q ≫ a)
    (M : schemeDerivedCategory Z) {N₀ N₁ : schemeDerivedCategory K}
    (d₁ : N₀ ⟶ N₁) (d₂ : N₁ ⟶ (derivedPullback p).obj M) :
    (derivedPullback eX.inv).map ((derivedPullback r).map d₁) ≫
      (derivedPullback eX.inv).map ((derivedPullback r).map d₂) ≫
      (derivedPullback eX.inv).map ((compositionTo r p t hr).hom.app M) ≫
      (perfectHomComposition eX.inv t).hom.app M ≫
      (eqToIso (congrArg (fun k ↦ derivedPullback k) ht)).hom.app M ≫
      (perfectHomComposition (pullback.fst s b) a).inv.app M ≫
      (perfectHomComparison s l).hom.app ((derivedPullback a).obj M) =
    (perfectOverlapDerivedPullbackTransport r eX eK (baseChangeMap s l) hmap).hom.app N₀ ≫
      (derivedPullback (baseChangeMap s l)).map ((derivedPullback eK.inv).map d₁) ≫
      (derivedPullback (baseChangeMap s l)).map ((derivedPullback eK.inv).map d₂) ≫
      (derivedPullback (baseChangeMap s l)).map
        ((perfectHomComposition eK.inv p).hom.app M) ≫
      (derivedPullback (baseChangeMap s l)).map
        ((eqToIso (congrArg (fun k ↦ derivedPullback k) hp)).hom.app M) ≫
      (derivedPullback (baseChangeMap s l)).map
        ((perfectHomComposition (pullback.fst s q) a).inv.app M) := by
  have H := perfectOverlapProjectionCompositeAbstract s l r eX eK hmap p t hr a ht hp M
  simp only [Over.mk_hom] at H
  have h₁ := (perfectOverlapDerivedPullbackTransport r eX eK
    (baseChangeMap s l) hmap).hom.naturality d₁
  have h₂ := (perfectOverlapDerivedPullbackTransport r eX eK
    (baseChangeMap s l) hmap).hom.naturality d₂
  simp only [Functor.comp_map] at h₁ h₂
  rw [H, reassoc_of% h₂, reassoc_of% h₁]
end AlgebraicGeometry
