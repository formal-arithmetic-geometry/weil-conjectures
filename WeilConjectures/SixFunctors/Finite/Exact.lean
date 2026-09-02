/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Finite.Stalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePointAlgClosure
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!

# Exactness of the direct image along a finite morphism

For a finite morphism `f : X ⟶ Y`, the pushforward `f_*` on étale sheaves is exact
(`AlgebraicGeometry.Etale.preservesFiniteColimits_lowerStar_of_isFinite`): it is left exact
for any morphism, and it preserves epimorphisms because on the stalk at a geometric point `y`
with algebraically closed residue field it is the finite product of the stalk maps at the
geometric points over `y` (`AlgebraicGeometry.Etale.lowerStarSheafFiberIsoPi`), and these
stalks jointly detect epimorphisms
(`AlgebraicGeometry.Scheme.epi_of_forall_epi_sheafFiber_map_algClosurePoint`).

Consequently the total right derived functor of `f_*` is `f_*` applied levelwise
(`AlgebraicGeometry.Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory`); in particular
`R^q f_* = 0` for `q > 0`.

Besides the standing assumptions on the coefficient category `A`, the results need `A` to be
concrete over `Type (u + 1)` in a way compatible with filtered colimits and sheafification,
since that is what the conservativity of the geometric points asks for. This holds for
`A = ModuleCat.{u + 1} Λ`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry

open Scheme Etale Scheme.Hom

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  [hJ : Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- A morphism of sheaves whose image under each factor of a product of functors is an
epimorphism has epimorphic image under the product, for a finite product of functors into an
abelian category. -/
lemma Etale.epi_pi_map {D : Type*} [Category D] {ι : Type u} [Finite ι]
    (F : ι → (D ⥤ A)) {P Q : D} (φ : P ⟶ Q) [∀ t, Epi ((F t).map φ)] : Epi ((∏ᶜ F).map φ) := by
  have h : (∏ᶜ F).map φ = (piObjIso F P).hom ≫ Limits.Pi.map (fun t ↦ (F t).map φ) ≫
      (piObjIso F Q).inv := by
    rw [← cancel_mono (piObjIso F Q).hom]
    apply Pi.hom_ext
    intro t
    simp only [Category.assoc, piObjIso_hom_comp_π, piObjIso_inv_comp_π, Limits.Pi.map_π,
      piObjIso_hom_comp_π_assoc]
    exact NatTrans.naturality _ _
  rw [h]
  have : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  infer_instance

include hJ in
/-- **The direct image along a finite morphism preserves epimorphisms.** On the stalk at a
geometric point with algebraically closed residue field, `f_* φ` is the finite product of the
stalk maps of `φ` at the geometric points of `X` over it. -/
instance Etale.preservesEpimorphisms_lowerStar_of_isFinite :
    (f)_*[A].PreservesEpimorphisms where
  preserves {G G'} φ _ := by
    refine Scheme.epi_of_forall_epi_sheafFiber_map_algClosurePoint _ fun s ↦ ?_
    set y := Y.algClosurePoint s
    have h₁ : Epi (((f)_*[A] ⋙ (pointSmallEtale y).sheafFiber).map φ) := by
      rw [← NatIso.naturality_2 (Etale.lowerStarSheafFiberIsoPi A f y) φ]
      have : Epi ((∏ᶜ fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber).map φ) :=
        Etale.epi_pi_map A (fun t : GeometricFiber f y ↦ (pointSmallEtale t.1).sheafFiber) φ
      infer_instance
    have h₂ : Epi ((pointSmallEtale y).sheafFiber.map ((f)_*[A].map φ)) := h₁
    rw [← NatIso.naturality_2 ((pointSmallEtale y).uliftSheafFiberIso A) ((f)_*[A].map φ)]
    exact epi_comp _ _

include hJ in
/-- The direct image along a finite morphism preserves homology. -/
instance Etale.preservesHomology_lowerStar_of_isFinite : (f)_*[A].PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

include hJ in
/-- **The direct image along a finite morphism is exact** (blueprint:
`lemma:weil-pbc-finite-direct-image-exact`): it preserves finite colimits, and it preserves
finite limits by `AlgebraicGeometry.Etale.preservesFiniteLimits_lowerStar`. -/
instance Etale.preservesFiniteColimits_lowerStar_of_isFinite :
    PreservesFiniteColimits (f)_*[A] :=
  Functor.preservesFiniteColimits_of_preservesHomology _

section Derived

variable [HasDerivedCategory (Sheaf X.smallEtaleTopology A)]
  [HasDerivedCategory (Sheaf Y.smallEtaleTopology A)]
  [Abelian.HasKInjectiveResolutions (Sheaf X.smallEtaleTopology A)]

include hJ in
/-- **The right derived functor of a finite direct image is the direct image itself**: since
`f_*` is exact, its total right derived functor is `f_*` applied levelwise to complexes. In
particular `R^q f_* = 0` for `q > 0`. -/
def Etale.rightDerivedFunctorLowerStarIsoMapDerivedCategory :
    (f)_*[A].rightDerivedFunctor ≅ (f)_*[A].mapDerivedCategory :=
  (f)_*[A].rightDerivedFunctorIsoMapDerivedCategory

end Derived

end AlgebraicGeometry

end
