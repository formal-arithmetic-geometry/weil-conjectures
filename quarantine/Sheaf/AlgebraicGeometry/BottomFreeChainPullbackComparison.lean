/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.AlgebraicGeometry.BottomFreeChainDerivedSquare
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Natural homology comparison for termwise free pullback

Source: Stacks Project, Tags 06YD, 06YJ, 0D5S and 08DW.
(blueprint: lem-sc-bottom-free-chain-pullback-comparison). -/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
attribute [local instance] CategoryTheory.Functor.additive_of_preserves_binary_products
  CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Additivity of the explicit pullback functor used in the comparison.

Source: Stacks Project, Tag 06YJ (tensor pullback is additive) and the additive
equivalence of localized module categories.
-/
private theorem bottomFreeChain_pullback_additive
    (T : Scheme.{u}) (T' : Scheme.{u}) (g : T' ⟶ T) (W : T.Opens) :
    let V := g ⁻¹ᵁ W
    let F := Modules.tensorPullback (g.resLE W V (le_refl V)) ⋙
      (Modules.overEquiv V).inverse
    F.Additive := by
  dsimp
  let h := g.resLE W (g ⁻¹ᵁ W) (le_refl (g ⁻¹ᵁ W))
  letI : HasBinaryBiproducts
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have hT : (Modules.tensorPullback h).Additive := by
    let adj := Classical.choice (Modules.nonempty_tensorPullbackAdjunction h)
    exact adj.left_adjoint_additive
  letI : (Modules.tensorPullback h).Additive := hT
  letI : HasBinaryBiproducts
      (SheafOfModules.{u} ((moduleRings T'.toRingedSpace).over (g ⁻¹ᵁ W))) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have hE : (Modules.overEquiv (g ⁻¹ᵁ W)).inverse.Additive := by
    letI : PreservesBinaryBiproducts (Modules.overEquiv (g ⁻¹ᵁ W)).inverse :=
      preservesBinaryBiproducts_of_preservesBinaryProducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  letI := hE
  exact inferInstance

set_option maxHeartbeats 1000000 in
-- Elaborating the two localization universes and the composed naturality square needs this budget.
set_option backward.isDefEq.respectTransparency false in
/-- Natural homology comparison for termwise pullback of a specified free chain square.
No vanishing or invertibility conditions are imposed in any degree.

Source: Stacks Project, Tags 06YD, 06YJ, 0D5S and 08DW.
(blueprint: lem-sc-bottom-free-chain-pullback-comparison).

Proof: Put V = g inverse-image W and h = g.resLE W V (le_refl V). Construct F as
Modules.tensorPullback h followed by (Modules.overEquiv V).inverse. Tensor pullback
is additive by its pinned adjunction, and the equivalence is additive. Finite free
terms are flat; bounded-above flat complexes A and B are K-flat (06YD). The single
left-derived counit for tensor pullback h is invertible at both A and B (06YJ),
and its naturality at alpha gives a square for their termwise images. Identify
restriction to W with derived pullback W.ι using exactness of open restriction
and the left-derived universal property. Compose the given square with derived
composition and the open-restriction comparison (0D5S, 08DW), then apply derived
homology and its natural factorization through Q. Finally use the exact homology
comparison for (Modules.overEquiv V).inverse. The resulting eP and eQ satisfy the
stated equation by naturality of each comparison. This construction works for the
empty open and zero ranks, arbitrary integer a, and without bottom-degree conditions.
The functor is constructed explicitly as the tensor pullback followed by the site
equivalence; the endpoint isomorphisms are the components of these comparisons.
-/
theorem bottomFreeChain_pullback_comparison
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (T : Scheme.{u}) (X Z : schemeDerivedCategory T) (f : X ⟶ Z) (a : ℤ)
    (W : T.Opens)
    (A B : CochainComplex
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) ℤ)
    (hAbounded : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (A.X i))
    (hBbounded : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (B.X i))
    (hAfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (A.X i ≅ SheafOfModules.free
      (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n))))
    (hBfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (B.X i ≅ SheafOfModules.free
      (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n))))
    (α : A ⟶ B)
    (eA : (derivedPullback W.ι).obj X ≅ DerivedCategory.Q.obj A)
    (eB : (derivedPullback W.ι).obj Z ≅ DerivedCategory.Q.obj B)
    (hsquare : (derivedPullback W.ι).map f ≫ eB.hom =
      eA.hom ≫ DerivedCategory.Q.map α)
    (T' : Scheme.{u}) (g : T' ⟶ T) :
    let V := g ⁻¹ᵁ W
    let F := Modules.tensorPullback (g.resLE W V (le_refl V)) ⋙
      (Modules.overEquiv V).inverse
    ∃ hF : F.Additive,
      letI := hF
      let P := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A
      let Q := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj B
      let β := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map α
      ∃ (eP : ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).obj
          ((derivedPullback g).obj X)).over V ≅ P.homology a)
        (eQ : ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).obj
          ((derivedPullback g).obj Z)).over V ≅ Q.homology a),
        (((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).map
            ((derivedPullback g).map f)).over V) ≫ eQ.hom =
              eP.hom ≫ HomologicalComplex.homologyMap β a := by
  let V := g ⁻¹ᵁ W
  let F := Modules.tensorPullback (g.resLE W V (le_refl V)) ⋙
    (Modules.overEquiv V).inverse
  have hF : F.Additive := bottomFreeChain_pullback_additive T T' g W
  letI := hF
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} ((moduleRings T'.toRingedSpace).over V))
  let R := SheafOfModules.overFunctor.{u} (moduleRings T'.toRingedSpace) V
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} ((moduleRings T'.toRingedSpace).over V)) a
  let P := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A
  let Q := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj B
  let β := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map α
  obtain ⟨dP, dQ, hd⟩ := bottomFreeChain_derived_square T X Z f W A B hAbounded
    hBbounded hAfree hBfree α eA eB hsquare T' g hF
  let η := (R.mapDerivedCategoryHomologyFunctorIso a).symm
  let eP := η.symm.app ((derivedPullback g).obj X) ≪≫ H.mapIso dP ≪≫
    (DerivedCategory.homologyFunctorFactors _ a).app P
  let eQ := η.symm.app ((derivedPullback g).obj Z) ≪≫ H.mapIso dQ ≪≫
    (DerivedCategory.homologyFunctorFactors _ a).app Q
  refine ⟨hF, eP, eQ, ?_⟩
  have hη := η.inv.naturality ((derivedPullback g).map f)
  have hh := congrArg H.map hd
  have hβ := DerivedCategory.homologyFunctorFactors_hom_naturality β a
  dsimp only [Functor.comp_map] at hη
  change R.map ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).map
      ((derivedPullback g).map f)) ≫
    (η.inv.app ((derivedPullback g).obj Z) ≫ H.map dQ.hom) ≫
      (DerivedCategory.homologyFunctorFactors _ a).hom.app Q =
    (η.inv.app ((derivedPullback g).obj X) ≫ H.map dP.hom) ≫
      (DerivedCategory.homologyFunctorFactors _ a).hom.app P ≫
        HomologicalComplex.homologyMap β a
  simp only [Category.assoc]
  rw [reassoc_of% hη]
  simp only [Functor.map_comp] at hh
  rw [reassoc_of% hh, hβ]


end AlgebraicGeometry.Scheme
