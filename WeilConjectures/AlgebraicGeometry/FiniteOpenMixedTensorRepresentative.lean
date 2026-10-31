/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Derived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.FiniteOpenMixedTensorRepresentativeCounit
import WeilConjectures.AlgebraicGeometry.MixedRepForward.FiniteOpenMixedTensorRepresentativeForward
import WeilConjectures.CategoryTheory.FiniteOpenMixedTensorRepresentativeInverse

/-!
# Counit and cochain representative equations for the published mixed open tensor comparison

Source: Stacks Project, sites-cohomology.tex, Tag 07A4 (lemma-pullback-tensor-product)
(blueprint: lem-sf-finite-open-mixed-tensor-representative).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

private theorem mixedRep_cochain_tensor_obj
    {C : Type*} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    (P Q : CochainComplex C ℤ) :
    P ⊗ Q = HomologicalComplex.mapBifunctor P Q (curriedTensor C) (.up ℤ) := rfl

namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry Scheme

variable {A : Type (u + 1)} [CommRing A] [Finite A]
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The coefficient category `Sh(Y_proét, Mod_A)` on the small pro-étale site of `Y`.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4
(blueprint: lem-sf-finite-open-mixed-tensor-representative). -/
noncomputable abbrev FiniteCoeffSheaf (Y : Scheme.{u}) :=
  Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)

/-- The published pro-étale pullback `j^*` on `Mod_A`-valued sheaves.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4
(blueprint: lem-sf-finite-open-mixed-tensor-representative). -/
noncomputable abbrev FiniteCoeffUpperStar (j : U ⟶ X) :=
  (j)^*[ModuleCat.{u + 1} A]

/-- The curried sheaf tensor product of `Sh(Y_proét, Mod_A)`, whose `mapBifunctor` is the
signed direct-sum total tensor of cochain complexes.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4
(blueprint: lem-sf-finite-open-mixed-tensor-representative). -/
noncomputable abbrev FiniteCoeffCoTensor (Y : Scheme.{u}) :=
  curriedTensor (FiniteCoeffSheaf (A := A) Y)

set_option maxHeartbeats 1000000 in
-- Checking the concrete native sheaf tensor instances requires a larger kernel budget.
/-- For a finite commutative ring `A` and an open immersion `j : U ⟶ X`, with
`F = j^*` on pro-étale `Mod_A`-sheaves, `κ : LF ≅ DF`, `a : DF ∘ Q_X ≅ Q_U ∘ F_c`, `φ` the
published left-derived tensor comparison, `μ` the native lax tensorators of the cochain
localizations and `c` the signed total of the oplax tensorator of `F`:
(1) the left-derived counit at the homotopy image of `P`, transported along
`Q_X ≅ Q_{h,X} ∘ π_X` and `F_c ∘ π ≅ π ∘ F_h`, is `ε_P = κ_{Q_X P} ≫ a_P`;
(2) `φ ≫ (ε_P ⊗ ε_Q) ≫ μ^U = LF(μ^X) ≫ ε_{T_X(P,Q)} ≫ Q_U(c)`;
(3) `(κ⁻¹ ⊗ 1) ≫ φ⁻¹ ≫ κ ≫ DF(μ^X) ≫ a = (a_P ⊗ ε_Q) ≫ μ^U ≫ Q_U(c)⁻¹`.
No boundedness, flatness or K-flatness is assumed on `P, Q`; no `μ` is inverted.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4 (lemma-pullback-tensor-product).

Proof.
Step 1. `j^*` is exact, so the termwise factor `a^h : DF ∘ Q_{h,X} ≅ Q_{h,U} ∘ F_h` is
invertible on every complex and `(DF, a^h)` is a left-derived presentation of the same
functor as `(LF, ε^h)`. `κ` is the canonical comparison of the two presentations; the
counit-compatible uniqueness of right Kan extensions gives `κ_{Q_h H} ≫ a^h_H = ε^h_H`.
Whiskering by the homotopy quotient and conjugating by the canonical factors gives
`ε_P = κ_{Q_X P} ≫ a_P`, clause (1).
Step 2. `φ` is the universal lift of `LF(μ^h) ≫ ε^h ≫ Q_h(δ^h)` through the tensor counit
`(ε^h ⊗ ε^h) ≫ μ^{h,U}`; its defining equation is
`φ ≫ (ε^h_H ⊗ ε^h_J) ≫ μ^{h,U} = LF(μ^{h,X}) ≫ ε^h_{H ⊗ J} ≫ Q_h(δ^h_{H,J})`.
Step 3. Evaluate at `H = π P`, `J = π Q`. The native cochain lax structure is the
transport `μ = (r⁻¹ ⊗ r⁻¹) ≫ μ^h ≫ Q_h(t) ≫ r` along `quotientCompQhIso`, and `δ^h` at
`π P, π Q` is the image of `c`. Naturality moves the `t` and `r` factors to the ends,
where they cancel; with clause (1) this is clause (2).
Step 4. Naturality of `κ` gives `κ ≫ DF(μ^X) = LF(μ^X) ≫ κ`, so the left side of (3) is
`(κ⁻¹ ⊗ 1) ≫ φ⁻¹ ≫ LF(μ^X) ≫ ε_{T_X(P,Q)}`. Clause (2), composed with `φ⁻¹` before and
`Q_U(c)⁻¹` after, rewrites this as `(κ⁻¹ ⊗ 1) ≫ (ε_P ⊗ ε_Q) ≫ μ^U ≫ Q_U(c)⁻¹`, and
`κ⁻¹ ≫ ε_P = a_P` gives clause (3). Only `κ`, `φ` and `c` are inverted.
(blueprint: lem-sf-finite-open-mixed-tensor-representative)
-/
theorem finiteOpenMixedTensorRepresentative
    (P Q : CochainComplex (FiniteCoeffSheaf (A := A) X) ℤ) :
    L(FiniteCoeffUpperStar (A := A) j).map
        ((DerivedCategory.quotientCompQhIso (FiniteCoeffSheaf (A := A) X)).inv.app P) ≫
      (FiniteCoeffUpperStar (A := A) j).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map
        (((FiniteCoeffUpperStar (A := A) j).mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
      (DerivedCategory.quotientCompQhIso (FiniteCoeffSheaf (A := A) U)).hom.app
        (((FiniteCoeffUpperStar (A := A) j).mapHomologicalComplex (.up ℤ)).obj P) =
      (FiniteCoeffUpperStar (A := A) j).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) X)).obj P) ≫
        (FiniteCoeffUpperStar (A := A) j).mapDerivedCategoryFactors.hom.app P ∧
    ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso
      (ModuleCat.{u + 1} A) j).hom.app
      ((DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) X)).obj P)).app
      ((DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) X)).obj Q) ≫
      ((FiniteCoeffUpperStar (A := A) j).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) X)).obj P) ≫
        (FiniteCoeffUpperStar (A := A) j).mapDerivedCategoryFactors.hom.app P ⊗ₘ
       (FiniteCoeffUpperStar (A := A) j).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) X)).obj Q) ≫
        (FiniteCoeffUpperStar (A := A) j).mapDerivedCategoryFactors.hom.app Q) ≫
      (Functor.LaxMonoidal.μ (DerivedCategory.Q
        (C := FiniteCoeffSheaf (A := A) U))
        (((FiniteCoeffUpperStar (A := A) j).mapHomologicalComplex (.up ℤ)).obj P)
        (((FiniteCoeffUpperStar (A := A) j).mapHomologicalComplex (.up ℤ)).obj Q)) =
      L(FiniteCoeffUpperStar (A := A) j).map
        (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) X)) P Q) ≫
      ((FiniteCoeffUpperStar (A := A) j).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) X)).obj
          (HomologicalComplex.mapBifunctor P Q
            (FiniteCoeffCoTensor (A := A) X) (.up ℤ))) ≫
        (FiniteCoeffUpperStar (A := A) j).mapDerivedCategoryFactors.hom.app
          (HomologicalComplex.mapBifunctor P Q
            (FiniteCoeffCoTensor (A := A) X) (.up ℤ))) ≫
      (DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) U)).map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
          (FiniteCoeffUpperStar (A := A) j)).app P).app Q) ∧
    (((FiniteCoeffUpperStar (A := A) j).leftDerivedFunctorIsoMapDerivedCategory.inv.app
        ((DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) X)).obj P)) ⊗ₘ 𝟙 _) ≫
      ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso
        (ModuleCat.{u + 1} A) j).inv.app
        ((DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) X)).obj P)).app
        ((DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) X)).obj Q) ≫
      (FiniteCoeffUpperStar (A := A) j).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} A]).obj
          ((DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) X)).obj P)).obj
          ((DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) X)).obj Q)) ≫
      (FiniteCoeffUpperStar (A := A) j).mapDerivedCategory.map
        (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) X)) P Q) ≫
      (FiniteCoeffUpperStar (A := A) j).mapDerivedCategoryFactors.hom.app
        (HomologicalComplex.mapBifunctor P Q
          (FiniteCoeffCoTensor (A := A) X) (.up ℤ)) =
      ((FiniteCoeffUpperStar (A := A) j).mapDerivedCategoryFactors.hom.app P ⊗ₘ
        ((FiniteCoeffUpperStar (A := A) j).leftDerivedFunctorIsoMapDerivedCategory.hom.app
          ((DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) X)).obj Q) ≫
          (FiniteCoeffUpperStar (A := A) j).mapDerivedCategoryFactors.hom.app Q)) ≫
      (Functor.LaxMonoidal.μ (DerivedCategory.Q
        (C := FiniteCoeffSheaf (A := A) U))
        (((FiniteCoeffUpperStar (A := A) j).mapHomologicalComplex (.up ℤ)).obj P)
        (((FiniteCoeffUpperStar (A := A) j).mapHomologicalComplex (.up ℤ)).obj Q)) ≫
      inv ((DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) U)).map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
          (FiniteCoeffUpperStar (A := A) j)).app P).app Q)) := by
  constructor
  · have h := CategoryTheory.Functor.leftDerivedFactors_eq_counit
      (FiniteCoeffUpperStar (A := A) j) P
    rw [h]
    dsimp only [DerivedCategory.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
      CategoryTheory.Functor.mapHomotopyCategoryFactors]
    erw [CategoryTheory.Functor.map_id, Category.id_comp,
      CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
  · have hf := MixedRepForward.forward_transport j P Q
    refine ⟨hf, ?_⟩
    apply CategoryTheory.mixedTensor_inverse_transport
      L(FiniteCoeffUpperStar (A := A) j)
      (FiniteCoeffUpperStar (A := A) j).mapDerivedCategory
      (FiniteCoeffUpperStar (A := A) j).leftDerivedFunctorIsoMapDerivedCategory
      (((leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) j).app
        (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q))
      (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) X)) P Q)
      ((FiniteCoeffUpperStar (A := A) j).mapDerivedCategoryFactors.hom.app P)
      ((FiniteCoeffUpperStar (A := A) j).mapDerivedCategoryFactors.hom.app Q)
      ((FiniteCoeffUpperStar (A := A) j).mapDerivedCategoryFactors.hom.app
        (HomologicalComplex.mapBifunctor P Q (FiniteCoeffCoTensor (A := A) X) (.up ℤ)))
      (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) U))
        (((FiniteCoeffUpperStar (A := A) j).mapHomologicalComplex (.up ℤ)).obj P)
        (((FiniteCoeffUpperStar (A := A) j).mapHomologicalComplex (.up ℤ)).obj Q))
      (asIso ((DerivedCategory.Q (C := FiniteCoeffSheaf (A := A) U)).map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
          (FiniteCoeffUpperStar (A := A) j)).app P).app Q)))
    simpa only [FiniteCoeffUpperStar, FiniteCoeffCoTensor, derivedTensor,
      leftDerivedUpperStarDerivedTensor, Functor.postcompose₂_obj_obj_obj_obj,
      MonoidalCategory.curriedTensor_obj_obj, mixedRep_cochain_tensor_obj,
      Category.assoc, Iso.app_hom, asIso_hom] using hf

end AlgebraicGeometry.ProEtale
