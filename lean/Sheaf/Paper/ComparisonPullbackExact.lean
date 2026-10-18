/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.SfCommonStageWeilCohomology
import WeilConjectures.AlgebraicGeometry.DerivedCategories

/-!
# Exactness of the etale to pro-etale comparison pullback

Source: Stacks Project, Tags 04JC and 03D2; Pro-etale Cohomology, Tags 099R and
0GLZ (blueprint: lem-sf-comparison-pullback-exact).

## Main declarations

* `AlgebraicGeometry.comparisonConstantRingMap`: the canonical constant-ring comparison.
* `AlgebraicGeometry.comparisonPullbackExact`: its tensor identification, exactness and
  compatibility with cohomology sheaves.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped ChangeOfRings

namespace AlgebraicGeometry

/-- The canonical constant-ring comparison, adjoint to the map of constant etale
rings induced by the constant scalar sections of the pro-etale ring sheaf.
Source: Stacks, Tags 0H7J, 099R and 03D2
(blueprint: lem-sf-comparison-pullback-exact). -/
noncomputable def comparisonConstantRingMap (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] :
    (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt T)
      CommRingCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)).obj
        ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) ⟶
      (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
        (CommRingCat.of Λ) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Scheme.toProEt T)
    CommRingCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)).homEquiv _ _).symm
      (((constantSheafAdj T.smallEtaleTopology CommRingCat.{u + 1}
        (Scheme.Etale.isTerminalMkId T)).homEquiv _ _).symm
          ((toSheafify (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of Λ))).app
              (Opposite.op (Scheme.ProEt.mk (𝟙 T)))))

/-- The inverse image along the etale/pro-etale comparison is exact on finite
coefficient module sheaves and commutes with cohomology sheaves.

Source: Stacks Project, Tags 04JC and 03D2; Pro-etale Cohomology, Tags 099R and
0GLZ (blueprint: lem-sf-comparison-pullback-exact).
Proof, following the node's six steps:
1. In the common larger universe, the comparison-morphism node supplies the
   finite-limit-preserving left adjoint L and restriction right adjoint R.
   Lift the adjunction to ring objects by
   lem-weil-pbc-adjunction-lifts-group-ring-objects and identify them with ring
   sheaves by lem-weil-pbc-sheaf-algebraic-structures-objects (Tag 00YV).
2. Since R preserves sections at the terminal object, the constant-sheaf
   adjunction (lem-weil-pbc-constant-sheaf-maps-global-sections, Tag 0H7J)
   identifies Hom(L(Λ_et), G) with Hom(Λ_proet, G), naturally in G. The images
   of identity maps give inverse ring maps. The forward map is exactly
   comparisonConstantRingMap: its adjunct extends the constant scalar sections.
3. The module-adjunction theorem
   lem-weil-pbc-ringed-topoi-module-adjunction identifies ringed pullback with
   scalar extension of the induced inverse-image module (Tags 03D2 and 03D7).
   For any module M over L(Λ_et), the map on sectionwise tensors sends
   b tensor m to c.inv(b) times m; the inverse sends m to 1 tensor m.
   The balanced relation gives both inverse identities and the formulas commute
   with restriction. Sheafification gives the displayed abelian-sheaf isomorphism.
   This formula also identifies the induced scalar action; for constant λ it is
   L of multiplication by λ, as in the comparison-morphism node. Uniqueness on
   local pure tensors gives naturality in M. Thus scalar extension along c has
   the same underlying abelian sheaves and is exact, expressing flatness.
4. Apply lem-weil-pbc-site-pullback-abelian-exact (Tag 04JC). By
   def-weil-sheaf-of-modules-category, kernels and sheafified cokernels have
   the same underlying abelian sheaves. The module inverse image therefore
   preserves both and is additive. Finite limits are kernels between finite
   biproducts, and finite colimits are their cokernel analogues, including the
   empty diagram. This proves the three exact-functor clauses.
5. Apply lem-weil-pbc-exact-functor-complex-cohomology to each three-term
   segment of an arbitrary complex. It identifies pulled-back cycles and
   boundaries and hence their quotient, naturally in the complex. These are
   the cohomology sheaves of def-weil-derived-cohomology-sheaves, with the
   specified direction of the natural isomorphism and no boundedness condition.
6. For a quasi-isomorphism, naturality conjugates the pulled-back homology
   map to the image of its invertible homology map. For vanishing below a,
   the same isomorphism and preservation of zero give vanishing in every i < a.
   This includes every negative degree and proves both final clauses. -/
theorem comparisonPullbackExact (T : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] :
    (∃ c :
      ((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt T)
          CommRingCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)).obj
        ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)) ≅
        (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)),
      c.hom = comparisonConstantRingMap T Λ ∧
      ∀ M : SheafOfModules.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt T)
              CommRingCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)).obj
                ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
                  (CommRingCat.of Λ)))),
      ∃ e :
        (SheafOfModules.toSheaf
          ((sheafCompose (Scheme.ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
                (CommRingCat.of Λ)))).obj
                  (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
                    (C := T.ProEt) (J := Scheme.ProEt.topology T) c.hom M) ≅
        (SheafOfModules.toSheaf
          ((sheafCompose (Scheme.ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt T)
                CommRingCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)).obj
                  ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
                    (CommRingCat.of Λ))))).obj M,
      ∀ (W : T.ProEtᵒᵖ)
        (b : ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
          (CommRingCat.of Λ)).obj.obj W) (m : M.val.obj W),
        e.hom.hom.app W
          (((PresheafOfModules.sheafificationAdjunction.{u + 1}
            (R := (sheafCompose (Scheme.ProEt.topology T)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
                ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
                  (CommRingCat.of Λ)))
            (𝟙 (((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
              (CommRingCat.of Λ)).obj ⋙ forget₂ CommRingCat RingCat))).unit.app
                (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
                  (C := T.ProEt) (J := Scheme.ProEt.topology T) c.hom M)).app W
                  (b ⊗ₜ[_, (c.hom.hom.app W).hom] m)) =
          c.inv.hom.app W b • m) ∧
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T).Additive ∧
      PreservesFiniteLimits
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T) ∧
      PreservesFiniteColimits
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T) ∧
      (∀ (i : ℤ),
        Nonempty
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapHomologicalComplex
              (ComplexShape.up ℤ) ⋙
            HomologicalComplex.homologyFunctor
              (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))
              (ComplexShape.up ℤ) i ≅
            HomologicalComplex.homologyFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
              (ComplexShape.up ℤ) i ⋙
            ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T)) ∧
      (∀ {K L : CochainComplex
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
        (f : K ⟶ L),
        HomologicalComplex.quasiIso _ (ComplexShape.up ℤ) f →
          HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)
            (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f)) ∧
      (∀ (a : ℤ)
        (K : CochainComplex
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ),
        (∀ i : ℤ, i < a → IsZero (K.homology i)) →
          ∀ i : ℤ, i < a →
            IsZero
              ((((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K).homology i)) := by
  sorry

end AlgebraicGeometry
