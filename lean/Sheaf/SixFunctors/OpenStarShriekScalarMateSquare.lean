/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.TransverseTameOpenShriekExchange
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.SixFunctors.OpenScalarConjugateNormalization
import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import Sheaf.Algebra.Homology.LocallyFreeDerivedScalars
import Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting
import Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit
import Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel

/-! # The normalized open star/shriek scalar square

Source: blueprint main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md,
paragraph (3), agent-extracted scalar-mate sublemma
(blueprint: lem-sfb-open-star-shriek-scalar-mate-square).

The open exchange is the published adjunct of the inverse slice comparison.
The scalar/pullback comparisons are fixed by their scalar-adjunction mates; the
finite-free comparison is fixed by its scalar unit. No flatness is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.OpenStarShriekScalar

variable {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
  (φ : A ⟶ B) [IsMonHom φ]

/-- The existing derived scalar extension, projected from its specified adjunction.
Source: paragraph (3), T_T (blueprint: lem-sfb-open-star-shriek-scalar-mate-square). -/
abbrev scalar (T : Scheme.{u}) :=
  (fun {F : _} {G : _} (_ : F ⊣ G) ↦ F)
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ T))

/-- The prescribed inverse scalar/pullback mate. Its direction is theta, inverse to
lambda_d in the proof, so that beta uses its inverse.
Source: paragraph (3), canonical scalar comparison; proof step 3
(blueprint: lem-sfb-open-star-shriek-scalar-mate-square). -/
def pullMate {S T : Scheme.{u}} (f : S ⟶ T) :
    D((f)^*⟦A⟧) ⋙ scalar φ S ⟶ scalar φ T ⋙ D((f)^*⟦B⟧) :=
  ((mateEquiv
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ T))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ S))).symm
      (TwoSquare.mk _ _ _ _ (derivedComapUpperStarIso φ f).inv)).natTrans

/-- Beta is the geometric adjunct of inverse theta followed by scalar extension of
 the actual A-counit. The theorem below fixes theta.hom to pullMate, rather than
 assuming an arbitrary endpoint identification.
Source: paragraph (3), definition of beta
(blueprint: lem-sfb-open-star-shriek-scalar-mate-square). -/
def beta {S T : Scheme.{u}} (f : S ⟶ T)
    (θ : D((f)^*⟦A⟧) ⋙ scalar φ S ≅ scalar φ T ⋙ D((f)^*⟦B⟧))
    (H : DerivedCategory (TransverseTame.Modules A S)) :
    (scalar φ T).obj ((moduleObjectDerivedPushforward A f).obj H) ⟶
      (moduleObjectDerivedPushforward B f).obj ((scalar φ S).obj H) :=
  (((derivedUpperStarLowerStarAdjunction B f).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory B f)).homEquiv _ _)
      (θ.inv.app ((moduleObjectDerivedPushforward A f).obj H) ≫
        (scalar φ S).map
          (((derivedUpperStarLowerStarAdjunction A f).ofNatIsoLeft
            (leftDerivedUpperStarIsoMapDerivedCategory A f)).counit.app H))

/-- The scalar comparison for a_* with the normalized finite-free identification.
Source: paragraph (3), Theta_a
(blueprint: lem-sfb-open-star-shriek-scalar-mate-square). -/
def thetaA {W U : Scheme.{u}} (a : W ⟶ U)
    (θ : D((a)^*⟦A⟧) ⋙ scalar φ W ≅ scalar φ U ⋙ D((a)^*⟦B⟧))
    {M : DerivedCategory (TransverseTame.Modules A W)}
    {N : DerivedCategory (TransverseTame.Modules B W)}
    (ι : (scalar φ W).obj M ≅ N) :=
  beta φ a θ M ≫ (moduleObjectDerivedPushforward B a).map ι.hom

/-- The scalar comparison for j_* b_!, using the specified conjugate delta_b.
Source: paragraph (3), delta_b,L and Theta_j
(blueprint: lem-sfb-open-star-shriek-scalar-mate-square). -/
def thetaJ {W V X : Scheme.{u}} (b : W ⟶ V) (j : V ⟶ X) [IsOpenImmersion b]
    (θ : D((j)^*⟦A⟧) ⋙ scalar φ V ≅ scalar φ X ⋙ D((j)^*⟦B⟧))
    {M : DerivedCategory (TransverseTame.Modules A W)}
    {N : DerivedCategory (TransverseTame.Modules B W)}
    (ι : (scalar φ W).obj M ≅ N) :=
  beta φ j θ (D((b)_!open⟦A⟧).obj M) ≫
    (moduleObjectDerivedPushforward B j).map
      ((derivedOpenImmersionShriekIso φ b).hom.app M ≫ D((b)_!open⟦B⟧).map ι.hom)

/-- The canonical scalar comparison of the finite-rank lisse input intertwines
star/shriek exchange with the specified conjugate open-scalar isomorphisms.

Source: blueprint main-20261015, direct-image stability proof paragraph (3),
agent-extracted sublemma (blueprint: lem-sfb-open-star-shriek-scalar-mate-square).

Proof:
1. Transport L by lem-sfb-internal-section-scalar-adjunction. Its finite-free charts
allow lem-sfb-locally-free-derived-scalars to compute scalar extension in degree zero.
The actual scalar adjunction identifies its unit with x maps to 1 tensor x, giving iota
with the displayed unit equation. No flatness of B over A is used.
2. For R=A,B the ordinary restriction comparison of
lem-sfb-module-direct-image-open-pasting is its actual counit mate by
lem-sfb-proetale-open-restriction-counit and lem-sfb-alpha-iso. Descend on K-injectives
by lem-sfb-kinjective-direct-image-open-word-model. This is precisely the published
TransverseTame.restrictionComparison; its inverse adjunct is TransverseTame.exchange.
3. Use lem-sfb-open-scalar-conjugate-normalization for b and c. Under the actual open
units, delta_b restricts to inverse theta_b, and delta_c inverse restricts to theta_c.
The scalar mates are the canonical K-flat comparisons, with forward map pullMate.
4. Apply lem-sfb-scalar-geometric-exchange-rectangle to (j,c,a,b), at b_!L[0].
Naturality of exchange and beta_a, and step 3, identify the restriction of Theta_j
with Theta_a composed with scalar extension of the A-restriction comparison.
Postcompose with a_*(iota), using naturality in iota.
5. Precompose both proposed maps with delta_c inverse and transpose under c_! adjoint
c^*. Step 3, naturality of theta_c and step 4 make the left transpose equal to the
inverse B-restriction comparison followed by Theta_a. Naturality of the actual open
unit and the defining equation of e_B give the same right transpose. Injectivity of
the Hom adjunction and invertibility of delta_c give the displayed equality.
6. These formulas include identity opens, empty W and rank zero. Neither e nor beta
is inverted. All categories are ordinary unbounded derived categories. -/
theorem open_star_shriek_scalar_mate_square
    {W V U X : Scheme.{u}} (b : W ⟶ V) (a : W ⟶ U) (j : V ⟶ X) (c : U ⟶ X)
    [IsOpenImmersion b] [IsOpenImmersion a] [IsOpenImmersion j] [IsOpenImmersion c]
    [QuasiCompact j] [QuasiCompact c] (sq : IsPullback b a j c)
    (L : TransverseTame.Modules A W) (_hL : IsLisseCoefficientModule A L) :
    ∃ (θj : D((j)^*⟦A⟧) ⋙ scalar φ V ≅ scalar φ X ⋙ D((j)^*⟦B⟧))
      (θa : D((a)^*⟦A⟧) ⋙ scalar φ W ≅ scalar φ U ⋙ D((a)^*⟦B⟧)),
      θj.hom = pullMate φ j ∧ θa.hom = pullMate φ a ∧
      ∃ ι : (scalar φ W).obj ((DerivedCategory.singleFunctor _ 0).obj L) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((Mod.extendScalars (coefficientMap φ W)).obj L),
        (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ W)).unit.app
            ((DerivedCategory.singleFunctor _ 0).obj L) ≫
          D(Mod.comap (coefficientMap φ W)).map ι.hom ≫
          ((Mod.comap (coefficientMap φ W)).mapDerivedCategorySingleFunctor 0).hom.app
            ((Mod.extendScalars (coefficientMap φ W)).obj L) =
          (DerivedCategory.singleFunctor _ 0).map
            ((Mod.extendRestrictAdjunction (coefficientMap φ W)).unit.app L) ∧
        (scalar φ X).map
            (TransverseTame.exchange A sq ((DerivedCategory.singleFunctor _ 0).obj L)) ≫
          thetaJ φ b j θj ι =
        (derivedOpenImmersionShriekIso φ c).hom.app
            ((moduleObjectDerivedPushforward A a).obj
              ((DerivedCategory.singleFunctor _ 0).obj L)) ≫
          D((c)_!open⟦B⟧).map (thetaA φ a θa ι) ≫
          TransverseTame.exchange B sq
            ((DerivedCategory.singleFunctor _ 0).obj
              ((Mod.extendScalars (coefficientMap φ W)).obj L)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.OpenStarShriekScalar
