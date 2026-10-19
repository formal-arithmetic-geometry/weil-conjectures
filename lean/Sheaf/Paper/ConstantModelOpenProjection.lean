/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom
import WeilConjectures.ConstructibleSheaf.Devissage

/-!
# Unbounded open projection formula for condensed coefficients

Source: blueprint main-20261015, sk-lem-integral-models-operations,
parent proof step 9 (blueprint: lem-sfb-constant-model-open-projection).
-/

@[expose] public section

set_option autoImplicit false

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Mod.extendScalars
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
  AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek


universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The unbounded open projection formula, with the ambient uncompleted tensor.
Source: integral-models-operations proof, paragraph (4), parent step 9;
Stacks Project, Modules on Sites Tag 0E8I and Cohomology on Sites,
lemma-j-shriek-and-tensor (blueprint: lem-sfb-constant-model-open-projection).

Proof: choose the complementary closed immersion. The existing open internal-Hom
formula, together with its naturality clause, identifies RHom(j!L,-) with
Rj* RHom(L,j*(-)). Compose the open adjunctions and the tensor-Hom adjunction for L:
j!(L tensor j*(-)) is a left adjoint of this right adjoint. Transport the tensor-Hom
adjunction for j!L through the displayed natural isomorphism. Uniqueness of left
adjoints gives (j!L) tensor (-) isomorphic to j!(L tensor j*(-)). Finally identify
the support pullback with the actual upperStar functor on derived objects.
No boundedness, flatness or constructibility is assumed on L or M. Empty and identity
open immersions are included by the same adjunction argument. -/
theorem constantModel_open_projection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    Nonempty ((((derivedTensor Λ X).obj
      ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L)).obj M) ≅
      (openImmersionLowerShriek Λ j).mapDerivedCategory.obj
        (((derivedTensor Λ U).obj L).obj ((upperStar Λ j).mapDerivedCategory.obj M))) :=
  by
    obtain ⟨Z, i, hi, hij⟩ := exists_isClosedImmersion_range_eq_compl j
    have := hi
    obtain ⟨p, o, c, hp, ho, hc, hn, hcn⟩ := openClosedInternalHomFormulas Λ i j hij
    let e : (derivedHom Λ X).obj (Opposite.op
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L)) ≅
        (supportPullback Λ j).mapDerivedCategory ⋙ (derivedHom Λ U).obj (Opposite.op L) ⋙
          (lowerStar Λ j).rightDerivedFunctor :=
      NatIso.ofComponents (fun N ↦ o L N) (by
        intro N N' b
        simpa using hn L L N N' (𝟙 L) b)
    let a := (closedSupportOpenDerivedAdjunction Λ j).comp
      ((derivedTensorHomAdjunction Λ L).comp (openSupportDerivedAdjunction Λ j))
    let b := (derivedTensorHomAdjunction Λ
      ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L)).ofNatIsoRight e
    let es := (Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ j)).app M
    exact ⟨(b.leftAdjointUniq a).app M ≪≫
      (openImmersionLowerShriek Λ j).mapDerivedCategory.mapIso
        (((derivedTensor Λ U).obj L).mapIso es)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
