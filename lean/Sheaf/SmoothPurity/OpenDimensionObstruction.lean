/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.TateTwist.ProEtale
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # The cohomological obstruction to positive-dimensional purity for an open immersion

Source: the canonical derived t-structure and the definition of the condensed Tate complex;
this certifies the missing-hypothesis diagnostic for SmoothPurity.Defs.
(blueprint: lem-pur-open-positive-dimension-obstruction)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem isZero_of_single_shift_iso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (A B : C) (d : ℕ) (hd : 0 < d)
    (e : (DerivedCategory.singleFunctor C 0).obj A ≅
      (shiftFunctor _ (2 * (d : ℤ))).obj ((DerivedCategory.singleFunctor C 0).obj B)) :
    IsZero A := by
  let a := e ≪≫ ((DerivedCategory.singleFunctors C).shiftIso (2 * (d : ℤ))
    (-(2 * (d : ℤ))) 0 (by omega)).app B
  have hz := DerivedCategory.isZero_of_isLE
    ((DerivedCategory.singleFunctor C (-(2 * (d : ℤ)))).obj B)
    (-(2 * (d : ℤ))) 0 (by omega)
  exact hz.of_iso
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).symm.app A ≪≫
      (DerivedCategory.homologyFunctor C 0).mapIso a)

/-- An open immersion cannot have a positive-dimensional purity isomorphism unless its
source coefficient unit is zero. No assertion about smoothTrace or smoothPurityMap is used.

Source: DerivedCategory.singleFunctorCompHomologyFunctorIso, the single-functor shift
comparison, and boundedConstructibleUpperShriekUnitIso_padicAlgCl.
(blueprint: lem-pur-open-positive-dimension-obstruction)

Proof: the actual open-adjunction unit comparison identifies the exceptional inverse
image of the coefficient unit with that unit. The latter is the regular module in
cohomological degree zero. A Tate twist is also a degree-zero single complex; shifting
it by 2d places it in degree -2d. For d positive its zeroth cohomology vanishes. Applying
zeroth cohomology to the alleged isomorphism and using the canonical single/homology
comparison therefore makes the regular module a zero object. This includes the empty
scheme, where the conclusion is true, and uses no nonvanishing claim about Tate lines. -/
theorem isZero_unit_of_open_positive_purity
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (j : X ⟶ Y) [IsOpenImmersion j.left] (d : ℕ) (hd : 0 < d)
    (e : ((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))).obj ≅
      (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d)) :
    IsZero (𝟙_ (Mod (Sheaf (ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))) := by
  let C := Mod (Sheaf (ProEt.topology X.left) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)
  exact isZero_of_single_shift_iso (𝟙_ C) (tateTwist X.left ℓ d) d hd
    (DerivedCategory.singleFunctorObjUnitIso C ≪≫
      ((ObjectProperty.ι _).mapIso
        (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j)).symm ≪≫ e)

end AlgebraicGeometry.ProEtale.CondensedRing
