/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Localized Hom boundaries and null-homotopies

Source: Stacks Project, Tag 0A8X, differential of the Hom complex,
and Equation 0A8Y, degree zero.
(blueprint: lem-pur-localized-hom-complex-boundaries)
-/

@[expose] public section

universe u v
open CategoryTheory Opposite
namespace CategoryTheory

/-- A localized chain map represented by a cycle is null-homotopic exactly when
that cycle is a boundary in the section complex.
Source: Stacks Project, Tag 0A8X, differential of the Hom complex,
and Equation 0A8Y, degree zero.
(blueprint: lem-pur-localized-hom-complex-boundaries)

Proof: the product fan specified by homComplex_exists remains limiting after
forgetting module sheaves, evaluating at U, and forgetting modules to abelian
groups. In degree -1 it identifies a section x with the family of localized
maps h_p : L^p|_U → I^(p-1)|_U supplied by the projections. Lift the underlying
presheaf-module maps to sheaf-module maps using the fully faithful forgetful
functor. The differential projection formula in degree -1 says that the p-th
component of d(x) is h_p followed by d_I plus d_L followed by h_(p+1), since
(-1)^(-1)=-1. The identity toCycles followed by iCycles equals d therefore
shows, using the assumed component formula for f, that these h_p form a
null-homotopy of f when z=toCycles(x). This proves the boundary-to-homotopy direction.
Conversely, take the adjacent-degree components h_p of a null-homotopy of f.
Their underlying presheaf maps assemble uniquely into a degree -1 section x
by the evaluated product fan. The same differential identity and the homotopy
commutation equation give d(x)=iCycles(z), component by component. The product
projections are jointly injective on sections. Since iCycles is monic, the
identity iCycles(toCycles(x))=d(x) implies toCycles(x)=z.
There is no boundedness or finite support assumption. For zero complexes the
section and map groups are zero. If both differentials vanish, the homotopy
equation forces f=0 and both sides require z=0. -/
theorem localizedHomComplex_nullHomotopy_iff_boundary
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v}) (U : C)
    (L I : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
    (hzero : Functor.PreservesZeroMorphisms
      (SheafOfModules.overFunctor.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) U)) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
    let H := homComplex (R := R) L I
    let π := Classical.choose (Classical.choose_spec
      (homComplex_exists.{u, v, max u v, max u v} (J := J) (R := R)))
    let S := ((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj H
    let := hzero
    let res : CochainComplex (SheafOfModules.{max u v} R₀) ℤ ⥤
        CochainComplex (SheafOfModules.{max u v} (R₀.over U)) ℤ :=
      (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex (ComplexShape.up ℤ)
    ∀ (z : S.cycles 0) (f : res.obj L ⟶ res.obj I),
      (∀ (p : ℤ) (W : (Over U)ᵒᵖ),
        (f.f p).val.app W =
          (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W) →
      (Nonempty (Homotopy f 0) ↔ ∃ x : S.X (-1), S.toCycles (-1) 0 x = z) := by sorry

end CategoryTheory
