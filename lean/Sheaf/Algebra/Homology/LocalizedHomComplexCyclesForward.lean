module

public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Functor

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory

/-- The projection components of a localized degree-zero cycle form a chain map.
Source: Stacks Project, Tag 0A8X, construction preceding Equation 0A8Y.
(blueprint: lem-pur-localized-hom-complex-cycles-forward)

Proof: for a cycle z, define the degree-p component by applying the chosen
projection pi at U to iCycles z. An internal-Hom section is a linear natural
transformation on the slice; equip it with the sheaf-morphism wrapper. The cycle
inclusion followed by the differential is zero. Compose this equality with each
degree-one product projection and use the differential formula in
homComplex_exists at n = 0, m = 1. Since (-1)^0 = 1, it says that the component
followed by d_I equals d_L followed by the next component. These are exactly the
successive chain-map equations on the slice. Every other equation has both
complex differentials zero by the shape condition and preservation of zero
morphisms under restriction. Thus the components define a chain map for each z.
The asserted formula holds by construction. This argument needs neither an
inverse map nor preservation of the product by section evaluation. -/
theorem localizedHomComplex_cycles_forward
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
    letI := hzero
    let res : CochainComplex (SheafOfModules.{max u v} R₀) ℤ ⥤
        CochainComplex (SheafOfModules.{max u v} (R₀.over U)) ℤ :=
      (SheafOfModules.overFunctor.{max u v} R₀ U).mapHomologicalComplex (ComplexShape.up ℤ)
    ∃ f : S.cycles 0 → (res.obj L ⟶ res.obj I),
      (∀ (z : S.cycles 0) (p : ℤ) (W : (Over U)ᵒᵖ),
        ((f z).f p).val.app W =
          (((π L I 0 p p (add_zero p)).val.app (op U)) (S.iCycles 0 z)).app W) := by sorry

end CategoryTheory
