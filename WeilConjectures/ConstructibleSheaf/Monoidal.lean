/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.RingTheory.PicardGroup
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal

/-!
# Tensor products and duals of constructible sheaves

Let `Λ` be a commutative ring. For sheaves of `Λ`-modules on the small étale site of a scheme
`X`:

- a finite locally constant sheaf is constructible, for the trivial stratification, and a
  constructible sheaf has finitely generated stalks; so a sheaf is finite locally constant if and
  only if it is constructible and locally constant;
- the tensor product of two constructible sheaves is constructible: on the strata of a common
  refinement of stratifications the pullback of `F ⊗ G` is the tensor product of two finite
  locally constant sheaves, the pullback being monoidal;
- a sheaf of modules with a tensor inverse is finite: its stalks are invertible modules, hence
  finitely generated;
- for `Λ` noetherian, the internal hom `[F, Λ]` of a finite locally constant sheaf `F` into the
  unit is finite locally constant: on a trivialising cover it is the constant sheaf at
  `Hom_Λ(M, Λ)` for the finitely generated module `M`, a finitely generated module.

Unlike the tensor product, the internal hom of a constructible sheaf into the unit need not be
constructible without finiteness hypotheses on `X`: for an open immersion `j` it sends `j_!Λ` to
`j_*Λ`.

## Main results

- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.isConstructibleSheaf`
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.isFiniteSheaf`
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.tensorObj`
- `AlgebraicGeometry.Scheme.IsFiniteSheaf.of_tensorIso`
- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.ihom_unit`

## TODO

Prove `IsConstructibleSheaf.isFiniteSheaf`, `IsFiniteLocallyConstantSheaf.tensorObj` and
`IsFiniteLocallyConstantSheaf.ihom_unit`.
-/

@[expose] public section

universe u u'

open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

section General

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  {F : Sheaf X.smallEtaleTopology A}

/-- A finite locally constant sheaf is constructible, for the trivial stratification. -/
theorem IsFiniteLocallyConstantSheaf.isConstructibleSheaf (hF : IsFiniteLocallyConstantSheaf F) :
    IsConstructibleSheaf F :=
  ⟨Stratification.trivial X, fun _ ↦ IsFiniteLocallyConstantSheaf.upperStar (𝟙 X) F⟩

/-- A constructible sheaf is finite: a geometric point of `X` lies in a stratum, through whose
immersion it factors, and the stalk of `F` there is the stalk of the finite locally constant
pullback of `F` to the stratum. -/
theorem IsConstructibleSheaf.isFiniteSheaf (hF : IsConstructibleSheaf F) : IsFiniteSheaf F :=
  sorry

/-- A constructible locally constant sheaf is finite locally constant. -/
theorem IsConstructibleSheaf.isFiniteLocallyConstantSheaf (hF : IsConstructibleSheaf F)
    (hF' : IsLocallyConstantSheaf F) :
    IsFiniteLocallyConstantSheaf F where
  toIsLocallyConstantSheaf := hF'
  toIsFiniteSheaf := hF.isFiniteSheaf

end General

section Modules

variable {Λ : Type (u + 1)} [CommRing Λ] {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

/-- The tensor product of two finite locally constant sheaves of modules is finite locally
constant: on a common trivialising cover it is the constant sheaf at the tensor product of two
finitely generated modules. -/
theorem IsFiniteLocallyConstantSheaf.tensorObj (hF : IsFiniteLocallyConstantSheaf F)
    (hG : IsFiniteLocallyConstantSheaf G) :
    IsFiniteLocallyConstantSheaf (F ⊗ G) :=
  sorry

/-- **The tensor product of two constructible sheaves of modules is constructible**: on the
common refinement of witnessing stratifications, the pullback of `F ⊗ G` to a stratum is the
tensor product of two finite locally constant sheaves, the pullback being monoidal. -/
theorem IsConstructibleSheaf.tensorObj (hF : IsConstructibleSheaf F) (hG : IsConstructibleSheaf G) :
    IsConstructibleSheaf (F ⊗ G) := by
  obtain ⟨S, hS⟩ := hF.exists_stratification
  obtain ⟨T, hT⟩ := hG.exists_stratification
  refine ⟨S.inter T, fun k ↦ ?_⟩
  have hF' := (S.inter_refines_left T).isFiniteLocallyConstantSheaf_upperStar F hS k
  have hG' := (S.inter_refines_right T).isFiniteLocallyConstantSheaf_upperStar G hT k
  have := hF'.tensorObj hG'
  exact IsFiniteLocallyConstantSheaf.of_iso
    (Functor.Monoidal.μIso (Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)) F G)

/-- **The dual of a finite locally constant sheaf is finite locally constant**: for `Λ`
noetherian, the internal hom `[F, Λ]` of a finite locally constant sheaf `F` into the unit is
finite locally constant. On a trivialising cover it is the constant sheaf at `Hom_Λ(M, Λ)`, `M`
being finitely generated and hence finitely presented, `Λ` being noetherian; and
`Hom_Λ(M, Λ)` is finitely generated, being a submodule of `Λⁿ` for a surjection `Λⁿ ⟶ M`. -/
theorem IsFiniteLocallyConstantSheaf.ihom_unit [IsNoetherianRing Λ]
    (hF : IsFiniteLocallyConstantSheaf F) :
    IsFiniteLocallyConstantSheaf ((ihom F).obj (𝟙_ _)) :=
  sorry

/-- A sheaf of `Λ`-modules with a tensor inverse, `F ⊗ G ≅ Λ`, is finite: the stalks are strong
monoidal, so `F_s ⊗ G_s ≅ Λ` and `F_s` is an invertible, hence finitely generated, `Λ`-module. -/
theorem IsFiniteSheaf.of_tensorIso (e : F ⊗ G ≅ 𝟙_ _) : IsFiniteSheaf F where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    let Φ := (pointSmallEtale s).ulift.{u + 1}
    let e' : Φ.sheafFiber.obj F ⊗ Φ.sheafFiber.obj G ≅ 𝟙_ (ModuleCat.{u + 1} Λ) :=
      (Etale.sheafFiberTensorIso s F G).symm ≪≫ Φ.sheafFiber.mapIso e ≪≫
        Etale.sheafFiberUnitIso _ s
    have : Module.Invertible Λ ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :=
      .left e'.toLinearEquiv
    exact (((ModuleCat.isFinitelyGenerated_iff _).2 inferInstance).of_iso
      (((pointSmallEtale s).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).app F))

end Modules

end AlgebraicGeometry.Scheme
