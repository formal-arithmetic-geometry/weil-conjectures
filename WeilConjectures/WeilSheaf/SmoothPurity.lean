/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PurityTensorMap
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.WeilSheaf.UpperShriek
public import WeilConjectures.WeilSheaf.UpperShriekGeometric
public import WeilConjectures.WeilSheaf.UpperStarConstant
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
import WeilConjectures.TraceFormula.PurityDevissage

/-!
# Smooth purity for Weil complexes

For a smooth separated morphism `f : X ⟶ Y` of pure relative dimension `d` of `k₀`-schemes of
finite type, the exceptional inverse image of Weil complexes is the twisted shifted pullback,
`Rf^! ≅ f^*(d)[2d]`. Since `Rf^!` is characterized as the right adjoint of the direct image with
compact support `Rf₀!` (`def-weil-exceptional-inverse-image`), this is the statement that
`f^*(d)[2d]` is right adjoint to `Rf₀!`
(`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_adjunction_of_smooth`, the Weil stage
`Λ = ℚ̄_ℓ` of `sk-thm-purity-transport`).

## Proof

`Rf₀!` has a right adjoint `Rf^!`
(`AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek`), so it suffices to show
`f^*(d)[2d] ≅ Rf^!`. Forgetting the Weil structure, the underlying complex of `Rf^! L` on the
geometric fibre `X̄` is `Rf̄^!` of that of `L`
(`WeilComplex.nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriek`).
Through this identification, the purity map `γ_{f,L} : f^* L(d)[2d] ⟶ Rf^! L` of Weil complexes
is the geometric purity map `f̄^* L̄ ⊗ Rf̄^! ℚ̄_ℓ ⟶ Rf̄^! L̄`
(`AlgebraicGeometry.WeilComplex.exists_natTrans_forget_eq_upperShriekUnitTensorMap`),
which is an isomorphism by smooth purity over `k̄`
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth`). Forgetting
the Weil structure reflects isomorphisms
(`CategoryTheory.Endofunctor.IsoAlgebra.isIso_of_isIso_forget_mapDerivedCategory_map`), so `γ_f`
is an isomorphism.

## Unfinished

The Weil equivariance of the purity map,
`exists_natTrans_forget_eq_upperShriekUnitTensorMap`, is stated with `sorry`. Its
proof needs:
- a purity map `γ_f` of Weil complexes, natural in `L`, e.g. the adjoint under `Rf₀! ⊣ Rf^!` of a
  smooth trace `Rf₀! f^* L(d)[2d] ⟶ L` of Weil complexes, together with its Frobenius
  equivariance (`thm-pur-weil-equivariance-of-purity-and-trace`). The condensed orientation
  `AlgebraicGeometry.ProEtale.CondensedRing.smoothOrientation` is not canonical, and
  `AlgebraicGeometry.Etale.exists_tateOrientation_isWeilMorphism_untwistedSmoothTrace` is for finite
  coefficients over `Spec k₀`;
- the comparison of pullback and Tate twist of Weil complexes with forgetting the Weil structure
  (the native pullback–tensor comparison), to identify the source of `γ_f` on `X̄`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

section Geometric

open ProEtale MonoidalCategory

variable [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l f]

/-- **Weil equivariance of the purity map** (blueprint:
`thm-pur-weil-equivariance-of-purity-and-trace`, at the coefficient stage `ℚ̄_ℓ`): let
`f : X ⟶ Y` be smooth separated of pure relative dimension `d`, and let `φ_L` identify the
underlying complex on `X̄` of `Rf^! L` with `Rf̄^!` of the underlying complex `L̄` of `L` (such
identifications exist by
`WeilComplex.nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriek`).
Then there is a natural morphism of Weil complexes `γ_{f,L} : f^* L(d)[2d] ⟶ Rf^! L` which,
read through `φ_L`, is the geometric purity map
`γ_{f̄,L̄} : f̄^* L̄ ⊗ Rf̄^! ℚ̄_ℓ ⟶ Rf̄^! L̄`
(`AlgebraicGeometry.ProEtale.CondensedRing.upperShriekUnitTensorMap`) up to an isomorphism `ψ_L`
of the sources.

The source isomorphism `ψ_L` is the comparison of pullback, Tate twist and shift with forgetting
the Weil structure, followed by the smooth purity isomorphism `Rf̄^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso`); here it is only required to exist.
The content is the construction of `γ_f` as a morphism of Weil complexes: the geometric purity map
must commute with the Frobenius structures. This is stated with `sorry`; see the module docstring
for what its proof still needs. -/
theorem exists_natTrans_forget_eq_upperShriekUnitTensorMap (d : ℕ)
    [SmoothOfRelativeDimension d f]
    (φ : ∀ L : WeilComplex k₀ l Y, (adicSheafDerivedEquivCondensedMod l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
          (forget.obj ((upperShriek f).obj L)) ≅
      ((CondensedRing.boundedConstructibleUpperShriek l (geometricFiberHom (k₀ := k₀) f)).obj
        (geometricFiberBoundedConstructibleObj L)).obj) :
    ∃ γ : upperStar f ⋙ tateTwist k₀ l X d ⋙ shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ) ⟶
        upperShriek f,
      ∀ L : WeilComplex k₀ l Y, ∃ ψ : (adicSheafDerivedEquivCondensedMod l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
            (forget.obj ((upperStar f ⋙ tateTwist k₀ l X d ⋙
              shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ)).obj L)) ≅
          ((CondensedRing.boundedConstructibleUpperStar _ l (geometricFiberHom (k₀ := k₀) f)).obj
              (geometricFiberBoundedConstructibleObj L) ⊗
            (CondensedRing.boundedConstructibleUpperShriek l
              (geometricFiberHom (k₀ := k₀) f)).obj (𝟙_ _)).obj,
        (adicSheafDerivedEquivCondensedMod l _).functor.map (forget.map (γ.app L)) ≫ (φ L).hom =
          ψ.hom ≫ (ObjectProperty.ι _).map (CondensedRing.upperShriekUnitTensorMap l
            (geometricFiberHom (k₀ := k₀) f) (geometricFiberBoundedConstructibleObj L)) :=
  sorry

/-- **The purity map of Weil complexes** (blueprint: `thm-pur-weil-equivariance-of-purity-and-trace`
and `sk-thm-purity-transport`, at the coefficient stage `ℚ̄_ℓ` with Weil structures): for a smooth
separated morphism `f : X ⟶ Y` of pure relative dimension `d` of `k₀`-schemes of finite type, there
is a natural morphism of Weil complexes `γ_{f,L} : f^* L(d)[2d] ⟶ Rf^! L` which is an isomorphism
on the underlying `ℓ`-adic complexes on the geometric fibre `X̄`.

The underlying complex of `Rf^! L` is `Rf̄^!` of that of `L`
(`WeilComplex.nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriek`),
and through this identification `γ_f` is the geometric purity map
(`AlgebraicGeometry.WeilComplex.exists_natTrans_forget_eq_upperShriekUnitTensorMap`),
an isomorphism by smooth purity
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth`). -/
theorem exists_natTrans_upperShriek_isIso_forget_of_smooth (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    ∃ γ : upperStar f ⋙ tateTwist k₀ l X d ⋙ shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ) ⟶
        upperShriek f,
      ∀ L : WeilComplex k₀ l Y, IsIso (forget.map (γ.app L)) := by
  have φ (L : WeilComplex k₀ l Y) :=
    (nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriek f
      (derivedLowerShriekUpperShriekAdjunction f) L).some
  obtain ⟨γ, hγ⟩ :=
    exists_natTrans_forget_eq_upperShriekUnitTensorMap (l := l) f d φ
  refine ⟨γ, fun L ↦ ?_⟩
  obtain ⟨ψ, hψ⟩ := hγ L
  have : Smooth f := SmoothOfRelativeDimension.smooth (n := d) (f := f)
  have : Smooth (geometricFiberHom (k₀ := k₀) f).left :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Smooth) f (comp_over f _) ‹_›
  have := CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth l
    (geometricFiberHom (k₀ := k₀) f) (geometricFiberBoundedConstructibleObj L)
  have : IsIso ((adicSheafDerivedEquivCondensedMod l _).functor.map (forget.map (γ.app L))) := by
    rw [(Iso.eq_comp_inv _).2 hψ]
    infer_instance
  exact isIso_of_reflects_iso _ (adicSheafDerivedEquivCondensedMod l _).functor

end Geometric

/-- **Smooth purity for Weil complexes** (blueprint: `sk-thm-purity-transport`, at the coefficient
stage `ℚ̄_ℓ` with Weil structures): for a smooth separated morphism `f : X ⟶ Y` of pure relative
dimension `d` of `k₀`-schemes of finite type, the twisted shifted pullback `K ↦ f^* K(d)[2d]` of
Weil complexes is right adjoint to the direct image with compact support `Rf₀!`; that is,
`Rf^! ≅ f^*(d)[2d]`. The purity map `f^*(d)[2d] ⟶ Rf^!`
(`AlgebraicGeometry.WeilComplex.exists_natTrans_upperShriek_isIso_forget_of_smooth`) is an
isomorphism, since forgetting the Weil structures reflects isomorphisms. -/
theorem nonempty_derivedLowerShriek_adjunction_of_smooth (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (derivedLowerShriek k₀ l f ⊣
      upperStar f ⋙ tateTwist k₀ l X d ⋙ shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ)) := by
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]
    infer_instance
  have : IsSeparated (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]
    infer_instance
  have := isLeftAdjoint_derivedLowerShriek (k₀ := k₀) (l := l) f
  obtain ⟨γ, hγ⟩ := exists_natTrans_upperShriek_isIso_forget_of_smooth (k₀ := k₀) (l := l) f d
  have (L : WeilComplex k₀ l Y) : IsIso (γ.app L) := by
    have : IsIso ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.map (γ.app L).hom) :=
      hγ L
    have : IsIso ((ObjectProperty.ι (WeilComplex.objectProperty k₀ l X)).map (γ.app L)) :=
      Endofunctor.IsoAlgebra.isIso_of_isIso_forget_mapDerivedCategory_map (γ.app L).hom
    exact isIso_of_fully_faithful (ObjectProperty.ι _) _
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  exact ⟨(derivedLowerShriekUpperShriekAdjunction f).ofNatIsoRight (asIso γ).symm⟩

variable {f} in
/-- **The exceptional inverse image of `ℚ̄_ℓ` along a smooth morphism** (blueprint:
`cor-pur-adic-and-rational-smooth-dualizing-complexes`, at the coefficient stage `ℚ̄_ℓ`): for a
smooth separated morphism `f : X ⟶ Y` of pure relative dimension `d`, and any right adjoint `G` of
`Rf₀!`, `G ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]`. This is smooth purity
(`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_adjunction_of_smooth`) applied to
`ℚ̄_ℓ`, with `f^* ℚ̄_ℓ ≅ ℚ̄_ℓ`. -/
theorem nonempty_rightAdjoint_obj_adicConstant_iso_of_smooth (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    {G : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerShriek k₀ l f ⊣ G) :
    Nonempty (G.obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      ((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧) := by
  obtain ⟨adj'⟩ := nonempty_derivedLowerShriek_adjunction_of_smooth (k₀ := k₀) (l := l) f d
  let e : (upperStar f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X) :=
    (ObjectProperty.isoMk _ (((ProEtaleWeilSheaf.upperStar k₀ l f).mapDerivedCategorySingleFunctor
      0).app (WeilSheaf.adicConstant k₀ l Y).obj) :
        _ ≅ WeilSheaf.toComplex.obj
          ((WeilSheaf.upperStar f).obj (WeilSheaf.adicConstant k₀ l Y))) ≪≫
      WeilSheaf.toComplex.mapIso (WeilSheaf.upperStarAdicConstantIso f)
  exact ⟨(adj.rightAdjointUniq adj').app _ ≪≫
    (tateTwist k₀ l X d ⋙ shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ)).mapIso e⟩

end WeilComplex

end AlgebraicGeometry
