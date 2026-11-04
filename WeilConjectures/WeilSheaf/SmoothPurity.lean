/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.WeilSheaf.UpperShriek
public import WeilConjectures.WeilSheaf.UpperStarConstant
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp

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
`f^*(d)[2d] ≅ Rf^!`. The purity map `γ_{f,L} : f^* L(d)[2d] ⟶ Rf^! L` is a natural morphism
of Weil complexes, and on the underlying `ℓ`-adic complexes on the geometric fibre `X̄` it is
the geometric smooth purity isomorphism
(`AlgebraicGeometry.WeilComplex.exists_natTrans_upperShriek_isIso_forget_of_smooth`).
Forgetting the Weil structure reflects isomorphisms
(`CategoryTheory.Endofunctor.IsoAlgebra.isIso_of_isIso_forget_mapDerivedCategory_map`), so `γ_f`
is an isomorphism.

## Unfinished

The input `exists_natTrans_upperShriek_isIso_forget_of_smooth` is not proved, and it is as strong
as the conclusion: given the adjunction, `rightAdjointUniq` produces such a `γ`. It is the place
where the actual purity map has to be constructed. The planned construction defines `γ_f` as the
adjoint, under `Rf₀! ⊣ Rf^!`, of a smooth trace `Rf₀! f^* L(d)[2d] ⟶ L` of Weil complexes, and
compares it with the smooth purity of the condensed `ℚ̄_ℓ`-coefficients
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso`,
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth`).
It still lacks:
- a smooth trace for Weil complexes, or for `ℓ`-adic sheaves on `X̄`, natural in `L`, together with
  its Frobenius equivariance (`thm-pur-weil-equivariance-of-purity-and-trace`). The condensed
  orientation `AlgebraicGeometry.ProEtale.CondensedRing.smoothOrientation` is not canonical, and
  `AlgebraicGeometry.Etale.exists_tateOrientation_isWeilMorphism_untwistedSmoothTrace` is for finite
  coefficients over `Spec k₀`;
- the comparison of `For ∘ Rf₀!` with the condensed `Rf̄_!` on `Dᵇc`, and of `For ∘ Rf^!` with the
  geometric `Rf̄^!`.
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

/-- **The purity map of Weil complexes** (blueprint: `thm-pur-weil-equivariance-of-purity-and-trace`
and `sk-thm-purity-transport`, at the coefficient stage `ℚ̄_ℓ` with Weil structures): for a smooth
separated morphism `f : X ⟶ Y` of pure relative dimension `d` of `k₀`-schemes of finite type, there
is a natural morphism of Weil complexes `γ_{f,L} : f^* L(d)[2d] ⟶ Rf^! L` which is an isomorphism
on the underlying `ℓ`-adic complexes on the geometric fibre `X̄`.

This combines two inputs of the chapter on smooth purity that are not yet formalized for Weil
complexes:
- *Weil equivariance*: the purity map commutes with the Weil structures, so that it is a
  morphism of Weil complexes, natural in `L`;
- *identification*: forgetting the Weil structures, the Weil `Rf^!` is the exceptional inverse
  image on the geometric fibre, and `γ_f` is the smooth purity isomorphism there. This is proved
  for the condensed `ℚ̄_ℓ`-coefficients
  (`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso`).

It is stated with `sorry`; see the module docstring for what its proof still needs. -/
theorem exists_natTrans_upperShriek_isIso_forget_of_smooth
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [HasUpperShriek k₀ l f] (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    ∃ γ : upperStar f ⋙ tateTwist k₀ l X d ⋙ shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ) ⟶
        upperShriek f,
      ∀ L : WeilComplex k₀ l Y, IsIso (forget.map (γ.app L)) :=
  sorry

/-- **Smooth purity for Weil complexes** (blueprint: `sk-thm-purity-transport`, at the coefficient
stage `ℚ̄_ℓ` with Weil structures): for a smooth separated morphism `f : X ⟶ Y` of pure relative
dimension `d` of `k₀`-schemes of finite type, the twisted shifted pullback `K ↦ f^* K(d)[2d]` of
Weil complexes is right adjoint to the direct image with compact support `Rf₀!`; that is,
`Rf^! ≅ f^*(d)[2d]`. The purity map `f^*(d)[2d] ⟶ Rf^!`
(`AlgebraicGeometry.WeilComplex.exists_natTrans_upperShriek_isIso_forget_of_smooth`) is an
isomorphism, since forgetting the Weil structures reflects isomorphisms. -/
theorem nonempty_derivedLowerShriek_adjunction_of_smooth (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    Nonempty (derivedLowerShriek k₀ l f ⊣
      upperStar f ⋙ tateTwist k₀ l X d ⋙ shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ)) := by
  have : QuasiCompact (X ↘ Spec (CommRingCat.of k₀)) := by
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
    [SmoothOfRelativeDimension d f] {G : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X}
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
