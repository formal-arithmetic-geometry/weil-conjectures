/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.WeilSheaf.UpperStarConstant

/-!
# Smooth purity for Weil complexes

For a smooth separated morphism `f : X ⟶ Y` of pure relative dimension `d` of `k₀`-schemes of
finite type, the exceptional inverse image of Weil complexes is the twisted shifted pullback,
`Rf^! ≅ f^*(d)[2d]`. Since `Rf^!` is characterized as the right adjoint of the direct image with
compact support `Rf₀!` (`def-weil-exceptional-inverse-image`), this is the statement that
`f^*(d)[2d]` is right adjoint to `Rf₀!`.

This is the Weil stage (`Λ = ℚ̄_ℓ` with Weil structures) of `sk-thm-purity-transport`. It belongs to
the chapter on smooth purity, where it is proved for the condensed `ℚ̄_ℓ`-coefficients
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso`) but is not yet transported to Weil
complexes: it is stated here with `sorry`, as the input of
`AlgebraicGeometry.WeilComplex.nonempty_dualizingComplex_iso`
(`cor-pur-adic-and-rational-smooth-dualizing-complexes`).
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

/-- **Smooth purity for Weil complexes** (blueprint: `sk-thm-purity-transport`, at the coefficient
stage `ℚ̄_ℓ` with Weil structures): for a smooth separated morphism `f : X ⟶ Y` of pure relative
dimension `d` of `k₀`-schemes of finite type, the twisted shifted pullback `K ↦ f^* K(d)[2d]` of
Weil complexes is right adjoint to the direct image with compact support `Rf₀!`; that is,
`Rf^! ≅ f^*(d)[2d]`.

This input of the chapter on smooth purity is not formalized for Weil complexes yet; it is stated
with `sorry`. -/
theorem nonempty_derivedLowerShriek_adjunction_of_smooth (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    Nonempty (derivedLowerShriek k₀ l f ⊣
      upperStar f ⋙ tateTwist k₀ l X d ⋙ shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ)) :=
  sorry

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
