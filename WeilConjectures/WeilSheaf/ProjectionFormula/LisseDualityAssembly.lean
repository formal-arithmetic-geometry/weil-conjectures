/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ProjectionFormula.LisseDualityWeil
public import WeilConjectures.WeilSheaf.ProjectionFormula.ExtensionByZeroIhom

/-!
# Duality for lisse pro-étale Weil sheaves

If the morphism `X ⊗ M^∨ ⟶ 𝓗om(M, X)` (`CategoryTheory.Mod.tensorDualToIhom`) is an isomorphism
for lisse `M`, then the internal hom out of a pro-étale Weil sheaf with lisse underlying sheaf is
the tensor product with its dual (`AlgebraicGeometry.ProEtaleWeilSheaf.lisseDuality_of_isIso`):
the morphism is compatible with the Weil structures
(`AlgebraicGeometry.ProEtale.tensorDualToIhom_comm`).
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Duality for lisse pro-étale Weil sheaves**, from the duality of lisse `ℓ`-adic sheaves. -/
theorem lisseDuality_of_isIso
    (h : ∀ {T : Scheme.{u}} {M : AdicSheaf l T}, IsAdicLisseSheaf M →
      ∀ N : AdicSheaf l T, IsIso (Mod.tensorDualToIhom M N)) :
    LisseDuality k₀ l := by
  intro T _ M hM
  have := h hM
  let e : tensorFunctor k₀ l T (ihom k₀ l T M (adicConstant k₀ l T)) ≅ ihomFunctor k₀ l T M :=
    NatIso.ofComponents
      (fun B ↦ IsoAlgebra.isoMk (asIso (Mod.tensorDualToIhom M.carrier B.carrier))
        (tensorDualToIhom_comm _ M.carrier B.carrier M.str B.obj.str))
      fun {B B' : ProEtaleWeilSheaf k₀ l T} (f : B ⟶ B') ↦ IsoAlgebra.hom_ext
        (Mod.tensorDualToIhom_naturality M.carrier f.hom.f)
  exact ⟨e.symm⟩

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The projection formula for Weil complexes**, from the duality of lisse `ℓ`-adic sheaves:
`Rf₀!(K) ⊗ G ≅ Rf₀!(K ⊗ f^* G)` for a lisse Weil sheaf `G`, provided
`X ⊗ M^∨ ⟶ 𝓗om(M, X)` is an isomorphism for lisse `M`. -/
theorem nonempty_iso_derivedLowerShriek_tensorLisse_of_isIso
    (h : ∀ {T : Scheme.{u}} {M : ProEtale.AdicSheaf l T}, ProEtale.IsAdicLisseSheaf M →
      ∀ N : ProEtale.AdicSheaf l T, IsIso (Mod.tensorDualToIhom M N))
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l Y) (hG : G.IsLisse) :
    Nonempty (derivedLowerShriek k₀ l f ⋙ tensorLisse G hG ≅
      tensorLisse ((WeilSheaf.upperStar f).obj G) (ProEtale.IsAdicLisseSheaf.upperStar _ hG) ⋙
        derivedLowerShriek k₀ l f) :=
  nonempty_iso_derivedLowerShriek_tensorLisse_of_duality
    (ProEtaleWeilSheaf.lisseDuality_of_isIso h) f G hG

end AlgebraicGeometry.WeilComplex
