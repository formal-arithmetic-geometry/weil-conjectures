/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.WeilSheaf.Stalk

/-!
# The dual and the geometric coinvariants of a Weil sheaf

The dual of a lisse Weil sheaf `F` is the internal hom `F^∨ = [F, ℚ̄_ℓ]` of étale sheaves on
the geometric fiber `X̄`. Its Weil structure is transported from that of `F`: the pullback `Fr^*`
along the automorphism `Fr` of `X̄` is a monoidal equivalence, so it commutes with internal
homs (`CategoryTheory.Functor.Monoidal.ihomObjIso`), and

`Fr^* [F, ℚ̄_ℓ] ≅ [Fr^* F, Fr^* ℚ̄_ℓ] ≅ [F, ℚ̄_ℓ]`

by the inverse of the Weil structure `φ : Fr^* F ≅ F` in the first variable and the unit
isomorphism `Fr^* ℚ̄_ℓ ≅ ℚ̄_ℓ` in the second. The internal hom is the duality functor only for
lisse `F`: for a skyscraper `F = i_* M` the internal hom `[F, ℚ̄_ℓ]` vanishes, and for an open
immersion `j` it sends `j_!ℚ̄_ℓ` to `j_*ℚ̄_ℓ`, which need not be constructible. The dual of a
general constructible `F` is its Verdier dual, a Weil complex.

The geometric coinvariants of `F` are the dual of the global sections of `F^∨`. For a lisse
`F` on a geometrically connected `X`, with geometric generic fibre `V` a representation of
`π₁(X̄)`, `Γ(X̄, F^∨) = (V^∨)^{π₁(X̄)} = (V_{π₁(X̄)})^∨`, whose dual is the space of coinvariants
`V_{π₁(X̄)}` with the Frobenius induced by `φ`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.dual`: the dual `F^∨ = [F, ℚ̄_ℓ]` of a lisse Weil sheaf, with
  the Weil structure `AlgebraicGeometry.WeilSheaf.dualStr`.
- `AlgebraicGeometry.WeilSheaf.dualStr_ev`: the evaluation `F ⊗ F^∨ ⟶ ℚ̄_ℓ` is compatible
  with the Weil structures.
- `AlgebraicGeometry.WeilSheaf.geometricCoinvariants`: the geometric coinvariants of a lisse
  Weil sheaf, with the Frobenius induced from the Weil structure.
- `AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_geometricCoinvariants`: the geometric
  coinvariants of a punctually pure lisse sheaf are pure of the same weight.

## TODO

- The quotient map `F_s̄ ↠ geometricCoinvariants F` at a geometric point `s̄`, the dual of
  `AlgebraicGeometry.WeilSheaf.globalSectionsToStalkObj` for `F^∨` composed with
  `(F^∨)_s̄ ≅ (F_s̄)^∨`, together with its compatibility with the Frobenius at closed points.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

/-- The Weil structure of the dual `F^∨ = [F, ℚ̄_ℓ]` of a Weil sheaf `F`, the composite
```
  Fr^* [F, ℚ̄_ℓ] ≅ [Fr^* F, Fr^* ℚ̄_ℓ] ≅ [F, Fr^* ℚ̄_ℓ] ≅ [F, ℚ̄_ℓ]
```
of the comparison `CategoryTheory.Functor.Monoidal.ihomObjIso` for the monoidal equivalence
`Fr^*`, the inverse of the Weil structure `φ : Fr^* F ≅ F` in the first variable and the unit
isomorphism `Fr^* ℚ̄_ℓ ≅ ℚ̄_ℓ` in the second. -/
noncomputable def dualStr (F : WeilSheaf k₀ l X) :
    (frobeniusPullback k₀ l X).obj ((ihom F.obj.carrier).obj (𝟙_ _)) ≅
      (ihom F.obj.carrier).obj (𝟙_ _) :=
  Functor.Monoidal.ihomObjIso (frobeniusPullback k₀ l X) _ _ ≪≫
    ((MonoidalClosed.internalHom.mapIso F.obj.str.op).app _).symm ≪≫
    (ihom F.obj.carrier).mapIso (Functor.Monoidal.εIso _).symm

/-- The underlying sheaf of a lisse Weil sheaf is finite locally constant, being constructible
and locally constant. -/
theorem IsLisse.isFiniteLocallyConstantSheaf {F : WeilSheaf k₀ l X} (hF : F.IsLisse) :
    Scheme.IsFiniteLocallyConstantSheaf F.obj.carrier :=
  Scheme.IsConstructibleSheaf.isFiniteLocallyConstantSheaf F.property hF

-- TODO(unify): sk-d-real-operations
/-- The dual `F^∨ = [F, ℚ̄_ℓ]` of a lisse Weil sheaf: the internal hom into the unit sheaf on
`X̄`, with the Weil structure `AlgebraicGeometry.WeilSheaf.dualStr`. Its underlying sheaf is
finite locally constant (`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.ihom_unit`),
hence constructible. -/
noncomputable def dual (F : WeilSheaf k₀ l X) (hF : F.IsLisse) : WeilSheaf k₀ l X where
  obj := .mk ((ihom F.obj.carrier).obj (𝟙_ _)) F.dualStr
  property := hF.isFiniteLocallyConstantSheaf.ihom_unit.isConstructibleSheaf

/-- The dual of a lisse Weil sheaf is lisse. -/
theorem IsLisse.dual {F : WeilSheaf k₀ l X} (hF : F.IsLisse) : (F.dual hF).IsLisse :=
  hF.isFiniteLocallyConstantSheaf.ihom_unit.toIsLocallyConstantSheaf

/-- The evaluation `F ⊗ F^∨ ⟶ ℚ̄_ℓ` is compatible with the Weil structures:
```
  Fr^* F ⊗ Fr^* [F, ℚ̄_ℓ] ──μ──▶ Fr^* (F ⊗ [F, ℚ̄_ℓ]) ──Fr^* ev──▶ Fr^* ℚ̄_ℓ
          │                                                         │
     φ ⊗ φ^∨│                                                         │
          ▼                                                         ▼
     F ⊗ [F, ℚ̄_ℓ] ──────────────────────ev──────────────────────▶   ℚ̄_ℓ
```
-/
lemma dualStr_ev (F : WeilSheaf k₀ l X) :
    (F.obj.str.hom ⊗ₘ F.dualStr.hom) ≫ (ihom.ev F.obj.carrier).app (𝟙_ _) =
      Functor.LaxMonoidal.μ (frobeniusPullback k₀ l X) _ _ ≫
        (frobeniusPullback k₀ l X).map ((ihom.ev F.obj.carrier).app (𝟙_ _)) ≫
          Functor.OplaxMonoidal.η (frobeniusPullback k₀ l X) :=
  by
  simp only [dualStr, Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.ihomObjIso_hom,
    Functor.Monoidal.commIhom, asIso_hom, Functor.mapIso_hom, Iso.app_inv, Functor.mapIso_inv,
    Iso.op_inv, MonoidalClosed.internalHom_map, Quiver.Hom.unop_op, tensorHom_def',
    MonoidalCategory.whiskerLeft_comp, Category.assoc, Functor.Monoidal.εIso_inv]
  rw [whisker_exchange_assoc, ihom.ev_naturality, whisker_exchange_assoc,
    MonoidalClosed.id_tensor_pre_app_comp_ev_assoc, ← comp_whiskerRight_assoc, Iso.hom_inv_id,
    id_whiskerRight, Category.id_comp, Functor.LaxMonoidal.ihomComparison_ev_assoc]

-- TODO(unify): sk-d-real-operations
/-- The geometric coinvariants of a lisse Weil sheaf `F`: the dual `Γ(X̄, F^∨)^∨` of the global
sections of the dual `F^∨`, with the dual of the Frobenius of
`AlgebraicGeometry.WeilSheaf.globalSections`.

For a lisse `F` on a geometrically connected `X`, with geometric generic fibre `V` a
representation of `π₁(X̄)`, the global sections are
`Γ(X̄, F^∨) = (V^∨)^{π₁(X̄)} = (V_{π₁(X̄)})^∨`, so this is the space of coinvariants
`V_{π₁(X̄)}` with the Frobenius induced from the Weil structure: the maximal geometrically
constant quotient of `F`. If `X̄` is not connected, `Γ(X̄, -)` is a sum over its connected
components.

The universe `max (u + 1) 0 = u + 1` of `FrobeniusModule.dual` agrees with that of the global
sections, since the coefficients `ℚ̄_ℓ` live in universe `0`. -/
noncomputable def geometricCoinvariants [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X)
    (hF : F.IsLisse) : FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  FrobeniusModule.dual (globalSections (F.dual hF))

/-- *Purity of the geometric coinvariants.* If `F` is a lisse Weil sheaf, punctually `ι`-pure of
weight `w`, then its geometric coinvariants `V_{π₁(X̄)}` with the induced Frobenius are `ι`-pure
of weight `w` (possibly zero). The argument compares the coinvariants with the stalk at a closed
point with finite residue field on each geometric component, as an equivariant quotient.

The blueprint states this for `X` a nonempty smooth geometrically connected curve; here `X` is
only assumed locally of finite type over `k₀`, which is what provides these closed points.
Some such hypothesis is needed: `IsPunctuallyPureOfWeight` only sees the points of
`X.finitePoints`, so for `X = Spec 𝔽_q(t)` it holds for every `w`, while the coinvariants of a
rank-one sheaf need not be pure of every weight.
(blueprint: `lem-a1-geometric-coinvariants-pure`) -/
theorem isPureOfWeightOver_geometricCoinvariants
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (ι : PadicAlgCl l →+* ℂ)
    (F : WeilSheaf k₀ l X) (hF : F.IsLisse) {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w) :
    (F.geometricCoinvariants hF).IsPureOfWeightOver k₀ ι w := by
  -- TODO(adic): prove once Weil sheaves carry genuine `ℓ`-adic coefficients
  sorry

end WeilSheaf

end AlgebraicGeometry
