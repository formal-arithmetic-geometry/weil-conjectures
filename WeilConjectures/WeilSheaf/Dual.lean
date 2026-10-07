/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Monoidal
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.Stalk

/-!
# Internal homs, duals and geometric coinvariants of Weil sheaves

The Frobenius pullback `Fr^* = (Fr⁻¹)_*` of pro-étale sheaves on the geometric fiber `X̄` is a
monoidal autoequivalence, so it commutes with internal homs
(`CategoryTheory.Functor.Monoidal.ihomObjIso`). The internal hom `[A, B]` of two pro-étale
Weil sheaves therefore carries the Weil structure

`Fr^* [A, B] ≅ [Fr^* A, Fr^* B] ≅ [A, B]`

by the inverse of the Weil structure of `A` in the first variable and that of `B` in the
second (`AlgebraicGeometry.ProEtaleWeilSheaf.ihom`).

The dual of a lisse Weil sheaf `F` is the internal hom `F^∨ = [F, ℚ̄_ℓ]` into the constant Weil
sheaf `ℚ̄_ℓ` (`AlgebraicGeometry.WeilSheaf.adicConstant`). A ℚ̄_ℓ-linear morphism between lisse
`ℓ`-adic sheaves is automatically linear over the sheaf of rings `ℚ̄_ℓ,X̄` (it commutes with
restriction to the points of a weakly contractible cover), so this is the dual of `F` as a
locally free `ℚ̄_ℓ,X̄`-module of finite rank. The internal hom is the duality functor only for
lisse `F`: the dual of a general constructible `F` is its Verdier dual, a Weil complex.

The geometric coinvariants of `F` are the dual of the global sections of `F^∨`. For a lisse
`F` on a geometrically connected `X`, with geometric generic fibre `V` a representation of
`π₁(X̄)`, `Γ(X̄, F^∨) = (V^∨)^{π₁(X̄)} = (V_{π₁(X̄)})^∨`, whose dual is the space of coinvariants
`V_{π₁(X̄)}` with the Frobenius induced by `φ`.

## Main declarations

- `AlgebraicGeometry.ProEtaleWeilSheaf.ihom`: the internal hom of pro-étale Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.dual`: the dual `F^∨ = [F, ℚ̄_ℓ]` of a lisse Weil sheaf, with
  the Weil structure `AlgebraicGeometry.WeilSheaf.dualStr`.
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

open CategoryTheory MonoidalCategory Endofunctor

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

section Monoidal

variable (k₀ l X) in
/-- The comparison `Fr^* F ⊗ Fr^* G ⟶ Fr^* (F ⊗ G)` of the Frobenius pullback is an isomorphism:
the pushforward along the automorphism `Fr⁻¹` is induced by an automorphism of the pro-étale
site, which commutes with the objectwise tensor product of presheaves and with
sheafification. -/
instance WeilSheaf.isIso_μ_frobeniusPullback
    (F G : Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l)) :
    IsIso (Functor.LaxMonoidal.μ (WeilSheaf.frobeniusPullback k₀ l X) F G) :=
  sorry

variable (k₀ l X) in
/-- The comparison `𝟙 ⟶ Fr^* 𝟙` of the Frobenius pullback is an isomorphism, as for
`AlgebraicGeometry.WeilSheaf.isIso_μ_frobeniusPullback`. -/
instance WeilSheaf.isIso_ε_frobeniusPullback :
    IsIso (Functor.LaxMonoidal.ε (WeilSheaf.frobeniusPullback k₀ l X)) :=
  sorry

/-- The Frobenius pullback `Fr^* = (Fr⁻¹)_*` is a monoidal functor. -/
noncomputable instance : (WeilSheaf.frobeniusPullback k₀ l X).Monoidal :=
  Functor.Monoidal.ofLaxMonoidal _

/-- The internal hom of two lisse sheaves is lisse: locally it is the internal hom of finite
sums of copies of `ℚ̄_ℓ`, and `[ℚ̄_ℓ, ℚ̄_ℓ] = ℚ̄_ℓ`, a `ℚ̄_ℓ`-linear endomorphism of `ℚ̄_ℓ,X̄`
being multiplication by a section. -/
theorem ProEtale.IsAdicLisseSheaf.ihom {Z : Scheme.{u}}
    {F G : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)} (hF : IsAdicLisseSheaf F)
    (hG : IsAdicLisseSheaf G) : IsAdicLisseSheaf ((ihom F).obj G) :=
  sorry

/-- The internal hom from a lisse sheaf into a constructible sheaf is constructible: on the
strata of the second sheaf it is the internal hom of two lisse sheaves. -/
theorem ProEtale.IsAdicConstructibleSheaf.ihom_of_isAdicLisseSheaf {Z : Scheme.{u}}
    {F G : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)} (hF : IsAdicLisseSheaf F)
    (hG : IsAdicConstructibleSheaf G) : IsAdicConstructibleSheaf ((ihom F).obj G) :=
  sorry

variable (k₀ l X) in
/-- The internal hom `[A, B]` of two pro-étale Weil sheaves, with the Weil structure
```
  Fr^* [A, B] ≅ [Fr^* A, Fr^* B] ≅ [A, Fr^* B] ≅ [A, B]
```
given by the comparison `CategoryTheory.Functor.Monoidal.ihomObjIso` for the monoidal
equivalence `Fr^*`, the inverse of the Weil structure of `A` in the first variable and the Weil
structure of `B` in the second. -/
noncomputable def ProEtaleWeilSheaf.ihom (A B : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf k₀ l X :=
  IsoAlgebra.mk ((CategoryTheory.ihom A.carrier).obj B.carrier)
    (Functor.Monoidal.ihomObjIso (WeilSheaf.frobeniusPullback k₀ l X) _ _ ≪≫
      ((MonoidalClosed.internalHom.mapIso A.str.op).app _).symm ≪≫
      (CategoryTheory.ihom A.carrier).mapIso B.str)

end Monoidal

namespace WeilSheaf

/-- The Weil structure of the dual `F^∨ = [F, ℚ̄_ℓ]` of a Weil sheaf `F`, the composite
```
  Fr^* [F, ℚ̄_ℓ] ≅ [Fr^* F, Fr^* ℚ̄_ℓ] ≅ [F, Fr^* ℚ̄_ℓ] ≅ [F, ℚ̄_ℓ]
```
of the comparison `CategoryTheory.Functor.Monoidal.ihomObjIso` for the monoidal equivalence
`Fr^*`, the inverse of the Weil structure `φ : Fr^* F ≅ F` in the first variable and the Weil
structure of the constant Weil sheaf `ℚ̄_ℓ` in the second. -/
noncomputable def dualStr (F : WeilSheaf k₀ l X) :
    (frobeniusPullback k₀ l X).obj
        ((ihom F.obj.carrier).obj (ProEtaleWeilSheaf.adicConstant k₀ l X).carrier) ≅
      (ihom F.obj.carrier).obj (ProEtaleWeilSheaf.adicConstant k₀ l X).carrier :=
  (ProEtaleWeilSheaf.ihom k₀ l X F.obj (ProEtaleWeilSheaf.adicConstant k₀ l X)).str

-- TODO(unify): sk-d-real-operations
/-- The dual `F^∨ = [F, ℚ̄_ℓ]` of a lisse Weil sheaf: the internal hom into the constant Weil
sheaf `ℚ̄_ℓ`, with the Weil structure `AlgebraicGeometry.WeilSheaf.dualStr`. It is lisse
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.ihom`), hence constructible. -/
noncomputable def dual (F : WeilSheaf k₀ l X) (hF : F.IsLisse) : WeilSheaf k₀ l X where
  obj := ProEtaleWeilSheaf.ihom k₀ l X F.obj (ProEtaleWeilSheaf.adicConstant k₀ l X)
  property := (hF.ihom (ProEtale.isAdicLisseSheaf_adicConstantSheaf _)).isAdicConstructibleSheaf

/-- The dual of a lisse Weil sheaf is lisse. -/
theorem IsLisse.dual {F : WeilSheaf k₀ l X} (hF : F.IsLisse) : (F.dual hF).IsLisse :=
  ProEtale.IsAdicLisseSheaf.ihom hF (ProEtale.isAdicLisseSheaf_adicConstantSheaf _)

/-- The evaluation `F ⊗ F^∨ ⟶ ℚ̄_ℓ` is compatible with the Weil structures:
```
  Fr^* F ⊗ Fr^* [F, ℚ̄_ℓ] ──μ──▶ Fr^* (F ⊗ [F, ℚ̄_ℓ]) ──Fr^* ev──▶ Fr^* ℚ̄_ℓ
          │                                                         │
     φ ⊗ φ^∨│                                                         │φ_ℚ̄_ℓ
          ▼                                                         ▼
     F ⊗ [F, ℚ̄_ℓ] ──────────────────────ev──────────────────────▶   ℚ̄_ℓ
```
-/
lemma dualStr_ev (F : WeilSheaf k₀ l X) :
    (F.obj.str.hom ⊗ₘ F.dualStr.hom) ≫
        (ihom.ev F.obj.carrier).app (ProEtaleWeilSheaf.adicConstant k₀ l X).carrier =
      Functor.LaxMonoidal.μ (frobeniusPullback k₀ l X) _ _ ≫
        (frobeniusPullback k₀ l X).map
          ((ihom.ev F.obj.carrier).app (ProEtaleWeilSheaf.adicConstant k₀ l X).carrier) ≫
          (ProEtaleWeilSheaf.adicConstant k₀ l X).str.hom := by
  simp only [dualStr, ProEtaleWeilSheaf.ihom, IsoAlgebra.mk_str, Iso.trans_hom, Iso.symm_hom,
    Functor.Monoidal.ihomObjIso_hom, Functor.Monoidal.commIhom, asIso_hom, Functor.mapIso_hom,
    Iso.app_inv, Functor.mapIso_inv, Iso.op_inv, MonoidalClosed.internalHom_map,
    Quiver.Hom.unop_op, tensorHom_def', MonoidalCategory.whiskerLeft_comp, Category.assoc]
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

-- TODO(adic): for `F` lisse, hence locally free of finite rank, the stalk of the internal hom
-- `[F, ℚ̄_ℓ]` is the dual of the stalk of `F`, with the inverse transpose Frobenius.
/-- The stalk of the dual of a lisse Weil sheaf is the dual of its stalk: the local Frobenius
of `F^∨` at `x` is the inverse transpose of that of `F`. -/
theorem nonempty_equiv_stalk_dual {F : WeilSheaf k₀ l X} (hF : F.IsLisse)
    (x : X.finitePoints) : Nonempty (((F.dual hF).stalk x).Equiv (F.stalk x).dual) := by
  sorry

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
