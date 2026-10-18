/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.AdicSystem

/-!
# Compatible systems of Frobenius coefficient morphisms and their realizations

Let `g` be an automorphism of a scheme `X` lying over an automorphism `h` of the base
`s = Spec k` (`g ≫ a_X = a_X ≫ h` cartesian); in the `ℓ`-adic formalism `X = X₀ ×_{k₀} k` and
`g = g_γ` is the geometric Frobenius. A *Weil datum* on `K` is a morphism `φ : Lg^* K ⟶ K`; it
has a *global Frobenius operator* `F_c(φ) = RΓ_c(X, φ) ∘ g_c^*` on compact cohomology
(`AlgebraicGeometry.Etale.globalOperator`) and, at a point `x̄` fixed by `(g, h)`, a *local
Frobenius operator* `F_x̄(φ) = φ_x̄ ∘ τ_x̄` on the geometric stalk
(`AlgebraicGeometry.Etale.localOperator`), blueprint `def-trf-frobenius-operators`.

A *compatible system of Frobenius coefficient morphisms* on a normalized adic system `L_•`
(`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem`, blueprint
`prop-trf-adic-coefficient-morphism-systems`) is a family `ψ_n : Lg^* L_n ⟶ L_n` reducing to each
other along the transitions of `L_•`; a compatible tower of Weil pairs is the case where every
`ψ_n` is invertible (`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.IsWeil`). For such a
system and every `m ≥ 1`, the global operators `F_c(ψ_n^{[m]})` and the local operators
`F_x̄(ψ_n^{[m]})` at points fixed by `(g^m, h^m)` form compatible families of endomorphisms of the
normalized towers of perfect complexes `RΓ_c(X, L_n)` and `(L_n)_x̄`
(`prop-trf-adic-coefficient-morphism-systems` (3)); hence they lift to the realizations over
`R`, the realization isomorphisms are equivariant for the lifts, and the traces of the lifts are
the limits of the levelwise traces (`prop-trf-adic-coefficient-morphism-systems` (4),
`sk-prop-trace-adic` (ii)).

## Main definitions

- `AlgebraicGeometry.Etale.globalOperator`, `AlgebraicGeometry.Etale.localOperator`: the
  Frobenius operators of a Weil datum.
- `AlgebraicGeometry.Etale.endIterate`, `AlgebraicGeometry.Etale.iterateWeilDatum`: the iterates
  `g^m` and `φ^{[m]} : L(g^m)^* K ⟶ K`.
- `AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem`: a compatible system of Frobenius
  coefficient morphisms, with its iterates
  `AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.iterate`.

## Main results

- `AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.isCompatible_globalOperatorFamily`,
  `AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.isCompatible_localOperatorFamily`:
  blueprint `prop-trf-adic-coefficient-morphism-systems` (3).
- `AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.exists_isLift_globalOperatorFamily`,
  `AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.exists_trace_eq_globalOperatorFamily` and
  their local versions: blueprint `prop-trf-adic-coefficient-morphism-systems` (2), (4) and
  `sk-prop-trace-adic` (ii), equivariance.

## Implementation notes

The blueprint writes Frobenius coefficient morphisms `ψ : LΦ^* K ⟶ K` with respect to the
`q`-power scheme Frobenius `Φ`, and their global operators as the action of the graph
correspondence of `(𝟙, Φ^m)`. By blueprint `prop-trf-graph-frobenius-operator` (general clause),
that action is `RΓ_c(X, v) ∘ g_{γ,c}^{m,*}` for the morphism `v = ψ_m ∘ (κ^{(m)})⁻¹` attached to
the geometric Frobenius `g_γ` through the comparison `κ^{(m)} : LΦ^{m*} ≅ Lg_γ^{m*}` of
`prop-trf-scheme-galois-comparison`. Here the data are taken directly relative to `g = g_γ`
(as for the strict Weil complexes `AlgebraicGeometry.Etale.WeilComplex` of
`sk-def-sf-weil-complexes`), and the operators are defined by that formula, with the
compact-support base change `g_c^*` of `AlgebraicGeometry.Etale.compactPullback`.

The compatibility of the operators with the coefficient change comes from the compatibility of
the coefficient comparisons with pullback (`AlgebraicGeometry.Etale.IsCompactPullbackCompatible`,
`AlgebraicGeometry.Etale.IsStalkPullbackCompatible`), which the coefficient comparisons of
`AlgebraicGeometry.Etale.AdicSystem.exists_compactSupportTower` and
`AlgebraicGeometry.Etale.AdicSystem.exists_stalkTower` satisfy.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section Operators

variable (Λ : Type (u + 1)) [CommRing Λ] {X s : Scheme.{u}} {g : X ⟶ X} {h : s ⟶ s}

/-- Blueprint `def-trf-frobenius-operators` (1): the *global Frobenius operator*
`F_c(φ) = RΓ_c(X, φ) ∘ g_c^*` on `RΓ_c(X, K)` of a Weil datum `φ : Lg^* K ⟶ K`, for an
automorphism `g` of `X` over an automorphism `h` of the base, `g_c^*` being the compact-support
base change `AlgebraicGeometry.Etale.compactPullback`. The datum `φ` need not be invertible. -/
noncomputable def globalOperator [Finite Λ] {a : X ⟶ s} [QuasiCompact a]
    [HasCompactification a] (sq : IsPullback g a a h) [IsIso h]
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K ⟶
      (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K :=
  (compactPullback Λ sq).app K ≫ (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).map φ

/-- Blueprint `def-trf-frobenius-operators` (2): the *local Frobenius operator*
`F_x̄(φ) = φ_x̄ ∘ τ_x̄` on the geometric stalk `K_x̄` of a Weil datum `φ : Lg^* K ⟶ K`, at a point
`x̄` fixed by the pair `(g, h)`, `τ_x̄` being the stalk transport
`AlgebraicGeometry.Etale.stalkPullback`. -/
noncomputable def localOperator {x : s ⟶ X} (hx : h ≫ x = x ≫ g) [IsIso h]
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    (geometricStalk Λ x).obj K ⟶ (geometricStalk Λ x).obj K :=
  (stalkPullback Λ hx).app K ≫ (geometricStalk Λ x).map φ

end Operators

/-- The inductive step of the compatibility of iterated Weil data with a change of coefficients,
stated for abstract functors so that the kernel does not unfold the derived pullbacks: if
`ψ₁ : G₁ L₁ ⟶ L₁` and `v₁ : M₁ L₁ ⟶ L₁` reduce along `t : L₁ ⟶ Res L₀` to `ψ₀` and `v₀`, then
so does `ψ₁ ∘ G₁ v₁ ∘ comp₁ : P₁ L₁ ⟶ L₁`, provided the comparisons `ι` are compatible with the
composition isomorphisms `comp : P ≅ M ⋙ G`. -/
lemma comp_comm_of_comm_aux {C₀ C₁ : Type*} [Category C₀] [Category C₁] (Res : C₀ ⥤ C₁)
    {G₀ M₀ P₀ : C₀ ⥤ C₀} {G₁ M₁ P₁ : C₁ ⥤ C₁} (comp₀ : P₀ ≅ M₀ ⋙ G₀) (comp₁ : P₁ ≅ M₁ ⋙ G₁)
    (ιg : Res ⋙ G₁ ≅ G₀ ⋙ Res) (ιm : Res ⋙ M₁ ≅ M₀ ⋙ Res) (ιp : Res ⋙ P₁ ≅ P₀ ⋙ Res)
    (hc : ∀ K, ιp.hom.app K ≫ Res.map (comp₀.hom.app K) =
      comp₁.hom.app (Res.obj K) ≫ G₁.map (ιm.hom.app K) ≫ ιg.hom.app (M₀.obj K))
    {L₀ : C₀} {L₁ : C₁} (t : L₁ ⟶ Res.obj L₀) {ψ₀ : G₀.obj L₀ ⟶ L₀} {ψ₁ : G₁.obj L₁ ⟶ L₁}
    (hψ : ψ₁ ≫ t = G₁.map t ≫ ιg.hom.app L₀ ≫ Res.map ψ₀) {v₀ : M₀.obj L₀ ⟶ L₀}
    {v₁ : M₁.obj L₁ ⟶ L₁} (hv : v₁ ≫ t = M₁.map t ≫ ιm.hom.app L₀ ≫ Res.map v₀) :
    (comp₁.hom.app L₁ ≫ G₁.map v₁ ≫ ψ₁) ≫ t =
      P₁.map t ≫ ιp.hom.app L₀ ≫ Res.map (comp₀.hom.app L₀ ≫ G₀.map v₀ ≫ ψ₀) := by
  have hnat := comp₁.hom.naturality t
  have hιg := ιg.hom.naturality v₀
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat hιg
  rw [Functor.map_comp, Functor.map_comp, reassoc_of% hc, reassoc_of% hnat, ← reassoc_of% hιg,
    ← G₁.map_comp_assoc, ← G₁.map_comp_assoc]
  rw [Category.assoc (M₁.map t), ← hv, G₁.map_comp_assoc, ← hψ]
  simp only [Category.assoc]

/-- The base case of the compatibility of iterated Weil data with a change of coefficients,
stated for abstract functors: the identity isomorphisms `id : P ≅ 𝟭` reduce to each other
provided the comparison `ι` is compatible with them. -/
lemma id_comm_of_comm_aux {C₀ C₁ : Type*} [Category C₀] [Category C₁] (Res : C₀ ⥤ C₁)
    {P₀ : C₀ ⥤ C₀} {P₁ : C₁ ⥤ C₁} (id₀ : P₀ ≅ 𝟭 C₀) (id₁ : P₁ ≅ 𝟭 C₁)
    (ιp : Res ⋙ P₁ ≅ P₀ ⋙ Res)
    (hc : ∀ K, ιp.hom.app K ≫ Res.map (id₀.hom.app K) = id₁.hom.app (Res.obj K))
    {L₀ : C₀} {L₁ : C₁} (t : L₁ ⟶ Res.obj L₀) :
    id₁.hom.app L₁ ≫ t = P₁.map t ≫ ιp.hom.app L₀ ≫ Res.map (id₀.hom.app L₀) := by
  rw [hc]
  exact (id₁.hom.naturality t).symm

/-- The compatibility of Frobenius operators with a change of coefficients, stated for abstract
functors so that the kernel does not unfold the six functors: for functors `Φ₀`, `Φ₁` (compact
cohomology or a geometric stalk at two coefficient levels) with a coefficient comparison
`α : Res ⋙ Φ₁ ≅ Φ₀ ⋙ Res'`, transports `cp : Φ ⟶ G ⋙ Φ` compatible with `α`, and Weil data
`ψ₁`, `ψ₀` reducing to each other along `t : L₁ ⟶ Res L₀`, the operators `Φ ψ ∘ cp` are
compatible with the transition `Φ₁ t ≫ α`. -/
lemma operator_comm_of_comm_aux {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁] [Category D₀]
    [Category D₁] (Res : C₀ ⥤ C₁) (Res' : D₀ ⥤ D₁) {Φ₀ : C₀ ⥤ D₀} {Φ₁ : C₁ ⥤ D₁}
    {G₀ : C₀ ⥤ C₀} {G₁ : C₁ ⥤ C₁} (α : Res ⋙ Φ₁ ≅ Φ₀ ⋙ Res') (ι : Res ⋙ G₁ ≅ G₀ ⋙ Res)
    (cp₀ : Φ₀ ⟶ G₀ ⋙ Φ₀) (cp₁ : Φ₁ ⟶ G₁ ⋙ Φ₁)
    (hcl : ∀ K, α.hom.app K ≫ Res'.map (cp₀.app K) =
      cp₁.app (Res.obj K) ≫ Φ₁.map (ι.hom.app K) ≫ α.hom.app (G₀.obj K))
    {L₀ : C₀} {L₁ : C₁} (t : L₁ ⟶ Res.obj L₀) {ψ₀ : G₀.obj L₀ ⟶ L₀} {ψ₁ : G₁.obj L₁ ⟶ L₁}
    (hψ : ψ₁ ≫ t = G₁.map t ≫ ι.hom.app L₀ ≫ Res.map ψ₀) :
    (Φ₁.map t ≫ α.hom.app L₀) ≫ Res'.map (cp₀.app L₀ ≫ Φ₀.map ψ₀) =
      (cp₁.app L₁ ≫ Φ₁.map ψ₁) ≫ Φ₁.map t ≫ α.hom.app L₀ := by
  have hcp := cp₁.naturality t
  have hα := α.hom.naturality ψ₀
  dsimp only [Functor.comp_obj, Functor.comp_map] at hcp hα
  rw [Functor.map_comp, Category.assoc, reassoc_of% hcl, Category.assoc, ← Functor.map_comp_assoc,
    hψ, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, ← hα,
    reassoc_of% hcp]

section Iterate

/-- The `m`-th iterate `g^m = g ≫ ⋯ ≫ g` of an endomorphism `g`, defined so that
`g^{m+1} = g ≫ g^m` holds by definition. It agrees with the power of `g` in `End X`
(`AlgebraicGeometry.Etale.endIterate_eq_pow`). -/
def endIterate {X : Scheme.{u}} (g : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | m + 1 => g ≫ endIterate g m

@[simp]
lemma endIterate_zero {X : Scheme.{u}} (g : X ⟶ X) : endIterate g 0 = 𝟙 X :=
  rfl

lemma endIterate_succ {X : Scheme.{u}} (g : X ⟶ X) (m : ℕ) :
    endIterate g (m + 1) = g ≫ endIterate g m :=
  rfl

lemma endIterate_eq_pow {X : Scheme.{u}} (g : X ⟶ X) (m : ℕ) :
    endIterate g m = End.asHom (End.of g ^ m) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [endIterate_succ, ih, pow_succ]; rfl

instance isIso_endIterate {X : Scheme.{u}} (g : X ⟶ X) [IsIso g] (m : ℕ) :
    IsIso (endIterate g m) := by
  induction m with
  | zero => exact inferInstanceAs (IsIso (𝟙 X))
  | succ m ih => exact inferInstanceAs (IsIso (g ≫ endIterate g m))

/-- The iterates of a cartesian square `g ≫ a = a ≫ h` are cartesian. -/
lemma isPullback_endIterate {X s : Scheme.{u}} {g : X ⟶ X} {h : s ⟶ s} {a : X ⟶ s}
    (sq : IsPullback g a a h) [IsIso g] [IsIso h] (m : ℕ) :
    IsPullback (endIterate g m) a a (endIterate h m) := by
  induction m with
  | zero => exact IsPullback.of_horiz_isIso ⟨by simp⟩
  | succ m ih => exact sq.paste_horiz ih

/-- A point fixed by a pair `(g, h)` is fixed by its iterates. -/
lemma endIterate_comp_of_comp {X s : Scheme.{u}} {g : X ⟶ X} {h : s ⟶ s} {x : s ⟶ X}
    (hx : h ≫ x = x ≫ g) (m : ℕ) : endIterate h m ≫ x = x ≫ endIterate g m := by
  induction m with
  | zero => simp
  | succ m ih => rw [endIterate_succ, endIterate_succ, Category.assoc, ih, ← Category.assoc, hx,
      Category.assoc]

variable (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}} (g : X ⟶ X)

/-- Blueprint `def-trf-frobenius-coefficient-morphism` (2), `def-trf-iterated-weil-map`: the
*iterates* `φ^{[m]} : L(g^m)^* K ⟶ K` of a Weil datum `φ : Lg^* K ⟶ K`, defined by
`φ^{[0]} = (L(𝟙)^* K ≅ K)` and
`φ^{[m+1]} : L(g ≫ g^m)^* K ≅ Lg^* L(g^m)^* K ──Lg^* φ^{[m]}──▶ Lg^* K ──φ──▶ K`. -/
noncomputable def iterateWeilDatum
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    ∀ m : ℕ, (L((endIterate g m)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K
  | 0 => (leftDerivedUpperStarId _ X).hom.app K
  | m + 1 => (leftDerivedUpperStarComp _ g (endIterate g m)).hom.app K ≫
      (L((g)^*[ModuleCat.{u + 1} Λ])).map (iterateWeilDatum φ m) ≫ φ

end Iterate

namespace AdicSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {X : Scheme.{u}} (S : AdicSystem I X)

/-- Blueprint `prop-trf-adic-coefficient-morphism-systems`: a *compatible system of Frobenius
coefficient morphisms* on a normalized adic system `L_•`, relative to an endomorphism `g` of `X`:
morphisms `ψ_n : Lg^* L_n ⟶ L_n` at every level such that `ψ_{n+1}` followed by the transition
`ν_n : L_{n+1} ⟶ Res L_n` is `Lg^* ν_n` followed by the identification
`Lg^* Res L_n ≅ Res Lg^* L_n` (`AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso`)
and `Res ψ_n`; in terms of derived base change, `ψ_{n+1} ⊗ᴸ A_n` corresponds to `ψ_n` under
`ν_n`. No invertibility is assumed. -/
structure FrobeniusSystem (g : X ⟶ X) where
  /-- The Frobenius coefficient morphism `ψ_n : Lg^* L_n ⟶ L_n`. -/
  coeff (n : ℕ) : (L((g)^*[ModuleCat.{u + 1} (R ⧸ I ^ n)])).obj (S.obj n) ⟶ S.obj n
  /-- `ψ_{n+1}` reduces to `ψ_n`. -/
  comm (n : ℕ) : coeff (n + 1) ≫ S.map n =
    (L((g)^*[ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))])).map (S.map n) ≫
      (leftDerivedUpperStarRestrictScalarsIso
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) n.le_succ)) g).hom.app
          (S.obj n) ≫
      (_root_.DerivedCategory.levelTransitionRestrictScalars _ I n.le_succ).map (coeff n)

namespace FrobeniusSystem

variable {S} {g : X ⟶ X} (F : S.FrobeniusSystem g)

/-- Blueprint `def-trf-adic-system`, `sk-prop-trace-adic` (ii): a compatible system of Frobenius
coefficient morphisms is a *compatible tower of Weil pairs* if every `ψ_n` is invertible: a
strict Weil structure `Lg^* L_n ≅ L_n` at every level (`sk-def-sf-weil-complexes`), compatible
with the transitions. -/
def IsWeil : Prop :=
  ∀ n, IsIso (F.coeff n)

/-- The iterated system `ψ_n^{[m]} : L(g^m)^* L_n ⟶ L_n` of a compatible system of Frobenius
coefficient morphisms is again compatible: the composition isomorphisms of the derived pullback
are compatible with restriction of scalars
(`AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso_comp_hom_app`). -/
noncomputable def iterate (m : ℕ) : S.FrobeniusSystem (endIterate g m) where
  coeff n := iterateWeilDatum _ g (F.coeff n) m
  comm n := by
    induction m with
    | zero =>
      exact id_comm_of_comm_aux _ (leftDerivedUpperStarId _ X) (leftDerivedUpperStarId _ X)
        (leftDerivedUpperStarRestrictScalarsIso _ (𝟙 X))
        (leftDerivedUpperStarRestrictScalarsIso_id_hom_app _ X) (S.map n)
    | succ m ih =>
      exact comp_comm_of_comm_aux _ (leftDerivedUpperStarComp _ g (endIterate g m))
        (leftDerivedUpperStarComp _ g (endIterate g m))
        (leftDerivedUpperStarRestrictScalarsIso _ g)
        (leftDerivedUpperStarRestrictScalarsIso _ (endIterate g m))
        (leftDerivedUpperStarRestrictScalarsIso _ (g ≫ endIterate g m))
        (leftDerivedUpperStarRestrictScalarsIso_comp_hom_app _ g (endIterate g m)) (S.map n)
        (F.comm n) ih

section Geometric

variable {k : Type u} [Field k] [IsSepClosed k] {aX : X ⟶ Spec (.of k)} [LocallyOfFiniteType aX]
  [QuasiCompact aX] [HasCompactification aX] [∀ n, Finite (R ⧸ I ^ n)]
  [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))] {h : Spec (.of k) ⟶ Spec (.of k)}
  [IsIso h]

/-- The global Frobenius operators `F_c(ψ_{n+1})` on the levels `RΓ_c(X, L_{n+1})` of the tower
`AlgebraicGeometry.Etale.AdicSystem.compactSupportTower`. -/
noncomputable def globalOperatorFamily (sq : IsPullback g aX aX h)
    (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
        ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hα : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (α n)) (n : ℕ) :
    (S.compactSupportTower aX α hα).obj n ⟶ (S.compactSupportTower aX α hα).obj n :=
  globalOperator _ sq (F.coeff (n + 1))

/-- The local Frobenius operators `F_x̄(ψ_{n+1})` on the levels `(L_{n+1})_x̄` of the tower
`AlgebraicGeometry.Etale.AdicSystem.stalkTower`, at a point `x̄` fixed by `(g, h)`. -/
noncomputable def localOperatorFamily {x : Spec (.of k) ⟶ X} (hx : h ≫ x = x ≫ g)
    (β : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        geometricStalk (R ⧸ I ^ (n + 1 + 1)) x ≅
      geometricStalk (R ⧸ I ^ (n + 1)) x ⋙ ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hβ : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (β n)) (n : ℕ) :
    (S.stalkTower x β hβ).obj n ⟶ (S.stalkTower x β hβ).obj n :=
  localOperator _ hx (F.coeff (n + 1))

/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (3), global operators: the global
Frobenius operators `F_c(ψ_n)` of a compatible system of Frobenius coefficient morphisms form a
compatible family of endomorphisms of the tower `RΓ_c(X, L_n)`, for coefficient identifications
compatible with the compact-support base change
(`AlgebraicGeometry.Etale.AdicSystem.exists_compactSupportTower`). Applied to the iterated
systems `AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.iterate`, this gives the statement for
every `m`. -/
theorem isCompatible_globalOperatorFamily (sq : IsPullback g aX aX h)
    (α : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1 + 1))) aX ≅
      compactlySupportedGlobalSections (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))) aX ⋙
        ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hα : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (α n))
    (hα' : ∀ n : ℕ, IsCompactPullbackCompatible (I.powSuccFactor n) (α n) sq) :
    (S.compactSupportTower aX α hα).IsCompatible (F.globalOperatorFamily sq α hα) := fun n ↦
  operator_comm_of_comm_aux _ _ (α n) _ (compactPullback _ sq) (compactPullback _ sq) (hα' n)
    (S.map (n + 1)) (F.comm (n + 1))

/-- Blueprint `prop-trf-adic-coefficient-morphism-systems` (3), local operators: at a point `x̄`
fixed by `(g, h)`, the local Frobenius operators `F_x̄(ψ_n)` of a compatible system of Frobenius
coefficient morphisms form a compatible family of endomorphisms of the tower `(L_n)_x̄`, for
coefficient identifications compatible with the stalk transport
(`AlgebraicGeometry.Etale.AdicSystem.exists_stalkTower`). -/
theorem isCompatible_localOperatorFamily {x : Spec (.of k) ⟶ X} (hx : h ≫ x = x ≫ g)
    (β : ∀ n : ℕ, Sheaf.derivedRestrictScalars X.smallEtaleTopology (I.powSuccFactor n) ⋙
        geometricStalk (R ⧸ I ^ (n + 1 + 1)) x ≅
      geometricStalk (R ⧸ I ^ (n + 1)) x ⋙ ModuleCat.derivedRestrictScalars (I.powSuccFactor n))
    (hβ : ∀ n : ℕ, IsCoefficientChange (I.powSuccFactor n) _ _ (β n))
    (hβ' : ∀ n : ℕ, IsStalkPullbackCompatible (I.powSuccFactor n) (β n) hx) :
    (S.stalkTower x β hβ).IsCompatible (F.localOperatorFamily hx β hβ) := fun n ↦
  operator_comm_of_comm_aux _ _ (β n) _ (stalkPullback _ hx) (stalkPullback _ hx) (hβ' n)
    (S.map (n + 1)) (F.comm (n + 1))

end Geometric

end FrobeniusSystem

end AdicSystem

end AlgebraicGeometry.Etale
